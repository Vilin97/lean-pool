/-
Copyright (c) 2026 Stefan Barańczuk, Aristotle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Barańczuk, Aristotle
-/

import Mathlib.LinearAlgebra.Projectivization.Cardinality
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.Data.Set.Card
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic.Common
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Polyrith
/-!
# FinEqs main file

Vendored from `nasqret/fineqs`. See `LeanPool/Fineqs.lean` for the project overview.
-/

namespace LeanPool.Fineqs

open scoped BigOperators

/-- The zero set of a set of functions `X → F`. -/
def ZeroSet {X F : Type*} [Zero F] (S : Set (X → F)) : Set X :=
  {x | ∀ f ∈ S, f x = 0}

/-- For a submodule `L` of a finite-dimensional `F`-vector space `V` of dimension
`finrank F L + n`, there is a linear map from `V` to `Fin n → F` with kernel exactly `L`. -/
private lemma exists_linearMap_of_ker {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
    [Module.Finite F V] (n : ℕ) (L : Submodule F V)
    (hV : Module.finrank F V = Module.finrank F L + n) :
    ∃ M : V →ₗ[F] (Fin n → F), LinearMap.ker M = L := by
  have hquot : Module.finrank F (V ⧸ L) = n := by
    have h := Submodule.finrank_quotient_add_finrank L
    omega
  classical
  have hrank : Module.finrank F (V ⧸ L) = Module.finrank F (Fin n → F) := by
    rw [hquot, Module.finrank_fin_fun]
  let e : (V ⧸ L) ≃ₗ[F] (Fin n → F) := LinearEquiv.ofFinrankEq _ _ hrank
  refine ⟨e.toLinearMap.comp L.mkQ, ?_⟩
  rw [LinearMap.ker_comp]
  have he : LinearMap.ker e.toLinearMap = ⊥ := e.ker
  rw [he, Submodule.comap_bot, Submodule.ker_mkQ]

variable {F : Type*} [Field F] [Fintype F]

/--
Cardinality of projective space minus a point: `|P^n(F) \ {α}| = (q^{n+1} - q) / (q - 1)`.
-/
lemma card_projectivization_minus_point (n : ℕ) (α : Projectivization F (Fin (n + 1) → F)) :
    Nat.card {x : Projectivization F (Fin (n + 1) → F) // x ≠ α} =
    (Fintype.card F ^ (n + 1) - Fintype.card F) / (Fintype.card F - 1) := by
  classical
  haveI : Fintype (Projectivization F (Fin (n + 1) → F)) := Fintype.ofFinite _
  haveI : Nonempty (Projectivization F (Fin (n + 1) → F)) := ⟨α⟩
  haveI : Fintype {x : Projectivization F (Fin (n + 1) → F) // x ≠ α} := Subtype.fintype _
  haveI : Fintype {x : Projectivization F (Fin (n + 1) → F) // x = α} := Subtype.fintype _
  rw [Nat.card_eq_fintype_card,
    Fintype.card_subtype_compl (p := (· = α)),
    Fintype.card_subtype_eq α]
  have hcardV := Projectivization.card' F (Fin (n + 1) → F)
  simp only [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin] at hcardV
  have hq : 2 ≤ Fintype.card F := Fintype.one_lt_card
  have hP : 1 ≤ Fintype.card (Projectivization F (Fin (n + 1) → F)) :=
    Fintype.card_pos
  set q := Fintype.card F
  set P := Fintype.card (Projectivization F (Fin (n + 1) → F))
  have hqsub : 0 < q - 1 := by omega
  -- Show: q^(n+1) - q = (q - 1) * (P - 1).
  have hPq : P * (q - 1) = q ^ (n + 1) - 1 := by omega
  have h_eq : q ^ (n + 1) - q = (P - 1) * (q - 1) := by
    rw [Nat.sub_mul, one_mul]; omega
  have hdvd : (q - 1) ∣ (q ^ (n + 1) - q) := ⟨P - 1, by rw [mul_comm]; exact h_eq⟩
  rw [eq_comm, Nat.div_eq_iff_eq_mul_left hqsub hdvd]
  exact h_eq

/-- The cardinality of `P^n(F)` in the form used by the sharpness example. -/
lemma card_projectivization_eq_bound_add_one (n : ℕ) :
    Nat.card (Projectivization F (Fin (n + 1) → F)) =
    (Fintype.card F ^ (n + 1) - Fintype.card F) / (Fintype.card F - 1) + 1 := by
  classical
  let e : Fin (n + 1) → F := Pi.single 0 1
  have he : e ≠ 0 := by
    intro h
    have := congr_fun h 0
    simp [e] at this
  let α : Projectivization F (Fin (n + 1) → F) := Projectivization.mk F e he
  have hcard := card_projectivization_minus_point (F := F) n α
  haveI : Fintype (Projectivization F (Fin (n + 1) → F)) := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card] at hcard ⊢
  have hcompl :
      Fintype.card {x : Projectivization F (Fin (n + 1) → F) // x ≠ α} =
        Fintype.card (Projectivization F (Fin (n + 1) → F)) - 1 := by
    rw [Fintype.card_subtype_compl (p := (· = α)), Fintype.card_subtype_eq α]
  rw [hcompl] at hcard
  have hpos : 0 < Fintype.card (Projectivization F (Fin (n + 1) → F)) :=
    Fintype.card_pos
  omega

/-- The affine-space cardinality bound needed for Theorem 1. -/
private lemma card_affine_le_projective_bound (n : ℕ) (hn : 0 < n) :
    Nat.card (Fin n → F) ≤
      (Fintype.card F ^ (n + 1) - Fintype.card F) / (Fintype.card F - 1) := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin]
  set q := Fintype.card F
  have hq : 2 ≤ q := Fintype.one_lt_card
  have hden : 0 < q - 1 := by omega
  rw [Nat.le_div_iff_mul_le hden]
  have hq_le_pow : q ≤ q ^ n := Nat.le_self_pow hn.ne' q
  have hmul : q ^ n * (q - 1) = q ^ (n + 1) - q ^ n := by
    rw [Nat.mul_sub_left_distrib, mul_one, pow_succ', mul_comm]
  rw [hmul]
  exact Nat.sub_le_sub_left hq_le_pow _

/--
Auxiliary form of Theorem 1: a map into `F^(n+1)` over a small finite set admits
a linear projection to `F^n` whose kernel misses all nonzero image points.
-/
lemma theorem_1_aux {X : Type*} [Finite X] (n : ℕ) (f : X → (Fin (n + 1) → F))
    (hX : Nat.card X ≤
      (Fintype.card F ^ (n + 1) - Fintype.card F) / (Fintype.card F - 1)) :
    ∃ M : (Fin (n + 1) → F) →ₗ[F] (Fin n → F),
      {x | M (f x) = 0} = {x | f x = 0} := by
  classical
  haveI : Fintype X := Fintype.ofFinite X
  let P := Projectivization F (Fin (n + 1) → F)
  let e : Fin (n + 1) → F := Pi.single 0 1
  have he : e ≠ 0 := by
    intro h
    have := congr_fun h 0
    simp [e] at this
  let α : P := Projectivization.mk F e he
  haveI : Fintype P := Fintype.ofFinite P
  have hbound_lt : (Fintype.card F ^ (n + 1) - Fintype.card F) /
      (Fintype.card F - 1) < Nat.card P := by
    have hcard := card_projectivization_minus_point (F := F) n α
    have hsubtype_lt : Nat.card {x : P // x ≠ α} < Nat.card P := by
      rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
      exact Fintype.card_lt_of_injective_of_notMem
        (fun x : {x : P // x ≠ α} => (x : P)) Subtype.val_injective (b := α) (by simp)
    rw [hcard] at hsubtype_lt
    exact hsubtype_lt
  let badPoint (x : {x : X // f x ≠ 0}) : P := Projectivization.mk F (f x) x.property
  have hdomain_lt : Fintype.card {x : X // f x ≠ 0} < Fintype.card P := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
    have hsub :
        Nat.card {x : X // f x ≠ 0} ≤ Nat.card X := by
      rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
      exact Fintype.card_le_of_injective (fun x : {x : X // f x ≠ 0} => (x : X))
        Subtype.val_injective
    exact lt_of_le_of_lt (hsub.trans hX) hbound_lt
  have hnot_surjective : ¬ Function.Surjective badPoint := by
    intro hsurj
    have hle := Fintype.card_le_of_surjective badPoint hsurj
    omega
  obtain ⟨p, hp⟩ := not_forall.mp hnot_surjective
  push Not at hp
  have hp_avoid : ∀ x, f x ≠ 0 → ¬ f x ∈ p.submodule := by
    intro x hx hmem
    have hspan : F ∙ f x = p.submodule := by
      refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
      · exact Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hmem)
      · rw [finrank_span_singleton hx, p.finrank_submodule]
    have hmk : Projectivization.mk F (f x) hx = p := by
      apply Projectivization.submodule_injective
      simpa [Projectivization.submodule_mk] using hspan
    exact hp ⟨x, hx⟩ hmk
  have hdim : Module.finrank F (Fin (n + 1) → F) = Module.finrank F p.submodule + n := by
    rw [Module.finrank_fin_fun, p.finrank_submodule]
    omega
  obtain ⟨M, hM⟩ := exists_linearMap_of_ker (F := F) n p.submodule hdim
  refine ⟨M, ?_⟩
  ext x
  constructor
  · intro hx
    by_contra hfx
    have hmem : f x ∈ LinearMap.ker M := by
      simpa [LinearMap.mem_ker] using hx
    rw [hM] at hmem
    exact hp_avoid x hfx hmem
  · intro hx
    have hfx : f x = 0 := by
      simpa using hx
    simp [hfx]

/--
Base case of Theorem 1: `n + 1` equations over a small finite set can be replaced
by at most `n` equations in their span.
-/
lemma theorem_1_base_case {X : Type*} [Finite X] (n : ℕ) (S : Set (X → F))
    (hS : S.Finite) (h_card : S.ncard = n + 1)
    (hX : Nat.card X ≤
      (Fintype.card F ^ (n + 1) - Fintype.card F) / (Fintype.card F - 1)) :
    ∃ T : Set (X → F),
      T ⊆ Submodule.span F S ∧ T.Finite ∧ T.ncard ≤ n ∧ ZeroSet T = ZeroSet S := by
  classical
  haveI : Finite S := hS
  haveI : Fintype S := Fintype.ofFinite S
  have hcard_subtype : Nat.card S = n + 1 := by
    rw [← Set.ncard_univ S, Set.ncard_coe]
    exact h_card
  let eS : S ≃ Fin (n + 1) := Finite.equivFinOfCardEq hcard_subtype
  let f : Fin (n + 1) → X → F := fun i => (eS.symm i).1
  have hf_range : Set.range f = S := by
    ext g
    constructor
    · rintro ⟨i, rfl⟩
      exact (eS.symm i).2
    · intro hg
      exact ⟨eS ⟨g, hg⟩, by simp [f]⟩
  obtain ⟨M, hM⟩ := theorem_1_aux (F := F) n (fun x i => f i x) hX
  let g : Fin n → X → F := fun k x => M (fun i => f i x) k
  refine ⟨Set.range g, ?_, Set.finite_range g, ?_, ?_⟩
  · rintro _ ⟨k, rfl⟩
    have hg :
        g k = ∑ i : Fin (n + 1), (M (fun j => if i = j then 1 else 0) k) • f i := by
      ext x
      have h := congr_fun (LinearMap.pi_apply_eq_sum_univ M (fun i => f i x)) k
      simpa [g, Finset.sum_apply, mul_comm] using h
    rw [hg]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _
        (Submodule.subset_span (by rw [← hf_range]; exact Set.mem_range_self i))
  · calc
      (Set.range g).ncard = (g '' Set.univ).ncard := by rw [Set.image_univ]
      _ ≤ (Set.univ : Set (Fin n)).ncard := Set.ncard_image_le
      _ = n := by simp
  · ext x
    have hleft : (∀ y ∈ Set.range g, y x = 0) ↔ M (fun i => f i x) = 0 := by
      constructor
      · intro h
        ext k
        exact h (g k) ⟨k, rfl⟩
      · intro h y hy
        rcases hy with ⟨k, rfl⟩
        exact congr_fun h k
    have hright : (∀ y ∈ S, y x = 0) ↔ (fun i => f i x) = 0 := by
      constructor
      · intro h
        ext i
        exact h (f i) (by rw [← hf_range]; exact Set.mem_range_self i)
      · intro h y hy
        rw [← hf_range] at hy
        rcases hy with ⟨i, rfl⟩
        exact congr_fun h i
    have hMx : M (fun i => f i x) = 0 ↔ (fun i => f i x) = 0 := by
      have := congrArg (fun U : Set X => x ∈ U) hM
      simpa using this
    change (∀ y ∈ Set.range g, y x = 0) ↔ (∀ y ∈ S, y x = 0)
    exact hleft.trans (hMx.trans hright.symm)

/--
Theorem 1: over a small finite set, any finite family of more than `n` functions can
be reduced to at most `n` functions in its span without changing its zero set.
-/
theorem theorem_1 {X : Type*} [Finite X] (n : ℕ) (S : Set (X → F)) (hS : S.Finite)
    (hn : S.ncard > n)
    (hX : Nat.card X ≤
      (Fintype.card F ^ (n + 1) - Fintype.card F) / (Fintype.card F - 1)) :
    ∃ T : Set (X → F),
      T ⊆ Submodule.span F S ∧ T.Finite ∧ T.ncard ≤ n ∧ ZeroSet T = ZeroSet S := by
  classical
  have h_ind :
      ∀ k, n + 1 ≤ k → ∀ S : Set (X → F), S.Finite → S.ncard = k →
        ∃ T : Set (X → F),
          T ⊆ Submodule.span F S ∧ T.Finite ∧ T.ncard ≤ n ∧ ZeroSet T = ZeroSet S := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base =>
        intro S hS hcard
        exact theorem_1_base_case (F := F) n S hS hcard hX
    | succ k hk ih =>
        intro S hS hcard
        obtain ⟨f, hf⟩ : ∃ f, f ∈ S := by
          have hpos : 0 < S.ncard := by omega
          exact (Set.ncard_pos hS).mp hpos
        let S' : Set (X → F) := S \ {f}
        have hS'_finite : S'.Finite := hS.diff
        have hS'_card : S'.ncard = k := by
          rw [Set.ncard_diff_singleton_of_mem hf, hcard]
          omega
        obtain ⟨T', hT'_span, hT'_finite, hT'_card, hT'_zero⟩ :=
          ih S' hS'_finite hS'_card
        let U : Set (X → F) := T' ∪ {f}
        have hU_finite : U.Finite := hT'_finite.union (Set.finite_singleton f)
        have hU_span : U ⊆ Submodule.span F S := by
          intro u hu
          rcases hu with hu | hu
          · exact (Submodule.span_mono (Set.diff_subset : S' ⊆ S)) (hT'_span hu)
          · rcases hu with rfl
            exact Submodule.subset_span hf
        have hU_zero : ZeroSet U = ZeroSet S := by
          ext x
          constructor
          · intro hx u huS
            by_cases huf : u = f
            · subst u
              exact hx f (by simp [U])
            · have hxS' : x ∈ ZeroSet S' := by
                rw [← hT'_zero]
                intro t ht
                exact hx t (by exact Or.inl ht)
              exact hxS' u ⟨huS, by simp [huf]⟩
          · intro hx u hu
            rcases hu with hu | hu
            · have hxT' : x ∈ ZeroSet T' := by
                rw [hT'_zero]
                intro t ht
                exact hx t ht.1
              exact hxT' u hu
            · have huf : u = f := by
                simpa using hu
              rw [huf]
              exact hx f hf
        have hU_card : U.ncard ≤ n + 1 := by
          calc
            U.ncard ≤ T'.ncard + ({f} : Set (X → F)).ncard := Set.ncard_union_le _ _
            _ ≤ n + 1 := by simpa using Nat.add_le_add_right hT'_card 1
        by_cases hU_small : U.ncard ≤ n
        · exact ⟨U, hU_span, hU_finite, hU_small, hU_zero⟩
        · have hU_card_eq : U.ncard = n + 1 := by omega
          obtain ⟨T'', hT''_span, hT''_finite, hT''_card, hT''_zero⟩ :=
            theorem_1_base_case (F := F) n U hU_finite hU_card_eq hX
          refine ⟨T'', ?_, hT''_finite, hT''_card, hT''_zero.trans hU_zero⟩
          exact hT''_span.trans (Submodule.span_le.mpr hU_span)
  exact h_ind S.ncard (by omega) S hS rfl

private lemma exists_lift_of_subset_span_image {K V W : Type*} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (n : ℕ) (φ : V →ₗ[K] W) {S : Set V} {U : Set W}
    (hU_finite : U.Finite) (hU_card : U.ncard ≤ n)
    (hU_span : U ⊆ Submodule.span K (φ '' S)) :
    ∃ T : Set V, T.Finite ∧ T.ncard ≤ n ∧ T ⊆ Submodule.span K S ∧ φ '' T = U := by
  classical
  haveI : Finite U := hU_finite
  haveI : Fintype U := Fintype.ofFinite U
  have hpre : ∀ y : U, ∃ v ∈ Submodule.span K S, φ v = y.1 := by
    intro y
    have hyspan := hU_span y.2
    rw [Submodule.span_image] at hyspan
    rcases hyspan with ⟨v, hv, hφ⟩
    exact ⟨v, hv, hφ⟩
  choose v hvspan hvmap using hpre
  refine ⟨Set.range v, Set.finite_range v, ?_, ?_, ?_⟩
  · calc
      (Set.range v).ncard = (v '' Set.univ).ncard := by rw [Set.image_univ]
      _ ≤ (Set.univ : Set U).ncard := Set.ncard_image_le
      _ = U.ncard := by simp
      _ ≤ n := hU_card
  · rintro x ⟨y, rfl⟩
    exact hvspan y
  · ext y
    constructor
    · rintro ⟨x, ⟨u, rfl⟩, rfl⟩
      simp [hvmap u, u.2]
    · intro hy
      exact ⟨v ⟨y, hy⟩, ⟨⟨y, hy⟩, rfl⟩, hvmap ⟨y, hy⟩⟩

/--
Corollary 2: zero loci in affine `n`-space over a finite field can be defined using
at most `n` members of the original span.
-/
theorem corollary_2 {K : Type*} [Field K] [Finite K] (n : ℕ) (hn : n > 0)
    (V : Type*) [AddCommGroup V] [Module K V]
    (φ : V →ₗ[K] ((Fin n → K) → K)) (S : Set V) (hS : S.Finite) :
    ∃ T : Set V,
      T.Finite ∧ T.ncard ≤ n ∧ T ⊆ Submodule.span K S ∧
        ZeroSet (φ '' T) = ZeroSet (φ '' S) := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  let Y : Set ((Fin n → K) → K) := φ '' S
  have hY_finite : Y.Finite := hS.image φ
  have hX : Nat.card (Fin n → K) ≤
      (Fintype.card K ^ (n + 1) - Fintype.card K) / (Fintype.card K - 1) := by
    simpa using card_affine_le_projective_bound (F := K) n hn
  obtain ⟨U, hU_span, hU_finite, hU_card, hU_zero⟩ :
      ∃ U : Set ((Fin n → K) → K),
        U ⊆ Submodule.span K Y ∧ U.Finite ∧ U.ncard ≤ n ∧ ZeroSet U = ZeroSet Y := by
    by_cases hYn : Y.ncard > n
    · exact theorem_1 (F := K) n Y hY_finite hYn hX
    · exact ⟨Y, Submodule.subset_span, hY_finite, le_of_not_gt hYn, rfl⟩
  obtain ⟨T, hT_finite, hT_card, hT_span, hT_image⟩ :=
    exists_lift_of_subset_span_image (K := K) n φ hU_finite hU_card hU_span
  exact ⟨T, hT_finite, hT_card, hT_span, by rw [hT_image, hU_zero]⟩

/--
Corollary 3: a nonempty projective zero locus in `P^n(F)` can be defined using at
most `n` members of the original span.
-/
theorem corollary_3 {K : Type*} [Field K] [Finite K] (n : ℕ)
    (V : Type*) [AddCommGroup V] [Module K V]
    (φ : V →ₗ[K] (Projectivization K (Fin (n + 1) → K) → K)) (S : Set V) (hS : S.Finite)
    (h_nonempty : ZeroSet (φ '' S) ≠ ∅) :
    ∃ T : Set V,
      T.Finite ∧ T.ncard ≤ n ∧ T ⊆ Submodule.span K S ∧
        ZeroSet (φ '' T) = ZeroSet (φ '' S) := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  let P := Projectivization K (Fin (n + 1) → K)
  obtain ⟨α, hα⟩ : (ZeroSet (φ '' S)).Nonempty := Set.nonempty_iff_ne_empty.2 h_nonempty
  let X' := {x : P // x ≠ α}
  let restrict : (P → K) →ₗ[K] (X' → K) := {
    toFun f x := f x.1
    map_add' f g := by ext x; simp
    map_smul' c f := by ext x; simp
  }
  let Y : Set (P → K) := φ '' S
  let Y' : Set (X' → K) := restrict '' Y
  have hY_finite : Y.Finite := hS.image φ
  have hY'_finite : Y'.Finite := hY_finite.image restrict
  have hX' : Nat.card X' ≤
      (Fintype.card K ^ (n + 1) - Fintype.card K) / (Fintype.card K - 1) := by
    rw [show Nat.card X' =
      Nat.card {x : Projectivization K (Fin (n + 1) → K) // x ≠ α} from rfl]
    exact le_of_eq (card_projectivization_minus_point (F := K) n α)
  obtain ⟨U', hU'_span, hU'_finite, hU'_card, hU'_zero⟩ :
      ∃ U' : Set (X' → K),
        U' ⊆ Submodule.span K Y' ∧ U'.Finite ∧ U'.ncard ≤ n ∧ ZeroSet U' = ZeroSet Y' := by
    by_cases hcard : Y'.ncard > n
    · exact theorem_1 (F := K) n Y' hY'_finite hcard hX'
    · exact ⟨Y', Submodule.subset_span, hY'_finite, le_of_not_gt hcard, rfl⟩
  obtain ⟨U, hU_finite, hU_card, hU_span, hU_image⟩ :=
    exists_lift_of_subset_span_image (K := K) n restrict hU'_finite hU'_card hU'_span
  have hspan_vanish : ∀ f ∈ Submodule.span K Y, f α = 0 := by
    intro f hf
    have hle : Submodule.span K Y ≤
        LinearMap.ker (LinearMap.proj α : (P → K) →ₗ[K] K) := by
      rw [Submodule.span_le]
      intro g hg
      exact hα g hg
    exact hle hf
  have hU_zero : ZeroSet U = ZeroSet Y := by
    ext x
    by_cases hx : x = α
    · subst x
      constructor
      · intro _ y hy
        exact hα y hy
      · intro _ u hu
        exact hspan_vanish u (hU_span hu)
    · let x' : X' := ⟨x, hx⟩
      have hUx : (∀ u ∈ U, u x = 0) ↔ (∀ u' ∈ U', u' x' = 0) := by
        rw [← hU_image]
        constructor
        · intro h u' hu'
          rcases hu' with ⟨u, hu, rfl⟩
          exact h u hu
        · intro h u hu
          exact h (restrict u) ⟨u, hu, rfl⟩
      have hYx : (∀ y ∈ Y, y x = 0) ↔ (∀ y' ∈ Y', y' x' = 0) := by
        constructor
        · intro h y' hy'
          rcases hy' with ⟨y, hy, rfl⟩
          exact h y hy
        · intro h y hy
          exact h (restrict y) ⟨y, hy, rfl⟩
      have hpoint := congrArg (fun Z : Set X' => x' ∈ Z) hU'_zero
      simpa [ZeroSet, hUx, hYx] using hpoint
  obtain ⟨T, hT_finite, hT_card, hT_span, hT_image⟩ :=
    exists_lift_of_subset_span_image (K := K) n φ hU_finite hU_card hU_span
  exact ⟨T, hT_finite, hT_card, hT_span, by rw [hT_image, hU_zero]⟩

/--
Proposition 1: the cardinality bound in Theorem 1 is sharp.
-/
theorem prop_1 (n : ℕ) (hn : n > 0) :
    ∃ (X : Set (Fin (n + 1) → F)) (f : Fin (n + 1) → X → F),
      X.ncard =
          (Fintype.card F ^ (n + 1) - Fintype.card F) / (Fintype.card F - 1) + 1 ∧
        (∀ x : X, ∃ i, f i x ≠ 0) ∧
      (∀ (g : Fin n → X → F), (∀ j, g j ∈ Submodule.span F (Set.range f)) →
          ∃ x : X, ∀ j, g j x = 0) := by
  classical
  have _ : 0 < n := hn
  let P := Projectivization F (Fin (n + 1) → F)
  let X : Set (Fin (n + 1) → F) := Set.range (Projectivization.rep : P → Fin (n + 1) → F)
  have hrep_injective :
      Function.Injective (Projectivization.rep : P → Fin (n + 1) → F) := by
    intro p q hpq
    apply Projectivization.submodule_injective
    rw [Projectivization.submodule_eq, Projectivization.submodule_eq, hpq]
  have hX_card : X.ncard =
      (Fintype.card F ^ (n + 1) - Fintype.card F) / (Fintype.card F - 1) + 1 := by
    change (Set.range (Projectivization.rep : P → Fin (n + 1) → F)).ncard =
      (Fintype.card F ^ (n + 1) - Fintype.card F) / (Fintype.card F - 1) + 1
    rw [Set.ncard_range_of_injective hrep_injective]
    exact card_projectivization_eq_bound_add_one (F := F) n
  let f : Fin (n + 1) → X → F := fun i x => x.1 i
  refine ⟨X, f, hX_card, ?_, ?_⟩
  · intro x
    rcases x.2 with ⟨p, hp⟩
    have hxne : (x : Fin (n + 1) → F) ≠ 0 := by
      rw [← hp]
      exact p.rep_nonzero
    exact Function.ne_iff.mp hxne
  · intro g hg
    have hcoeff :
        ∀ j : Fin n, ∃ c : Fin (n + 1) → F,
          ∀ x : X, g j x = ∑ i : Fin (n + 1), c i * x.1 i := by
      intro j
      obtain ⟨c, hc⟩ :=
        (Submodule.mem_span_range_iff_exists_fun (R := F) (v := f)).mp (hg j)
      refine ⟨c, ?_⟩
      intro x
      have := congr_fun hc x
      simpa [f, Finset.sum_apply, smul_eq_mul] using this.symm
    choose c hc using hcoeff
    let A : Matrix (Fin n) (Fin (n + 1)) F := fun j i => c j i
    have hker_ne : LinearMap.ker (Matrix.mulVecLin A) ≠ ⊥ := by
      apply LinearMap.ker_ne_bot_of_finrank_lt
      rw [Module.finrank_fin_fun, Module.finrank_fin_fun]
      omega
    obtain ⟨v, hvker, hvne⟩ := (Submodule.ne_bot_iff _).mp hker_ne
    let p : P := Projectivization.mk F v hvne
    let x : X := ⟨p.rep, ⟨p, rfl⟩⟩
    have hvzero : A.mulVec v = 0 := by
      simpa [LinearMap.mem_ker] using hvker
    have hxzero : A.mulVec x.1 = 0 := by
      obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep (K := F) v hvne
      have hAv : Matrix.mulVecLin A v = 0 := by simpa [Matrix.mulVecLin] using hvzero
      change Matrix.mulVecLin A p.rep = 0
      rw [← ha]
      simp [hAv]
    refine ⟨x, fun j => ?_⟩
    rw [hc j x]
    simpa [A, Matrix.mulVec, dotProduct] using congr_fun hxzero j

/--
The coordinate functions on affine `n`-space need `n` equations to cut out the origin:
any `n - 1` linear combinations have at least `|F|` common zeros.
-/
theorem remark_example (n : ℕ) (hn : n > 0) :
    let f : Fin n → (Fin n → F) → F := fun i x => x i
    ZeroSet (Set.range f) = {0} ∧
    ∀ (g : Fin (n - 1) → (Fin n → F) → F),
      (∀ j, g j ∈ Submodule.span F (Set.range f)) →
      (ZeroSet (Set.range g)).ncard ≥ Fintype.card F := by
  classical
  intro f
  constructor
  · ext x
    constructor
    · intro hx
      ext i
      exact hx (f i) ⟨i, rfl⟩
    · intro hx y hy
      rcases hy with ⟨i, rfl⟩
      have hx0 : x = 0 := by
        simpa using hx
      simp [hx0, f]
  · intro g hg
    have hcoeff :
        ∀ j : Fin (n - 1), ∃ c : Fin n → F,
          ∀ x : Fin n → F, g j x = ∑ i : Fin n, c i * x i := by
      intro j
      obtain ⟨c, hc⟩ :=
        (Submodule.mem_span_range_iff_exists_fun (R := F) (v := f)).mp (hg j)
      refine ⟨c, ?_⟩
      intro x
      have := congr_fun hc x
      simpa [f, Finset.sum_apply, smul_eq_mul] using this.symm
    choose c hc using hcoeff
    let A : Matrix (Fin (n - 1)) (Fin n) F := fun j i => c j i
    have hker_ne : LinearMap.ker (Matrix.mulVecLin A) ≠ ⊥ := by
      apply LinearMap.ker_ne_bot_of_finrank_lt
      rw [Module.finrank_fin_fun, Module.finrank_fin_fun]
      omega
    obtain ⟨v, hvker, hvne⟩ := (Submodule.ne_bot_iff _).mp hker_ne
    have hvzero : A.mulVec v = 0 := by
      simpa [LinearMap.mem_ker] using hvker
    let line : F → Fin n → F := fun a => a • v
    have hline_subset : Set.range line ⊆ ZeroSet (Set.range g) := by
      rintro x ⟨a, rfl⟩ y hy
      rcases hy with ⟨j, rfl⟩
      rw [hc j (a • v)]
      have hcomponent := congr_fun hvzero j
      simpa [A, Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]
        using congrArg (fun z => a * z) hcomponent
    have hline_card : (Set.range line).ncard = Nat.card F := by
      exact Set.ncard_range_of_injective (fun a b h => smul_left_injective F hvne h)
    calc
      Fintype.card F = Nat.card F := by rw [Nat.card_eq_fintype_card]
      _ = (Set.range line).ncard := hline_card.symm
      _ ≤ (ZeroSet (Set.range g)).ncard := Set.ncard_le_ncard hline_subset

end LeanPool.Fineqs
