/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.HasseWeil.FilteredDimension
public import LeanPool.MarkoffModP.BGS.HasseWeil.FiniteExtensionRiemannSpace

/-!
# Strict levels in one-point filtrations

This file separates the filtration-counting argument from any degree-one
leading-coefficient cancellation.  For a nested filtration whose successive
finrank jumps are bounded by `d`, it bounds the final finrank by `d` times the
number of strict levels.  A matching lower bound therefore forces many strict
levels.

For the one-point Riemann filtration, a section that first appears at level
`n + 1` automatically has exact pole order `-(n + 1)`.  Choosing one section
at every strict level gives a pairwise-distinct family of exact pole orders,
with no hypothesis on the degree of the distinguished place.
-/

@[expose] public section

namespace BGS.HasseWeil

noncomputable section

variable {K L : Type*} [Field K] [AddCommGroup L] [Module K L]

/-- Levels below `N` at which a nested filtration grows strictly. -/
noncomputable def strictFiltrationLevels
    (R : ℕ → Submodule K L) (N : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range N).filter (fun n => R n < R (n + 1))

@[simp]
theorem strictFiltrationLevels_zero (R : ℕ → Submodule K L) :
    strictFiltrationLevels R 0 = ∅ := by
  simp [strictFiltrationLevels]

theorem strictFiltrationLevels_succ_card_of_lt
    (R : ℕ → Submodule K L) (n : ℕ) (h : R n < R (n + 1)) :
    (strictFiltrationLevels R (n + 1)).card =
      (strictFiltrationLevels R n).card + 1 := by
  classical
  simp only [strictFiltrationLevels, Finset.range_add_one, Finset.filter_insert]
  rw [ite_eq_left h, Finset.card_insert_of_notMem]
  simp

theorem strictFiltrationLevels_succ_card_of_not_lt
    (R : ℕ → Submodule K L) (n : ℕ) (h : ¬ R n < R (n + 1)) :
    (strictFiltrationLevels R (n + 1)).card =
      (strictFiltrationLevels R n).card := by
  classical
  simp only [strictFiltrationLevels, Finset.range_add_one, Finset.filter_insert]
  rw [ite_eq_right h]

/-- If every nontrivial step of a nested filtration has dimension increase at
most `d`, then the total dimension is bounded by `d` times the number of
strict steps, plus the initial dimension. -/
theorem finrank_le_initial_add_mul_card_strictFiltrationLevels
    (R : ℕ → Submodule K L) (d : ℕ)
    (hnested : ∀ n, R n ≤ R (n + 1))
    (hjump : ∀ n, Module.finrank K (R (n + 1)) ≤
      Module.finrank K (R n) + d) :
    ∀ N, Module.finrank K (R N) ≤ Module.finrank K (R 0) +
      d * (strictFiltrationLevels R N).card := by
  intro N
  induction N with
  | zero => simp
  | succ n ih =>
      by_cases hstrict : R n < R (n + 1)
      · calc
          Module.finrank K (R (n + 1)) ≤
              Module.finrank K (R n) + d := hjump n
          _ ≤ (Module.finrank K (R 0) +
                d * (strictFiltrationLevels R n).card) + d :=
            Nat.add_le_add_right ih d
          _ = Module.finrank K (R 0) +
              d * (strictFiltrationLevels R (n + 1)).card := by
            rw [strictFiltrationLevels_succ_card_of_lt R n hstrict]
            simp [Nat.mul_add, Nat.add_assoc]
      · have heq : R n = R (n + 1) :=
          eq_of_le_of_not_lt (hnested n) hstrict
        calc
          Module.finrank K (R (n + 1)) = Module.finrank K (R n) := by rw [← heq]
          _ ≤ Module.finrank K (R 0) +
              d * (strictFiltrationLevels R n).card := ih
          _ = Module.finrank K (R 0) +
              d * (strictFiltrationLevels R (n + 1)).card := by
            rw [strictFiltrationLevels_succ_card_of_not_lt R n hstrict]

/-- A lower dimension bound forces many strict filtration levels. -/
theorem le_card_strictFiltrationLevels_of_initial_add_mul_le_finrank
    (R : ℕ → Submodule K L) {d m N : ℕ} (hd : 0 < d)
    (hnested : ∀ n, R n ≤ R (n + 1))
    (hjump : ∀ n, Module.finrank K (R (n + 1)) ≤
      Module.finrank K (R n) + d)
    (hlower : Module.finrank K (R 0) + d * m ≤
      Module.finrank K (R N)) :
    m ≤ (strictFiltrationLevels R N).card := by
  have hupper :=
    finrank_le_initial_add_mul_card_strictFiltrationLevels
      R d hnested hjump N
  have hmul : d * m ≤ d * (strictFiltrationLevels R N).card :=
    Nat.le_of_add_le_add_left (hlower.trans hupper)
  exact Nat.le_of_mul_le_mul_left hmul hd

end

end BGS.HasseWeil

namespace BGS.HasseWeil

open BGS.CorvajaZannier
open scoped Polynomial

noncomputable section


variable (K : Type*) [Field K] [Fintype K] [DecidableEq K]
  [DecidableEq (RatFunc K)]
variable (L : Type*) [Field L] [Algebra (RatFunc K) L]
  [FiniteDimensional (RatFunc K) L]
  [Algebra.IsSeparable (RatFunc K) L]

local instance strictLevelsConstantAlgebra : Algebra K L :=
  RingHom.toAlgebra ((algebraMap (RatFunc K) L).comp
    (algebraMap K (RatFunc K)))

local instance strictLevelsConstantTower :
    IsScalarTower K (RatFunc K) L :=
  IsScalarTower.of_algebraMap_eq' rfl

omit [Fintype K] [DecidableEq K] [DecidableEq (RatFunc K)]
  [FiniteDimensional (RatFunc K) L]
  [Algebra.IsSeparable (RatFunc K) L] in
private theorem exists_mem_not_mem_of_submodule_lt
    {S T : Submodule K L} (h : S < T) :
    ∃ x : L, x ∈ T ∧ x ∉ S := by
  have hnotle : ¬ T ≤ S := not_le_of_gt h
  by_contra hexists
  apply hnotle
  intro x hx
  by_contra hxNot
  exact hexists ⟨x, hx, hxNot⟩

/-- A section appearing for the first time at level `n + 1` has exact pole
order `-(n + 1)` at the distinguished place.  No residue-degree hypothesis
is needed. -/
theorem onePointRiemannSpace_order_eq_neg_succ_of_mem_not_mem
    (P : FiniteExtensionPlace K L) (n : ℕ) {x : L}
    (hxSucc : x ∈ finiteExtensionOnePointRiemannSpace K L P (n + 1))
    (hxNot : x ∉ finiteExtensionOnePointRiemannSpace K L P n) :
    x ≠ 0 ∧
      finiteExtensionPrincipalDivisor K L x P = -((n + 1 : ℕ) : ℤ) := by
  have hx0 : x ≠ 0 := by
    intro hx
    subst x
    exact hxNot (Submodule.zero_mem _)
  rcases
      (mem_finiteExtensionOnePointRiemannSpace_iff K L P (n + 1) x).mp
        hxSucc with
    hx | ⟨_, hxLower, hxAway⟩
  · exact (hx0 hx).elim
  · refine ⟨hx0, ?_⟩
    have hxNotLower : ¬ -(n : ℤ) ≤
        finiteExtensionPrincipalDivisor K L x P := by
      intro hxLowerN
      apply hxNot
      rw [mem_finiteExtensionOnePointRiemannSpace_iff]
      exact Or.inr ⟨hx0, hxLowerN, hxAway⟩
    have hxUpper : finiteExtensionPrincipalDivisor K L x P < -(n : ℤ) :=
      lt_of_not_ge hxNotLower
    omega

/-- Choose one section for every strict level below `N`.  The chosen sections
have pairwise distinct exact pole orders, hence are themselves pairwise
distinct. -/
theorem exists_onePointRiemannSpace_sections_indexed_by_strictLevels
    (P : FiniteExtensionPlace K L) (N : ℕ) :
    ∃ f : {n // n ∈ strictFiltrationLevels
        (K := K) (L := L)
        (fun m => finiteExtensionOnePointRiemannSpace K L P m) N} → L,
      (∀ i,
        f i ∈ finiteExtensionOnePointRiemannSpace K L P (i.1 + 1) ∧
        f i ∉ finiteExtensionOnePointRiemannSpace K L P i.1 ∧
        finiteExtensionPrincipalDivisor K L (f i) P =
          -((i.1 + 1 : ℕ) : ℤ)) ∧
      Function.Injective f := by
  classical
  let I := {n // n ∈ strictFiltrationLevels
    (K := K) (L := L)
    (fun m => finiteExtensionOnePointRiemannSpace K L P m) N}
  have hexists (i : I) : ∃ x : L,
      x ∈ finiteExtensionOnePointRiemannSpace K L P (i.1 + 1) ∧
      x ∉ finiteExtensionOnePointRiemannSpace K L P i.1 ∧
      finiteExtensionPrincipalDivisor K L x P =
        -((i.1 + 1 : ℕ) : ℤ) := by
    have hiStrict : finiteExtensionOnePointRiemannSpace K L P i.1 <
        finiteExtensionOnePointRiemannSpace K L P (i.1 + 1) :=
      (Finset.mem_filter.mp i.2).2
    obtain ⟨x, hxSucc, hxNot⟩ :=
      exists_mem_not_mem_of_submodule_lt K L hiStrict
    obtain ⟨_, hxOrder⟩ :=
      onePointRiemannSpace_order_eq_neg_succ_of_mem_not_mem
        K L P i.1 hxSucc hxNot
    exact ⟨x, hxSucc, hxNot, hxOrder⟩
  let f : I → L := fun i => Classical.choose (hexists i)
  have hf (i : I) :
      f i ∈ finiteExtensionOnePointRiemannSpace K L P (i.1 + 1) ∧
      f i ∉ finiteExtensionOnePointRiemannSpace K L P i.1 ∧
      finiteExtensionPrincipalDivisor K L (f i) P =
        -((i.1 + 1 : ℕ) : ℤ) :=
    Classical.choose_spec (hexists i)
  refine ⟨f, hf, ?_⟩
  intro i j hij
  apply Subtype.ext
  have horders : -((i.1 + 1 : ℕ) : ℤ) = -((j.1 + 1 : ℕ) : ℤ) := by
    calc
      -((i.1 + 1 : ℕ) : ℤ) =
          finiteExtensionPrincipalDivisor K L (f i) P := (hf i).2.2.symm
      _ = finiteExtensionPrincipalDivisor K L (f j) P := by rw [hij]
      _ = -((j.1 + 1 : ℕ) : ℤ) := (hf j).2.2
  omega

end


end BGS.HasseWeil
