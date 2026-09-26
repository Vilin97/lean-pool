/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.HasseWeil.FiniteExtensionRiemannSpace

/-!
# Local and away-regular subspaces of a function field

For an exhaustive place `P`, the one-point Riemann space is the intersection
of two elementary subspaces: functions with a bounded pole at `P`, and
functions regular at every place away from `P`.  This is the two-open-cover
decomposition used by the Cech form of Riemann's inequality.
-/

@[expose] public section

namespace BGS.HasseWeil

open BGS.CorvajaZannier

noncomputable section

variable (K : Type*) [Field K] [Fintype K] [DecidableEq K]
  [DecidableEq (RatFunc K)]
variable (L : Type*) [Field L] [Algebra (RatFunc K) L]
  [FiniteDimensional (RatFunc K) L]
  [Algebra.IsSeparable (RatFunc K) L]

local instance localPoleConstantAlgebra : Algebra K L :=
  RingHom.toAlgebra ((algebraMap (RatFunc K) L).comp
    (algebraMap K (RatFunc K)))

local instance localPoleConstantTower : IsScalarTower K (RatFunc K) L :=
  IsScalarTower.of_algebraMap_eq' rfl

/-- Functions whose pole at `P` has order at most `n`, with no condition at
the other places. -/
def finiteExtensionLocalPoleSpace
    (P : FiniteExtensionPlace K L) (n : ℕ) : Submodule K L where
  carrier := {x | x = 0 ∨
    (x ≠ 0 ∧ -(n : ℤ) ≤ finiteExtensionPrincipalDivisor K L x P)}
  zero_mem' := Or.inl rfl
  add_mem' := by
    rintro x y (hx0 | ⟨hx0, hx⟩) (hy0 | ⟨hy0, hy⟩)
    · exact Or.inl (by simp [hx0, hy0])
    · subst x
      simpa using
        (Or.inr ⟨hy0, hy⟩ : y = 0 ∨
          (y ≠ 0 ∧ -(n : ℤ) ≤ finiteExtensionPrincipalDivisor K L y P))
    · subst y
      simpa using
        (Or.inr ⟨hx0, hx⟩ : x = 0 ∨
          (x ≠ 0 ∧ -(n : ℤ) ≤ finiteExtensionPrincipalDivisor K L x P))
    · by_cases hxy : x + y = 0
      · exact Or.inl hxy
      · refine Or.inr ⟨hxy, ?_⟩
        exact le_trans (le_min hx hy)
          (finiteExtensionPrincipalDivisor_add_ge_min
            K L x y hx0 hy0 hxy P)
  smul_mem' := by
    intro c x hx
    by_cases hc : c = 0
    · subst c
      exact Or.inl (zero_smul K x)
    rcases hx with hx | ⟨hx, horder⟩
    · subst x
      exact Or.inl (smul_zero c)
    · have hcL : algebraMap K L c ≠ 0 := by
        simpa only [map_zero] using (algebraMap K L).injective.ne hc
      have hcx : c • x ≠ 0 := by
        rw [Algebra.smul_def]
        exact mul_ne_zero hcL hx
      refine Or.inr ⟨hcx, ?_⟩
      rw [Algebra.smul_def,
        finiteExtensionPrincipalDivisor_mul K L _ _ hcL hx,
        finiteExtensionPrincipalDivisor_algebraMap_constant K L c hc]
      simpa using horder

@[simp]
theorem mem_finiteExtensionLocalPoleSpace_iff
    (P : FiniteExtensionPlace K L) (n : ℕ) (x : L) :
    x ∈ finiteExtensionLocalPoleSpace K L P n ↔
      x = 0 ∨
        (x ≠ 0 ∧ -(n : ℤ) ≤ finiteExtensionPrincipalDivisor K L x P) :=
  Iff.rfl

/-- Functions regular at every exhaustive place other than `P`. -/
def finiteExtensionAwayRegularSpace
    (P : FiniteExtensionPlace K L) : Submodule K L where
  carrier := {x | x = 0 ∨
    (x ≠ 0 ∧ ∀ v, v ≠ P → 0 ≤ finiteExtensionPrincipalDivisor K L x v)}
  zero_mem' := Or.inl rfl
  add_mem' := by
    rintro x y (hx0 | ⟨hx0, hx⟩) (hy0 | ⟨hy0, hy⟩)
    · exact Or.inl (by simp [hx0, hy0])
    · subst x
      simpa only [zero_add, Set.mem_ofPred_eq] using
        (Or.inr ⟨hy0, hy⟩ : y = 0 ∨
          (y ≠ 0 ∧ ∀ v, v ≠ P →
            0 ≤ finiteExtensionPrincipalDivisor K L y v))
    · subst y
      simpa only [add_zero, Set.mem_ofPred_eq] using
        (Or.inr ⟨hx0, hx⟩ : x = 0 ∨
          (x ≠ 0 ∧ ∀ v, v ≠ P →
            0 ≤ finiteExtensionPrincipalDivisor K L x v))
    · by_cases hxy : x + y = 0
      · exact Or.inl hxy
      · refine Or.inr ⟨hxy, ?_⟩
        intro v hv
        exact le_trans (le_min (hx v hv) (hy v hv))
          (finiteExtensionPrincipalDivisor_add_ge_min
            K L x y hx0 hy0 hxy v)
  smul_mem' := by
    intro c x hx
    by_cases hc : c = 0
    · subst c
      exact Or.inl (zero_smul K x)
    rcases hx with hx | ⟨hx, horders⟩
    · subst x
      exact Or.inl (smul_zero c)
    · have hcL : algebraMap K L c ≠ 0 := by
        simpa only [map_zero] using (algebraMap K L).injective.ne hc
      have hcx : c • x ≠ 0 := by
        rw [Algebra.smul_def]
        exact mul_ne_zero hcL hx
      refine Or.inr ⟨hcx, ?_⟩
      intro v hv
      rw [Algebra.smul_def,
        finiteExtensionPrincipalDivisor_mul K L _ _ hcL hx,
        finiteExtensionPrincipalDivisor_algebraMap_constant K L c hc]
      simpa using horders v hv

@[simp]
theorem mem_finiteExtensionAwayRegularSpace_iff
    (P : FiniteExtensionPlace K L) (x : L) :
    x ∈ finiteExtensionAwayRegularSpace K L P ↔
      x = 0 ∨
        (x ≠ 0 ∧ ∀ v, v ≠ P →
          0 ≤ finiteExtensionPrincipalDivisor K L x v) :=
  Iff.rfl

/-- The local pole filtration is increasing. -/
theorem finiteExtensionLocalPoleSpace_mono
    (P : FiniteExtensionPlace K L) {m n : ℕ} (hmn : m ≤ n) :
    finiteExtensionLocalPoleSpace K L P m ≤
      finiteExtensionLocalPoleSpace K L P n := by
  intro x hx
  rw [mem_finiteExtensionLocalPoleSpace_iff] at hx ⊢
  rcases hx with rfl | ⟨hx0, hx⟩
  · exact Or.inl rfl
  · have hmnZ : (m : ℤ) ≤ (n : ℤ) := by exact_mod_cast hmn
    exact Or.inr ⟨hx0, le_trans (Int.neg_le_neg hmnZ) hx⟩

/-- The one-point Riemann space is the intersection of its local pole bound
and its away-regular condition. -/
theorem finiteExtensionOnePointRiemannSpace_eq_inf
    (P : FiniteExtensionPlace K L) (n : ℕ) :
    finiteExtensionOnePointRiemannSpace K L P n =
      finiteExtensionLocalPoleSpace K L P n ⊓
        finiteExtensionAwayRegularSpace K L P := by
  ext x
  rw [mem_finiteExtensionOnePointRiemannSpace_iff,
    Submodule.mem_inf, mem_finiteExtensionLocalPoleSpace_iff,
    mem_finiteExtensionAwayRegularSpace_iff]
  constructor
  · rintro (rfl | ⟨hx0, hP, hAway⟩)
    · exact ⟨Or.inl rfl, Or.inl rfl⟩
    · exact ⟨Or.inr ⟨hx0, hP⟩, Or.inr ⟨hx0, hAway⟩⟩
  · rintro ⟨hlocal, hAway⟩
    rcases hlocal with rfl | ⟨hx0, hP⟩
    · exact Or.inl rfl
    · rcases hAway with hzero | ⟨_, hAway⟩
      · exact (hx0 hzero).elim
      · exact Or.inr ⟨hx0, hP, hAway⟩

/-- At level zero the same intersection is the all-place regular space. -/
theorem finiteExtensionRiemannSpace_zero_eq_local_inf_away
    (P : FiniteExtensionPlace K L) :
    finiteExtensionRiemannSpace K L 0 =
      finiteExtensionLocalPoleSpace K L P 0 ⊓
        finiteExtensionAwayRegularSpace K L P := by
  rw [← finiteExtensionOnePointRiemannSpace_eq_inf K L P 0]
  apply congrArg (finiteExtensionRiemannSpace K L)
  ext v
  by_cases hv : v = P
  · subst v
    simp
  · simp

end

end BGS.HasseWeil
