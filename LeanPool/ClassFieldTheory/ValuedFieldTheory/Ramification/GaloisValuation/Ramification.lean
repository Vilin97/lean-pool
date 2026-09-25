/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import Mathlib.SetTheory.Cardinal.Finite
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Ramification.GaloisValuation.RamificationQuotients
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.DiscreteValuationField.PrincipalUnits.Core
public import Mathlib.Data.Rat.Lemmas

/-! # Ramification -/

@[expose] public section
namespace RamificationTheory

open LocalFieldTheory

/-!
# Ramification filtrations

This file provides the group-theoretic lower ramification APIs used by local CFT.
Concrete valued extensions supply the action quotient estimates; the subgroup
and normality/antitonicity consequences are proved here.
-/

noncomputable section

universe u v

namespace DiscreteValuationField

namespace AntitoneNormalSubgroupFiltration

variable {G : Type u} [Group G] (F : AntitoneNormalSubgroupFiltration G)

/-- The finite-level Herbrand step
`|G_i| / |G_0|`, written with `Nat.card` so it can be used before a global
fintype instance has been installed.  Positivity theorems below carry the
finite-level hypotheses needed to rule out the infinite-cardinality fallback
of `Nat.card`. -/
noncomputable def herbrandStep (i : Nat) : Rat :=
  (Nat.card (F.lower i) : Rat) / (Nat.card (F.lower 0) : Rat)

/-- The natural-index lower Herbrand function as the cumulative sum of the
finite-level steps through `0, ..., n - 1`. -/
noncomputable def herbrandFunctionNat (n : Nat) : Rat :=
  Finset.sum (Finset.range n) fun i => F.herbrandStep i

/-- States the theorem `herbrandFunctionNat_zero`. -/
@[simp] theorem herbrandFunctionNat_zero :
    F.herbrandFunctionNat 0 = 0 := by
  simp [herbrandFunctionNat]

/-- States the theorem `herbrandFunctionNat_succ`. -/
theorem herbrandFunctionNat_succ (n : Nat) :
    F.herbrandFunctionNat (n + 1) =
      F.herbrandFunctionNat n + F.herbrandStep n := by
  simp [herbrandFunctionNat, Finset.sum_range_succ]

/-- States the theorem `herbrandStep_nonneg`. -/
theorem herbrandStep_nonneg (i : Nat) :
    0 <= F.herbrandStep i := by
  exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

/-- States the theorem `herbrandStep_pos`. -/
theorem herbrandStep_pos (i : Nat)
    [Finite (F.lower i)] [Finite (F.lower 0)] :
    0 < F.herbrandStep i := by
  have hi : 0 < Nat.card (F.lower i) := Finite.card_pos
  have h0 : 0 < Nat.card (F.lower 0) := Finite.card_pos
  exact
    div_pos
      (Nat.cast_pos.mpr hi)
      (Nat.cast_pos.mpr h0)

/-- States the theorem `herbrandFunctionNat_mono`. -/
theorem herbrandFunctionNat_mono :
    Monotone F.herbrandFunctionNat := by
  intro m n hmn
  refine Nat.le_induction (m := m) ?base ?step n hmn
  · exact le_rfl
  · intro k _hmk ih
    exact le_trans ih (by
      rw [F.herbrandFunctionNat_succ k]
      exact le_add_of_nonneg_right (F.herbrandStep_nonneg k))

/-- Representative equality criterion in the graded piece `G_n/G_{n+1}`,
in left-quotient form. -/
theorem gradedPieceMk_eq_iff_inv_mul_mem (n : ℕ) (σ τ : F.lower n) :
    F.gradedPieceMk n σ = F.gradedPieceMk n τ ↔
      ((τ⁻¹ * σ : F.lower n) : G) ∈ F.lower (n + 1) := by
  rw [F.gradedPieceMk_eq_iff n σ τ]
  simpa [div_eq_mul_inv, Subgroup.mem_subgroupOf] using
    ((inferInstance :
      ((F.lower (n + 1)).subgroupOf (F.lower n)).Normal).mem_comm_iff
        (a := σ) (b := τ⁻¹))

/-- Representative equality criterion in the tame quotient `G_0/G_1`, in
left-quotient form. -/
theorem tameQuotientMk_eq_iff_inv_mul_mem (σ τ : F.inertiaSubgroup) :
    F.tameQuotientMk σ = F.tameQuotientMk τ ↔
      ((τ⁻¹ * σ : F.inertiaSubgroup) : G) ∈ F.wildInertiaSubgroup := by
  rw [F.tameQuotientMk_eq_iff σ τ]
  simpa [div_eq_mul_inv, Subgroup.mem_subgroupOf] using
    ((inferInstance :
      ((F.wildInertiaSubgroup).subgroupOf F.inertiaSubgroup).Normal).mem_comm_iff
        (a := σ) (b := τ⁻¹))

/-- The natural quotient map `G/G_n → G/G_m` for `m ≤ n`. -/
def quotientMapOfLe {m n : ℕ} (hmn : m ≤ n) :
    F.quotient n →* F.quotient m :=
  F.quotientMap F n m (MonoidHom.id G) (by
    intro σ hσ
    simpa using F.antitone hmn hσ)

/-- States the theorem `quotientMapOfLe_apply_mk`. -/
@[simp] theorem quotientMapOfLe_apply_mk {m n : ℕ} (hmn : m ≤ n)
    (σ : G) :
    F.quotientMapOfLe hmn (F.quotientMk n σ) =
      F.quotientMk m σ :=
  rfl

/-- Level-change quotient maps compose transitively. -/
theorem quotientMapOfLe_comp {l m n : ℕ}
    (hlm : l ≤ m) (hmn : m ≤ n) :
    (F.quotientMapOfLe hlm).comp (F.quotientMapOfLe hmn) =
      F.quotientMapOfLe (le_trans hlm hmn) := by
  apply MonoidHom.ext
  intro q
  refine F.quotient_inductionOn n
    (motive := fun q =>
      ((F.quotientMapOfLe hlm).comp (F.quotientMapOfLe hmn)) q =
        F.quotientMapOfLe (le_trans hlm hmn) q) q ?_
  intro σ
  change F.quotientMapOfLe hlm
      (F.quotientMapOfLe hmn (F.quotientMk n σ)) =
    F.quotientMapOfLe (le_trans hlm hmn) (F.quotientMk n σ)
  rw [F.quotientMapOfLe_apply_mk, F.quotientMapOfLe_apply_mk,
    F.quotientMapOfLe_apply_mk]

/-- The level-change quotient map for `n ≤ n` is the identity. -/
theorem quotientMapOfLe_refl (n : ℕ) :
    F.quotientMapOfLe (le_rfl : n ≤ n) = MonoidHom.id (F.quotient n) := by
  apply MonoidHom.ext
  intro q
  refine F.quotient_inductionOn n
    (motive := fun q =>
      F.quotientMapOfLe (le_rfl : n ≤ n) q =
        MonoidHom.id (F.quotient n) q) q ?_
  intro σ
  change F.quotientMapOfLe (le_rfl : n ≤ n) (F.quotientMk n σ) =
    F.quotientMk n σ
  exact F.quotientMapOfLe_apply_mk (le_rfl : n ≤ n) σ

/-- The subgroup of `G/G_n` represented by the coarser ramification group
`G_m`, for `m ≤ n`. -/
def quotientKernelOfLe {m n : ℕ} (_hmn : m ≤ n) :
    Subgroup (F.quotient n) :=
  (F.quotientMapOfLe _hmn).ker

/-- The map from the `m`th lower ramification group into `G/G_n`. -/
def levelSubgroupToQuotient {m n : ℕ} (_hmn : m ≤ n) :
    F.lower m →* F.quotient n :=
  (F.quotientMk n).comp (F.lower m).subtype

/-- States the theorem `levelSubgroupToQuotient_apply`. -/
@[simp] theorem levelSubgroupToQuotient_apply {m n : ℕ} (hmn : m ≤ n)
    (σ : F.lower m) :
    F.levelSubgroupToQuotient hmn σ =
      F.quotientMk n (σ : G) :=
  rfl

/-- The kernel of `G_m → G/G_n` is `G_n` inside `G_m`. -/
theorem levelSubgroupToQuotient_ker_eq {m n : ℕ} (hmn : m ≤ n) :
    (F.levelSubgroupToQuotient hmn).ker =
      (F.lower n).subgroupOf (F.lower m) := by
  ext σ
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  exact F.quotientMk_eq_one_iff n (σ : G)

/-- The range of `G_m → G/G_n` is the kernel subgroup of
`G/G_n → G/G_m`. -/
theorem levelSubgroupToQuotient_range_eq_quotientKernelOfLe {m n : ℕ}
    (hmn : m ≤ n) :
    (F.levelSubgroupToQuotient hmn).range = F.quotientKernelOfLe hmn := by
  ext q
  constructor
  · rintro ⟨σ, rfl⟩
    rw [quotientKernelOfLe, MonoidHom.mem_ker,
      F.levelSubgroupToQuotient_apply, F.quotientMapOfLe_apply_mk,
      F.quotientMk_eq_one_iff]
    exact σ.property
  · intro hq
    revert hq
    refine F.quotient_inductionOn n
      (motive := fun q =>
        q ∈ F.quotientKernelOfLe hmn →
          q ∈ (F.levelSubgroupToQuotient hmn).range) q ?_
    intro σ hq
    rw [quotientKernelOfLe, MonoidHom.mem_ker,
      F.quotientMapOfLe_apply_mk, F.quotientMk_eq_one_iff] at hq
    exact ⟨⟨σ, hq⟩, rfl⟩

/-- The kernel of `G/G_n → G/G_m` is the image of `G_m` in `G/G_n`. -/
theorem quotientMapOfLe_ker_eq_quotientKernelOfLe {m n : ℕ}
    (hmn : m ≤ n) :
    (F.quotientMapOfLe hmn).ker = F.quotientKernelOfLe hmn :=
  rfl

/-- The named kernel subgroup `G_m/G_n` is normal in `G/G_n`. -/
instance quotientKernelOfLe_normal {m n : ℕ} (hmn : m ≤ n) :
    (F.quotientKernelOfLe hmn).Normal := by
  rw [← F.quotientMapOfLe_ker_eq_quotientKernelOfLe hmn]
  infer_instance

/-- Representative kernel criterion for `G/G_n → G/G_m`. -/
theorem quotientMapOfLe_mk_eq_one_iff {m n : ℕ} (hmn : m ≤ n)
    (σ : G) :
    F.quotientMapOfLe hmn (F.quotientMk n σ) = 1 ↔
      σ ∈ F.lower m := by
  rw [F.quotientMapOfLe_apply_mk, F.quotientMk_eq_one_iff]

/-- Representative membership criterion for the kernel of `G/G_n → G/G_m`. -/
theorem quotientMapOfLe_mk_mem_ker_iff {m n : ℕ} (hmn : m ≤ n)
    (σ : G) :
    F.quotientMk n σ ∈ (F.quotientMapOfLe hmn).ker ↔
      σ ∈ F.lower m := by
  rw [MonoidHom.mem_ker, F.quotientMapOfLe_mk_eq_one_iff hmn σ]

/-- Equality after changing level, in right-quotient form. -/
theorem quotientMapOfLe_mk_eq_iff_div_mem {m n : ℕ} (hmn : m ≤ n)
    (σ τ : G) :
    F.quotientMapOfLe hmn (F.quotientMk n σ) =
        F.quotientMapOfLe hmn (F.quotientMk n τ) ↔
      σ / τ ∈ F.lower m := by
  rw [F.quotientMapOfLe_apply_mk, F.quotientMapOfLe_apply_mk,
    F.quotientMk_eq_iff]

/-- Equality after changing level, in left-quotient form. -/
theorem quotientMapOfLe_mk_eq_iff_inv_mul_mem {m n : ℕ} (hmn : m ≤ n)
    (σ τ : G) :
    F.quotientMapOfLe hmn (F.quotientMk n σ) =
        F.quotientMapOfLe hmn (F.quotientMk n τ) ↔
      τ⁻¹ * σ ∈ F.lower m := by
  rw [F.quotientMapOfLe_mk_eq_iff_div_mem hmn σ τ]
  simpa [div_eq_mul_inv] using
    ((inferInstance : (F.lower m).Normal).mem_comm_iff
      (a := σ) (b := τ⁻¹))

/-- Arbitrary class kernel criterion for `G/G_n → G/G_m`. -/
theorem quotientMapOfLe_eq_one_iff_exists_mem_repr {m n : ℕ}
    (hmn : m ≤ n) (q : F.quotient n) :
    F.quotientMapOfLe hmn q = 1 ↔
      ∃ σ : G, σ ∈ F.lower m ∧
        F.quotientMk n σ = q := by
  rw [← MonoidHom.mem_ker,
    F.quotientMapOfLe_ker_eq_quotientKernelOfLe hmn]
  rw [← F.levelSubgroupToQuotient_range_eq_quotientKernelOfLe hmn]
  constructor
  · rintro ⟨σ, rfl⟩
    exact ⟨(σ : G), σ.property, rfl⟩
  · rintro ⟨σ, hσ, rfl⟩
    exact ⟨⟨σ, hσ⟩, rfl⟩

/-- Kernel-membership criterion for an arbitrary class in `G/G_n → G/G_m`,
expanded by a representative from `G_m`. -/
theorem quotientMapOfLe_mem_ker_iff_exists_mem_repr {m n : ℕ}
    (hmn : m ≤ n) (q : F.quotient n) :
    q ∈ (F.quotientMapOfLe hmn).ker ↔
      ∃ σ : G, σ ∈ F.lower m ∧
        F.quotientMk n σ = q := by
  rw [MonoidHom.mem_ker]
  exact F.quotientMapOfLe_eq_one_iff_exists_mem_repr hmn q

/-- Membership in the named kernel subgroup of `G/G_n → G/G_m`, expanded by a
representative from `G_m`. -/
theorem mem_quotientKernelOfLe_iff_exists_mem_repr {m n : ℕ}
    (hmn : m ≤ n) (q : F.quotient n) :
    q ∈ F.quotientKernelOfLe hmn ↔
      ∃ σ : G, σ ∈ F.lower m ∧
        F.quotientMk n σ = q := by
  rw [← F.quotientMapOfLe_ker_eq_quotientKernelOfLe hmn]
  exact F.quotientMapOfLe_mem_ker_iff_exists_mem_repr hmn q

/-- Membership in the named kernel subgroup is the same as mapping to `1`
under the corresponding level-change map. -/
theorem mem_quotientKernelOfLe_iff_quotientMap_eq_one {m n : ℕ}
    (hmn : m ≤ n) (q : F.quotient n) :
    q ∈ F.quotientKernelOfLe hmn ↔
      F.quotientMapOfLe hmn q = 1 := by
  rw [← F.quotientMapOfLe_ker_eq_quotientKernelOfLe hmn,
    MonoidHom.mem_ker]

/-- Kernel subgroups are nested as the target quotient is coarsened:
`G_m/G_n` is contained in `G_l/G_n` for `l ≤ m ≤ n`. -/
theorem quotientKernelOfLe_le {l m n : ℕ}
    (hlm : l ≤ m) (hmn : m ≤ n) :
    F.quotientKernelOfLe hmn ≤
      F.quotientKernelOfLe (le_trans hlm hmn) := by
  intro q hq
  rw [F.mem_quotientKernelOfLe_iff_exists_mem_repr hmn] at hq
  rcases hq with ⟨σ, hσ, hqσ⟩
  rw [F.mem_quotientKernelOfLe_iff_exists_mem_repr (le_trans hlm hmn)]
  exact ⟨σ, F.antitone hlm hσ, hqσ⟩

/-- Membership in the coarser kernel after applying a level-change map is
equivalent to membership in the corresponding direct kernel. -/
theorem quotientMapOfLe_mem_quotientKernelOfLe_iff {l m n : ℕ}
    (hlm : l ≤ m) (hmn : m ≤ n) (q : F.quotient n) :
    F.quotientMapOfLe hmn q ∈ F.quotientKernelOfLe hlm ↔
      q ∈ F.quotientKernelOfLe (le_trans hlm hmn) := by
  rw [F.mem_quotientKernelOfLe_iff_quotientMap_eq_one hlm,
    F.mem_quotientKernelOfLe_iff_quotientMap_eq_one (le_trans hlm hmn)]
  change ((F.quotientMapOfLe hlm).comp (F.quotientMapOfLe hmn)) q = 1 ↔
    F.quotientMapOfLe (le_trans hlm hmn) q = 1
  rw [F.quotientMapOfLe_comp hlm hmn]

/-- The preimage of the coarser kernel subgroup under a level-change map is
the corresponding direct kernel subgroup. -/
theorem quotientMapOfLe_comap_quotientKernelOfLe_eq {l m n : ℕ}
    (hlm : l ≤ m) (hmn : m ≤ n) :
    Subgroup.comap (F.quotientMapOfLe hmn) (F.quotientKernelOfLe hlm) =
      F.quotientKernelOfLe (le_trans hlm hmn) := by
  ext q
  exact F.quotientMapOfLe_mem_quotientKernelOfLe_iff hlm hmn q

/-- Representative version of
`quotientMapOfLe_mem_quotientKernelOfLe_iff`. -/
theorem quotientMapOfLe_mk_mem_quotientKernelOfLe_iff {l m n : ℕ}
    (hlm : l ≤ m) (hmn : m ≤ n) (σ : G) :
    F.quotientMapOfLe hmn (F.quotientMk n σ) ∈
        F.quotientKernelOfLe hlm ↔
      σ ∈ F.lower l := by
  rw [F.quotientMapOfLe_mem_quotientKernelOfLe_iff hlm hmn,
    F.mem_quotientKernelOfLe_iff_quotientMap_eq_one (le_trans hlm hmn),
    F.quotientMapOfLe_apply_mk, F.quotientMk_eq_one_iff]

/-- Equality after changing level is kernel membership of the quotient `q / r`. -/
theorem quotientMapOfLe_eq_iff_div_mem_ker {m n : ℕ} (hmn : m ≤ n)
    (q r : F.quotient n) :
    F.quotientMapOfLe hmn q = F.quotientMapOfLe hmn r ↔
      q / r ∈ (F.quotientMapOfLe hmn).ker := by
  rw [MonoidHom.mem_ker]
  constructor
  · intro h
    rw [MonoidHom.map_div, h]
    exact div_self' ((F.quotientMapOfLe hmn) r)
  · intro h
    rwa [MonoidHom.map_div, div_eq_one] at h

/-- Equality after changing level is membership of `q / r` in the named kernel
subgroup of `G/G_n → G/G_m`. -/
theorem quotientMapOfLe_eq_iff_div_mem_quotientKernelOfLe {m n : ℕ}
    (hmn : m ≤ n) (q r : F.quotient n) :
    F.quotientMapOfLe hmn q = F.quotientMapOfLe hmn r ↔
      q / r ∈ F.quotientKernelOfLe hmn := by
  rw [F.quotientMapOfLe_eq_iff_div_mem_ker hmn q r,
    F.quotientMapOfLe_ker_eq_quotientKernelOfLe hmn]

/-- Level-change maps send the larger kernel subgroup `G_l/G_n` onto the
corresponding kernel subgroup `G_l/G_m`, for `l ≤ m ≤ n`. -/
theorem quotientMapOfLe_map_quotientKernelOfLe_eq {l m n : ℕ}
    (hlm : l ≤ m) (hmn : m ≤ n) :
    Subgroup.map (F.quotientMapOfLe hmn)
        (F.quotientKernelOfLe (le_trans hlm hmn)) =
      F.quotientKernelOfLe hlm := by
  ext q
  constructor
  · rintro ⟨x, hx, hxq⟩
    rcases
      (F.mem_quotientKernelOfLe_iff_exists_mem_repr
        (le_trans hlm hmn) x).1 hx with
      ⟨σ, hσ, hxσ⟩
    rw [← hxq, ← hxσ, F.quotientMapOfLe_apply_mk]
    exact (F.mem_quotientKernelOfLe_iff_exists_mem_repr hlm _).2
      ⟨σ, hσ, rfl⟩
  · intro hq
    rcases
      (F.mem_quotientKernelOfLe_iff_exists_mem_repr hlm q).1 hq with
      ⟨σ, hσ, hqσ⟩
    refine ⟨F.quotientMk n σ, ?_, ?_⟩
    · exact
        (F.mem_quotientKernelOfLe_iff_exists_mem_repr
          (le_trans hlm hmn) _).2 ⟨σ, hσ, rfl⟩
    · rw [F.quotientMapOfLe_apply_mk]
      exact hqσ

/-- A level-change map kills exactly the kernel subgroup it is named by. -/
theorem quotientMapOfLe_map_quotientKernelOfLe_eq_bot {m n : ℕ}
    (hmn : m ≤ n) :
    Subgroup.map (F.quotientMapOfLe hmn) (F.quotientKernelOfLe hmn) = ⊥ := by
  ext q
  constructor
  · rintro ⟨x, hx, hxq⟩
    have hx' : F.quotientMapOfLe hmn x = 1 :=
      (F.mem_quotientKernelOfLe_iff_quotientMap_eq_one hmn x).1 hx
    rw [← hxq, hx']
    simp
  · intro hq
    have hq' : q = 1 := by
      simpa using hq
    subst q
    exact ⟨1, (F.quotientKernelOfLe hmn).one_mem, by simp⟩

/-- The level-change map restricted to kernel subgroups:
`G_l/G_n → G_l/G_m`, for `l ≤ m ≤ n`. -/
def quotientKernelMapOfLe {l m n : ℕ} (hlm : l ≤ m) (hmn : m ≤ n) :
    F.quotientKernelOfLe (le_trans hlm hmn) →*
      F.quotientKernelOfLe hlm :=
  ((F.quotientMapOfLe hmn).domRestrict
      (F.quotientKernelOfLe (le_trans hlm hmn))).codRestrict
    (F.quotientKernelOfLe hlm)
    (by
      intro q
      exact
        (F.quotientMapOfLe_mem_quotientKernelOfLe_iff hlm hmn q).2 q.property)

/-- States the theorem `quotientKernelMapOfLe_apply`. -/
@[simp] theorem quotientKernelMapOfLe_apply {l m n : ℕ}
    (hlm : l ≤ m) (hmn : m ≤ n)
    (q : F.quotientKernelOfLe (le_trans hlm hmn)) :
    ((F.quotientKernelMapOfLe hlm hmn q :
      F.quotientKernelOfLe hlm) : F.quotient m) =
      F.quotientMapOfLe hmn (q : F.quotient n) :=
  rfl

/-- Restricted level-change maps on ramification kernels are identities at a
fixed quotient level. -/
theorem quotientKernelMapOfLe_refl {l m : ℕ} (hlm : l ≤ m) :
    F.quotientKernelMapOfLe hlm (le_rfl : m ≤ m) =
      MonoidHom.id (F.quotientKernelOfLe hlm) := by
  apply MonoidHom.ext
  intro q
  apply Subtype.ext
  change F.quotientMapOfLe (le_rfl : m ≤ m) (q : F.quotient m) =
    (q : F.quotient m)
  rw [F.quotientMapOfLe_refl m]
  rfl

/-- Restricted level-change maps on ramification kernels compose
transitively. -/
theorem quotientKernelMapOfLe_comp {k l m n : ℕ}
    (hkl : k ≤ l) (hlm : l ≤ m) (hmn : m ≤ n) :
    (F.quotientKernelMapOfLe hkl hlm).comp
        (F.quotientKernelMapOfLe (le_trans hkl hlm) hmn) =
      F.quotientKernelMapOfLe hkl (le_trans hlm hmn) := by
  apply MonoidHom.ext
  intro q
  apply Subtype.ext
  change F.quotientMapOfLe hlm
      (F.quotientMapOfLe hmn (q : F.quotient n)) =
    F.quotientMapOfLe (le_trans hlm hmn) (q : F.quotient n)
  change ((F.quotientMapOfLe hlm).comp (F.quotientMapOfLe hmn))
      (q : F.quotient n) =
    F.quotientMapOfLe (le_trans hlm hmn) (q : F.quotient n)
  rw [F.quotientMapOfLe_comp hlm hmn]

/-- The restricted map `G_l/G_n → G_l/G_m` has kernel `G_m/G_n`. -/
theorem quotientKernelMapOfLe_ker_eq {l m n : ℕ}
    (hlm : l ≤ m) (hmn : m ≤ n) :
    (F.quotientKernelMapOfLe hlm hmn).ker =
      (F.quotientKernelOfLe hmn).subgroupOf
        (F.quotientKernelOfLe (le_trans hlm hmn)) := by
  ext q
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  constructor
  · intro hq
    have hq' := congrArg Subtype.val hq
    change F.quotientMapOfLe hmn (q : F.quotient n) = 1 at hq'
    exact (F.mem_quotientKernelOfLe_iff_quotientMap_eq_one hmn
      (q : F.quotient n)).2 hq'
  · intro hq
    apply Subtype.ext
    change F.quotientMapOfLe hmn (q : F.quotient n) = 1
    exact (F.mem_quotientKernelOfLe_iff_quotientMap_eq_one hmn
      (q : F.quotient n)).1 hq

/-- The restricted map `G_l/G_n → G_l/G_m` is surjective. -/
theorem quotientKernelMapOfLe_surjective {l m n : ℕ}
    (hlm : l ≤ m) (hmn : m ≤ n) :
    Function.Surjective (F.quotientKernelMapOfLe hlm hmn) := by
  intro q
  rcases q with ⟨q, hq⟩
  have hq' :
      q ∈ Subgroup.map (F.quotientMapOfLe hmn)
        (F.quotientKernelOfLe (le_trans hlm hmn)) := by
    rw [F.quotientMapOfLe_map_quotientKernelOfLe_eq hlm hmn]
    exact hq
  rcases hq' with ⟨r, hr, hrq⟩
  refine ⟨⟨r, hr⟩, ?_⟩
  apply Subtype.ext
  exact hrq

/-- First isomorphism theorem inside ramification kernels:
`(G_l/G_n)/ker(G_l/G_n → G_l/G_m) ≃ G_l/G_m`, for `l ≤ m ≤ n`.
The kernel is identified with `G_m/G_n` by
`quotientKernelMapOfLe_ker_eq`. -/
def quotientKernelQuotientKerEquivQuotientKernelOfLe {l m n : ℕ}
    (hlm : l ≤ m) (hmn : m ≤ n) :
    F.quotientKernelOfLe (le_trans hlm hmn) ⧸
        (F.quotientKernelMapOfLe hlm hmn).ker ≃*
      F.quotientKernelOfLe hlm :=
  QuotientGroup.quotientKerEquivOfSurjective
    (F.quotientKernelMapOfLe hlm hmn)
    (F.quotientKernelMapOfLe_surjective hlm hmn)

/-- States the theorem `quotientKernelQuotientKerEquivQuotientKernelOfLe_mk'`. -/
theorem quotientKernelQuotientKerEquivQuotientKernelOfLe_mk'
    {l m n : ℕ} (hlm : l ≤ m) (hmn : m ≤ n)
    (q : F.quotientKernelOfLe (le_trans hlm hmn)) :
    F.quotientKernelQuotientKerEquivQuotientKernelOfLe hlm hmn
        (QuotientGroup.mk'
          (F.quotientKernelMapOfLe hlm hmn).ker q) =
      F.quotientKernelMapOfLe hlm hmn q := by
  exact QuotientGroup.kerLift_mk (F.quotientKernelMapOfLe hlm hmn) q

/-- Second-isomorphism-style form of the ramification-kernel quotient:
`(G_l/G_n)/(G_m/G_n) ≃ G_l/G_m`, for `l ≤ m ≤ n`. -/
def quotientKernelQuotientSubgroupOfEquivQuotientKernelOfLe {l m n : ℕ}
    (hlm : l ≤ m) (hmn : m ≤ n) :
    F.quotientKernelOfLe (le_trans hlm hmn) ⧸
        (F.quotientKernelOfLe hmn).subgroupOf
          (F.quotientKernelOfLe (le_trans hlm hmn)) ≃*
      F.quotientKernelOfLe hlm :=
  (QuotientGroup.quotientMulEquivOfEq
    (F.quotientKernelMapOfLe_ker_eq hlm hmn).symm).trans
      (F.quotientKernelQuotientKerEquivQuotientKernelOfLe hlm hmn)

/-- States the theorem `quotientKernelQuotientSubgroupOfEquivQuotientKernelOfLe_mk'`. -/
theorem quotientKernelQuotientSubgroupOfEquivQuotientKernelOfLe_mk'
    {l m n : ℕ} (hlm : l ≤ m) (hmn : m ≤ n)
    (q : F.quotientKernelOfLe (le_trans hlm hmn)) :
    F.quotientKernelQuotientSubgroupOfEquivQuotientKernelOfLe hlm hmn
        (QuotientGroup.mk'
          ((F.quotientKernelOfLe hmn).subgroupOf
            (F.quotientKernelOfLe (le_trans hlm hmn))) q) =
      F.quotientKernelMapOfLe hlm hmn q := by
  simpa [quotientKernelQuotientSubgroupOfEquivQuotientKernelOfLe] using
    F.quotientKernelQuotientKerEquivQuotientKernelOfLe_mk' hlm hmn q

/-- Cardinality form of the second-isomorphism quotient compatibility
`(G_l/G_n)/(G_m/G_n) ≃ G_l/G_m`. -/
theorem card_quotientKernelQuotientSubgroupOfLe {l m n : ℕ}
    (hlm : l ≤ m) (hmn : m ≤ n) [Finite G] :
    Nat.card
        (F.quotientKernelOfLe (le_trans hlm hmn) ⧸
          (F.quotientKernelOfLe hmn).subgroupOf
            (F.quotientKernelOfLe (le_trans hlm hmn))) =
      Nat.card (F.quotientKernelOfLe hlm) :=
  Nat.card_congr
    (F.quotientKernelQuotientSubgroupOfEquivQuotientKernelOfLe hlm hmn).toEquiv

/-- Arbitrary class equality criterion for `G/G_n → G/G_m`, expanded as a
representative of `q / r` from `G_m`. -/
theorem quotientMapOfLe_eq_iff_exists_mem_div_repr {m n : ℕ}
    (hmn : m ≤ n) (q r : F.quotient n) :
    F.quotientMapOfLe hmn q = F.quotientMapOfLe hmn r ↔
      ∃ σ : G, σ ∈ F.lower m ∧
        F.quotientMk n σ = q / r := by
  rw [F.quotientMapOfLe_eq_iff_div_mem_quotientKernelOfLe hmn q r,
    F.mem_quotientKernelOfLe_iff_exists_mem_repr hmn]

/-- The ramification subquotient `G_m/G_n` is canonically the kernel of
`G/G_n → G/G_m`. -/
def subquotientEquivQuotientKernelOfLe {m n : ℕ} (hmn : m ≤ n) :
    F.subquotient m n ≃*
      F.quotientKernelOfLe hmn :=
  (F.subquotientConcreteMulEquiv m n).trans
    ((QuotientGroup.quotientMulEquivOfEq
        (F.levelSubgroupToQuotient_ker_eq hmn).symm).trans
      ((QuotientGroup.quotientKerEquivRange
        (F.levelSubgroupToQuotient hmn)).trans
          (MulEquiv.subgroupCongr
            (F.levelSubgroupToQuotient_range_eq_quotientKernelOfLe hmn))))

/-- States the theorem `coe_subquotientEquivQuotientKernelOfLe_mk`. -/
@[simp] theorem coe_subquotientEquivQuotientKernelOfLe_mk
    {m n : ℕ} (hmn : m ≤ n) (σ : F.lower m) :
    ((F.subquotientEquivQuotientKernelOfLe hmn
        (F.subquotientMk m n σ) :
      F.quotientKernelOfLe hmn) : F.quotient n) =
      F.quotientMk n (σ : G) := by
  simp [subquotientEquivQuotientKernelOfLe]
  rfl

/-- The graded piece `G_n/G_{n+1}` as the kernel of
`G/G_{n+1} → G/G_n`. -/
def gradedPieceEquivQuotientKernel (n : ℕ) :
    F.gradedPiece n ≃*
      F.quotientKernelOfLe (Nat.le_succ n) :=
  (F.gradedPieceEquivSubquotient n).trans
    (F.subquotientEquivQuotientKernelOfLe (Nat.le_succ n))

/-- States the theorem `coe_gradedPieceEquivQuotientKernel_mk`. -/
@[simp] theorem coe_gradedPieceEquivQuotientKernel_mk
    (n : ℕ) (σ : F.lower n) :
    ((F.gradedPieceEquivQuotientKernel n
        (F.gradedPieceMk n σ) :
      F.quotientKernelOfLe (Nat.le_succ n)) : F.quotient (n + 1)) =
      F.quotientMk (n + 1) (σ : G) := by
  exact F.coe_subquotientEquivQuotientKernelOfLe_mk (Nat.le_succ n) σ

/-- At every finite level `N ≥ n + 1`, the `n`th graded piece is the quotient
of finite-level kernels `(G_n/G_N)/(G_{n+1}/G_N)`. -/
def quotientKernelByNextKernelEquivGradedPiece {n N : ℕ} (hN : n + 1 ≤ N) :
    F.quotientKernelOfLe (le_trans (Nat.le_succ n) hN) ⧸
        (F.quotientKernelOfLe hN).subgroupOf
          (F.quotientKernelOfLe (le_trans (Nat.le_succ n) hN)) ≃*
      F.gradedPiece n :=
  (F.quotientKernelQuotientSubgroupOfEquivQuotientKernelOfLe
      (Nat.le_succ n) hN).trans (F.gradedPieceEquivQuotientKernel n).symm

/-- States the theorem `gradedPieceEquivQuotientKernel_quotientKernelByNextKernel_mk'`. -/
theorem gradedPieceEquivQuotientKernel_quotientKernelByNextKernel_mk'
    {n N : ℕ} (hN : n + 1 ≤ N)
    (q : F.quotientKernelOfLe (le_trans (Nat.le_succ n) hN)) :
    F.gradedPieceEquivQuotientKernel n
        (F.quotientKernelByNextKernelEquivGradedPiece hN
          (QuotientGroup.mk'
            ((F.quotientKernelOfLe hN).subgroupOf
              (F.quotientKernelOfLe (le_trans (Nat.le_succ n) hN))) q)) =
      F.quotientKernelMapOfLe (Nat.le_succ n) hN q := by
  simpa [quotientKernelByNextKernelEquivGradedPiece] using
    F.quotientKernelQuotientSubgroupOfEquivQuotientKernelOfLe_mk'
      (Nat.le_succ n) hN q

/-- Cardinality form of the finite-level graded-piece compatibility
`(G_n/G_N)/(G_{n+1}/G_N) ≃ G_n/G_{n+1}`. -/
theorem card_quotientKernelByNextKernel_eq_gradedPiece {n N : ℕ}
    (hN : n + 1 ≤ N) [Finite G] :
    Nat.card
        (F.quotientKernelOfLe (le_trans (Nat.le_succ n) hN) ⧸
          (F.quotientKernelOfLe hN).subgroupOf
            (F.quotientKernelOfLe (le_trans (Nat.le_succ n) hN))) =
      Nat.card (F.gradedPiece n) :=
  Nat.card_congr (F.quotientKernelByNextKernelEquivGradedPiece hN).toEquiv

/-- The natural level-change map `G/G_n → G/G_m` is surjective. -/
theorem quotientMapOfLe_surjective {m n : ℕ} (hmn : m ≤ n) :
    Function.Surjective (F.quotientMapOfLe hmn) := by
  intro q
  refine F.quotient_inductionOn m
    (motive := fun q => ∃ r, F.quotientMapOfLe hmn r = q) q ?_
  intro σ
  exact ⟨F.quotientMk n σ, F.quotientMapOfLe_apply_mk hmn σ⟩

/-- States the theorem `quotientMapOfLe_range_eq_top`. -/
theorem quotientMapOfLe_range_eq_top {m n : ℕ} (hmn : m ≤ n) :
    (F.quotientMapOfLe hmn).range = ⊤ :=
  MonoidHom.range_eq_top.2 (F.quotientMapOfLe_surjective hmn)

/-- The tame quotient `G_0/G_1` as the kernel of `G/G_1 → G/G_0`. -/
def tameQuotientEquivQuotientKernel :
    F.tameQuotient ≃* F.quotientKernelOfLe (Nat.zero_le 1) :=
  F.tameQuotientEquivGradedPiece.trans
    (F.gradedPieceEquivQuotientKernel 0)

/-- States the theorem `coe_tameQuotientEquivQuotientKernel_mk`. -/
@[simp] theorem coe_tameQuotientEquivQuotientKernel_mk
    (σ : F.inertiaSubgroup) :
    ((F.tameQuotientEquivQuotientKernel
        (F.tameQuotientMk σ) :
      F.quotientKernelOfLe (Nat.zero_le 1)) : F.quotient 1) =
      F.quotientMk 1 (σ : G) := by
  exact F.coe_gradedPieceEquivQuotientKernel_mk 0 σ

/-- At every finite level `n ≥ 1`, the tame quotient is the quotient of
finite-level inertia by finite-level wild inertia:
`(G_0/G_n)/(G_1/G_n) ≃ G_0/G_1`. -/
def quotientInertiaByWildKernelEquivTameQuotient {n : ℕ} (hn : 1 ≤ n) :
    F.quotientKernelOfLe (le_trans (Nat.zero_le 1) hn) ⧸
        (F.quotientKernelOfLe hn).subgroupOf
          (F.quotientKernelOfLe (le_trans (Nat.zero_le 1) hn)) ≃*
      F.tameQuotient :=
  (F.quotientKernelQuotientSubgroupOfEquivQuotientKernelOfLe
      (Nat.zero_le 1) hn).trans F.tameQuotientEquivQuotientKernel.symm

/-- States the theorem `tameQuotientEquivQuotientKernel_quotientInertiaByWildKernel_mk'`. -/
theorem tameQuotientEquivQuotientKernel_quotientInertiaByWildKernel_mk'
    {n : ℕ} (hn : 1 ≤ n)
    (q : F.quotientKernelOfLe (le_trans (Nat.zero_le 1) hn)) :
    F.tameQuotientEquivQuotientKernel
        (F.quotientInertiaByWildKernelEquivTameQuotient hn
          (QuotientGroup.mk'
            ((F.quotientKernelOfLe hn).subgroupOf
              (F.quotientKernelOfLe (le_trans (Nat.zero_le 1) hn))) q)) =
      F.quotientKernelMapOfLe (Nat.zero_le 1) hn q := by
  simpa [quotientInertiaByWildKernelEquivTameQuotient] using
    F.quotientKernelQuotientSubgroupOfEquivQuotientKernelOfLe_mk'
      (Nat.zero_le 1) hn q

/-- Cardinality form of the finite-level tame quotient compatibility
`(G_0/G_n)/(G_1/G_n) ≃ G_0/G_1`. -/
theorem card_quotientInertiaByWildKernel_eq_tameQuotient {n : ℕ}
    (hn : 1 ≤ n) [Finite G] :
    Nat.card
        (F.quotientKernelOfLe (le_trans (Nat.zero_le 1) hn) ⧸
          (F.quotientKernelOfLe hn).subgroupOf
            (F.quotientKernelOfLe (le_trans (Nat.zero_le 1) hn))) =
      Nat.card F.tameQuotient :=
  Nat.card_congr (F.quotientInertiaByWildKernelEquivTameQuotient hn).toEquiv

/-- Kernel membership for `G/G_1 → G/G_0`, with a representative already in
the inertia subgroup. -/
theorem mem_tameQuotientKernel_iff_exists_inertia_repr
    (q : F.quotient 1) :
    q ∈ F.quotientKernelOfLe (Nat.zero_le 1) ↔
      ∃ σ : F.inertiaSubgroup,
        F.quotientMk 1 (σ : G) = q := by
  rw [F.mem_quotientKernelOfLe_iff_exists_mem_repr (Nat.zero_le 1)]
  constructor
  · rintro ⟨σ, hσ, hq⟩
    exact ⟨⟨σ, hσ⟩, hq⟩
  · rintro ⟨σ, hσ⟩
    exact ⟨(σ : G), σ.property, hσ⟩

/-- First isomorphism theorem for level-change maps:
`(G/G_n)/(G_m/G_n) ≃ G/G_m`. -/
def quotientQuotientKernelOfLeEquivQuotient {m n : ℕ} (hmn : m ≤ n) :
    F.quotient n ⧸ F.quotientKernelOfLe hmn ≃* F.quotient m :=
  (QuotientGroup.quotientMulEquivOfEq
      (F.quotientMapOfLe_ker_eq_quotientKernelOfLe hmn).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective
      (F.quotientMapOfLe hmn) (F.quotientMapOfLe_surjective hmn))

/-- States the theorem `quotientQuotientKernelOfLeEquivQuotient_mk'`. -/
theorem quotientQuotientKernelOfLeEquivQuotient_mk'
    {m n : ℕ} (hmn : m ≤ n) (q : F.quotient n) :
    F.quotientQuotientKernelOfLeEquivQuotient hmn
        (QuotientGroup.mk' (F.quotientKernelOfLe hmn) q) =
      F.quotientMapOfLe hmn q := by
  exact QuotientGroup.kerLift_mk (F.quotientMapOfLe hmn) q

/-- States the theorem `quotientQuotientKernelOfLeEquivQuotient_mk'_mk'`. -/
theorem quotientQuotientKernelOfLeEquivQuotient_mk'_mk'
    {m n : ℕ} (hmn : m ≤ n) (σ : G) :
    F.quotientQuotientKernelOfLeEquivQuotient hmn
        (QuotientGroup.mk' (F.quotientKernelOfLe hmn)
          (F.quotientMk n σ)) =
      F.quotientMk m σ := by
  rw [F.quotientQuotientKernelOfLeEquivQuotient_mk',
    F.quotientMapOfLe_apply_mk]

/-- The kernel subgroup for the identity level-change map is trivial. -/
theorem quotientKernelOfLe_refl_eq_bot (n : ℕ) :
    F.quotientKernelOfLe (le_rfl : n ≤ n) = ⊥ := by
  rw [← F.quotientMapOfLe_ker_eq_quotientKernelOfLe (le_rfl : n ≤ n),
    F.quotientMapOfLe_refl n]
  simp

end AntitoneNormalSubgroupFiltration

/-- A depth function whose threshold subgroups form a lower ramification filtration. -/
structure LowerRamificationDepth (G : Type u) [Group G] where
  /-- The lower ramification depth of each group element. -/
  depth : G → WithTop ℕ
  /-- The identity has infinite ramification depth. -/
  depth_one : depth 1 = ⊤
  /-- Each depth threshold is closed under multiplication. -/
  depth_mul_mem :
    ∀ {n : ℕ} {σ τ : G},
      (n : WithTop ℕ) ≤ depth σ →
      (n : WithTop ℕ) ≤ depth τ →
      (n : WithTop ℕ) ≤ depth (σ * τ)
  /-- Each depth threshold is closed under inversion. -/
  depth_inv_mem :
    ∀ {n : ℕ} {σ : G},
      (n : WithTop ℕ) ≤ depth σ →
      (n : WithTop ℕ) ≤ depth σ⁻¹
  /-- Each depth threshold is preserved under conjugation. -/
  depth_conj_mem :
    ∀ {n : ℕ} {γ σ : G},
      (n : WithTop ℕ) ≤ depth σ →
      (n : WithTop ℕ) ≤ depth (γ * σ * γ⁻¹)

namespace LowerRamificationDepth

variable {G : Type u} [Group G] (D : LowerRamificationDepth G)

/-- The threshold subgroup cut out by a ramification depth function. -/
def lowerRamificationGroup (n : ℕ) : Subgroup G where
  carrier := {σ | (n : WithTop ℕ) ≤ D.depth σ}
  one_mem' := by
    change (n : WithTop ℕ) ≤ D.depth 1
    rw [D.depth_one]
    exact le_top
  mul_mem' := by
    intro σ τ hσ hτ
    exact D.depth_mul_mem hσ hτ
  inv_mem' := by
    intro σ hσ
    exact D.depth_inv_mem hσ

/-- States the theorem `mem_lowerRamificationGroup_iff`. -/
@[simp] theorem mem_lowerRamificationGroup_iff (n : ℕ) (σ : G) :
    σ ∈ D.lowerRamificationGroup n ↔ (n : WithTop ℕ) ≤ D.depth σ :=
  Iff.rfl

/-- States the theorem `lowerRamificationGroup_normal`. -/
theorem lowerRamificationGroup_normal (n : ℕ) :
    (D.lowerRamificationGroup n).Normal where
  conj_mem := by
    intro σ hσ γ
    exact D.depth_conj_mem (γ := γ) hσ

/-- Provides the instance `lowerRamificationGroup_normal_instance`. -/
instance lowerRamificationGroup_normal_instance (n : ℕ) :
    (D.lowerRamificationGroup n).Normal :=
  D.lowerRamificationGroup_normal n

/-- States the theorem `lowerRamificationGroup_antitone`. -/
theorem lowerRamificationGroup_antitone {m n : ℕ} (hmn : m ≤ n) :
    D.lowerRamificationGroup n ≤ D.lowerRamificationGroup m := by
  intro σ hσ
  change (m : WithTop ℕ) ≤ D.depth σ
  have hmn' : (m : WithTop ℕ) ≤ (n : WithTop ℕ) := by
    exact_mod_cast hmn
  exact le_trans hmn' hσ

/-- States the theorem `mem_lowerRamificationGroup_of_le`. -/
theorem mem_lowerRamificationGroup_of_le {m n : ℕ} (hmn : m ≤ n) {σ : G}
    (hσ : σ ∈ D.lowerRamificationGroup n) :
    σ ∈ D.lowerRamificationGroup m :=
  D.lowerRamificationGroup_antitone hmn hσ

/-- Package a depth function as a lower ramification filtration. -/
def toLowerRamificationFiltration : AntitoneNormalSubgroupFiltration G where
  lower := D.lowerRamificationGroup
  lower_normal := D.lowerRamificationGroup_normal
  antitone := by
    intro m n hmn
    exact D.lowerRamificationGroup_antitone hmn

/-- States the theorem `toLowerRamificationFiltration_apply`. -/
@[simp] theorem toLowerRamificationFiltration_apply (n : ℕ) :
    D.toLowerRamificationFiltration.lower n = D.lowerRamificationGroup n :=
  rfl

/-- Herbrand step attached to a depth-defined lower filtration. -/
noncomputable def herbrandStep (i : Nat) : Rat :=
  D.toLowerRamificationFiltration.herbrandStep i

/-- Natural-index Herbrand function attached to a depth-defined lower
filtration. -/
noncomputable def herbrandFunctionNat (n : Nat) : Rat :=
  D.toLowerRamificationFiltration.herbrandFunctionNat n

/-- States the theorem `herbrandStep_pos`. -/
theorem herbrandStep_pos (i : Nat)
    [Finite (D.lowerRamificationGroup i)]
    [Finite (D.lowerRamificationGroup 0)] :
    0 < D.herbrandStep i := by
  let : Finite (D.toLowerRamificationFiltration.lower i) := by
    simpa [toLowerRamificationFiltration_apply] using
      (inferInstance : Finite (D.lowerRamificationGroup i))
  let : Finite (D.toLowerRamificationFiltration.lower 0) := by
    simpa [toLowerRamificationFiltration_apply] using
      (inferInstance : Finite (D.lowerRamificationGroup 0))
  simpa [herbrandStep, toLowerRamificationFiltration_apply] using
    D.toLowerRamificationFiltration.herbrandStep_pos i

/-- States the theorem `herbrandFunctionNat_mono`. -/
theorem herbrandFunctionNat_mono :
    Monotone D.herbrandFunctionNat := by
  change Monotone D.toLowerRamificationFiltration.herbrandFunctionNat
  exact D.toLowerRamificationFiltration.herbrandFunctionNat_mono

end LowerRamificationDepth

/-- A ramification filtration coming from an action quotient tested against
principal units. -/
structure ValuationActionRamification (G : Type u) [Group G]
    (K : Type v) [Group K] where
  /-- The principal-unit filtration used to test action quotients. -/
  principalUnits : LocalFieldTheory.DiscreteValuationField.AntitoneSubgroupFiltration K
  /-- The action of `G` on `K` by multiplicative automorphisms. -/
  action : G →* MulAut K
  /-- The element of `K` on which action quotients are evaluated. -/
  probe : K
  /-- Membership of action quotients at a fixed level is closed under multiplication. -/
  quotient_mul_mem :
    ∀ {n : ℕ} {σ τ : G},
      ((action σ) probe / probe) ∈ principalUnits.subgroup n →
      ((action τ) probe / probe) ∈ principalUnits.subgroup n →
      ((action (σ * τ)) probe / probe) ∈ principalUnits.subgroup n
  /-- Membership of action quotients at a fixed level is closed under inversion. -/
  quotient_inv_mem :
    ∀ {n : ℕ} {σ : G},
      ((action σ) probe / probe) ∈ principalUnits.subgroup n →
      ((action σ⁻¹) probe / probe) ∈ principalUnits.subgroup n
  /-- Membership of action quotients at a fixed level is preserved under conjugation. -/
  quotient_conj_mem :
    ∀ {n : ℕ} {γ σ : G},
      ((action σ) probe / probe) ∈ principalUnits.subgroup n →
      ((action (γ * σ * γ⁻¹)) probe / probe) ∈ principalUnits.subgroup n

namespace ValuationActionRamification

variable {G : Type u} [Group G] {K : Type v} [Group K]
variable (A : ValuationActionRamification G K)

/-- The action quotient used to test ramification depth. -/
def actionQuotient (σ : G) : K :=
  (A.action σ) A.probe / A.probe

/-- States the theorem `actionQuotient_one`. -/
@[simp] theorem actionQuotient_one :
    A.actionQuotient 1 = 1 := by
  simp [actionQuotient]

/-- Defines `actionDepthAtLeast`. -/
def actionDepthAtLeast (n : ℕ) (σ : G) : Prop :=
  A.actionQuotient σ ∈ A.principalUnits.subgroup n

/-- States the theorem `actionDepthAtLeast_iff`. -/
@[simp] theorem actionDepthAtLeast_iff (n : ℕ) (σ : G) :
    A.actionDepthAtLeast n σ ↔
      A.actionQuotient σ ∈ A.principalUnits.subgroup n :=
  Iff.rfl

/-- States the theorem `actionDepthAtLeast_one`. -/
theorem actionDepthAtLeast_one (n : ℕ) :
    A.actionDepthAtLeast n 1 := by
  rw [A.actionDepthAtLeast_iff, A.actionQuotient_one]
  exact (A.principalUnits.subgroup n).one_mem

/-- States the theorem `actionDepthAtLeast_mul`. -/
theorem actionDepthAtLeast_mul {n : ℕ} {σ τ : G}
    (hσ : A.actionDepthAtLeast n σ) (hτ : A.actionDepthAtLeast n τ) :
    A.actionDepthAtLeast n (σ * τ) :=
  A.quotient_mul_mem hσ hτ

/-- States the theorem `actionDepthAtLeast_inv`. -/
theorem actionDepthAtLeast_inv {n : ℕ} {σ : G}
    (hσ : A.actionDepthAtLeast n σ) :
    A.actionDepthAtLeast n σ⁻¹ :=
  A.quotient_inv_mem hσ

/-- States the theorem `actionDepthAtLeast_conj`. -/
theorem actionDepthAtLeast_conj {n : ℕ} {γ σ : G}
    (hσ : A.actionDepthAtLeast n σ) :
    A.actionDepthAtLeast n (γ * σ * γ⁻¹) :=
  A.quotient_conj_mem hσ

/-- The action-defined lower ramification group. -/
def lowerRamificationGroup (n : ℕ) : Subgroup G where
  carrier := {σ | A.actionDepthAtLeast n σ}
  one_mem' := A.actionDepthAtLeast_one n
  mul_mem' := by
    intro σ τ hσ hτ
    exact A.actionDepthAtLeast_mul hσ hτ
  inv_mem' := by
    intro σ hσ
    exact A.actionDepthAtLeast_inv hσ

/-- States the theorem `mem_lowerRamificationGroup_iff`. -/
@[simp] theorem mem_lowerRamificationGroup_iff (n : ℕ) (σ : G) :
    σ ∈ A.lowerRamificationGroup n ↔ A.actionDepthAtLeast n σ :=
  Iff.rfl

/-- Membership in the action-defined lower ramification group, expanded as a
principal-unit condition on the action quotient. -/
theorem mem_lowerRamificationGroup_iff_actionQuotient (n : ℕ) (σ : G) :
    σ ∈ A.lowerRamificationGroup n ↔
      A.actionQuotient σ ∈ A.principalUnits.subgroup n :=
  (A.mem_lowerRamificationGroup_iff n σ).trans
    (A.actionDepthAtLeast_iff n σ)

/-- States the theorem `lowerRamificationGroup_normal`. -/
theorem lowerRamificationGroup_normal (n : ℕ) :
    (A.lowerRamificationGroup n).Normal where
  conj_mem := by
    intro σ hσ γ
    exact A.actionDepthAtLeast_conj (γ := γ) hσ

/-- Provides the instance `lowerRamificationGroup_normal_instance`. -/
instance lowerRamificationGroup_normal_instance (n : ℕ) :
    (A.lowerRamificationGroup n).Normal :=
  A.lowerRamificationGroup_normal n

/-- States the theorem `lowerRamificationGroup_antitone`. -/
theorem lowerRamificationGroup_antitone {m n : ℕ} (hmn : m ≤ n) :
    A.lowerRamificationGroup n ≤ A.lowerRamificationGroup m := by
  intro σ hσ
  exact A.principalUnits.antitone hmn hσ

/-- Package the action-defined groups as a lower ramification filtration. -/
def toLowerRamificationFiltration : AntitoneNormalSubgroupFiltration G where
  lower := A.lowerRamificationGroup
  lower_normal := A.lowerRamificationGroup_normal
  antitone := by
    intro m n hmn
    exact A.lowerRamificationGroup_antitone hmn

/-- States the theorem `toLowerRamificationFiltration_apply`. -/
@[simp] theorem toLowerRamificationFiltration_apply (n : ℕ) :
    A.toLowerRamificationFiltration.lower n = A.lowerRamificationGroup n :=
  rfl

/-- Herbrand step attached to an action-defined lower filtration. -/
noncomputable def herbrandStep (i : Nat) : Rat :=
  A.toLowerRamificationFiltration.herbrandStep i

/-- Natural-index Herbrand function attached to an action-defined lower
filtration. -/
noncomputable def herbrandFunctionNat (n : Nat) : Rat :=
  A.toLowerRamificationFiltration.herbrandFunctionNat n

/-- States the theorem `herbrandStep_pos`. -/
theorem herbrandStep_pos (i : Nat)
    [Finite (A.lowerRamificationGroup i)]
    [Finite (A.lowerRamificationGroup 0)] :
    0 < A.herbrandStep i := by
  let : Finite (A.toLowerRamificationFiltration.lower i) := by
    simpa [toLowerRamificationFiltration_apply] using
      (inferInstance : Finite (A.lowerRamificationGroup i))
  let : Finite (A.toLowerRamificationFiltration.lower 0) := by
    simpa [toLowerRamificationFiltration_apply] using
      (inferInstance : Finite (A.lowerRamificationGroup 0))
  simpa [herbrandStep, toLowerRamificationFiltration_apply] using
    A.toLowerRamificationFiltration.herbrandStep_pos i

/-- States the theorem `herbrandFunctionNat_mono`. -/
theorem herbrandFunctionNat_mono :
    Monotone A.herbrandFunctionNat := by
  change Monotone A.toLowerRamificationFiltration.herbrandFunctionNat
  exact A.toLowerRamificationFiltration.herbrandFunctionNat_mono

/-- The inertia subgroup `G_0` for an action-defined filtration. -/
abbrev inertiaSubgroup : Subgroup G :=
  A.lowerRamificationGroup 0

/-- States the theorem `lowerRamificationGroup_zero_eq_inertiaSubgroup`. -/
theorem lowerRamificationGroup_zero_eq_inertiaSubgroup :
    A.lowerRamificationGroup 0 = A.inertiaSubgroup :=
  rfl

/-- The wild inertia subgroup `G_1` for an action-defined filtration. -/
abbrev wildInertiaSubgroup : Subgroup G :=
  A.lowerRamificationGroup 1

/-- The tame quotient `G_0/G_1` for an action-defined filtration. -/
def tameQuotient : Type u :=
  A.toLowerRamificationFiltration.tameQuotient

/-- Provides the instance `tameQuotientGroup`. -/
instance tameQuotientGroup : Group A.tameQuotient := by
  change Group A.toLowerRamificationFiltration.tameQuotient
  infer_instance

/-- The action-defined tame quotient is canonically identified with the
underlying lower-filtration model. -/
def tameQuotientEquivLowerFiltration :
    A.tameQuotient ≃*
      A.toLowerRamificationFiltration.tameQuotient :=
  MulEquiv.refl _

/-- Provides the instance `tameQuotientFinite`. -/
instance tameQuotientFinite [Finite G] : Finite A.tameQuotient :=
  Finite.of_equiv A.toLowerRamificationFiltration.tameQuotient
    A.tameQuotientEquivLowerFiltration.symm.toEquiv

/-- Canonical projection to the action-defined tame quotient. -/
def tameQuotientMk : A.inertiaSubgroup →* A.tameQuotient :=
  A.tameQuotientEquivLowerFiltration.symm.toMonoidHom.comp
    A.toLowerRamificationFiltration.tameQuotientMk

/-- States the theorem `tameQuotientEquivLowerFiltration_apply_mk`. -/
@[simp]
theorem tameQuotientEquivLowerFiltration_apply_mk
    (σ : A.inertiaSubgroup) :
    A.tameQuotientEquivLowerFiltration (A.tameQuotientMk σ) =
      A.toLowerRamificationFiltration.tameQuotientMk σ :=
  rfl

/-- States the theorem `tameQuotientMk_surjective`. -/
theorem tameQuotientMk_surjective :
    Function.Surjective A.tameQuotientMk := by
  intro q
  let q' := A.tameQuotientEquivLowerFiltration q
  obtain ⟨σ, hσ⟩ :=
    A.toLowerRamificationFiltration.tameQuotient_inductionOn
      (motive := fun q' => ∃ σ,
        A.toLowerRamificationFiltration.tameQuotientMk σ = q')
      q' (fun σ => ⟨σ, rfl⟩)
  refine ⟨σ, A.tameQuotientEquivLowerFiltration.injective ?_⟩
  exact (A.tameQuotientEquivLowerFiltration_apply_mk
    (show A.inertiaSubgroup from σ)).trans hσ

/-- States the theorem `tameQuotientMk_eq_one_iff`. -/
@[simp]
theorem tameQuotientMk_eq_one_iff (σ : A.inertiaSubgroup) :
    A.tameQuotientMk σ = 1 ↔ (σ : G) ∈ A.wildInertiaSubgroup := by
  constructor
  · intro h
    have h' := congrArg A.tameQuotientEquivLowerFiltration h
    rw [A.tameQuotientEquivLowerFiltration_apply_mk, map_one] at h'
    simpa only [toLowerRamificationFiltration_apply] using
      (A.toLowerRamificationFiltration.tameQuotientMk_eq_one_iff σ).1 h'
  · intro h
    apply A.tameQuotientEquivLowerFiltration.injective
    rw [A.tameQuotientEquivLowerFiltration_apply_mk, map_one]
    apply
      (A.toLowerRamificationFiltration.tameQuotientMk_eq_one_iff σ).2
    simpa only [toLowerRamificationFiltration_apply] using h

/-- States the theorem `tameQuotientMk_eq_iff`. -/
@[simp]
theorem tameQuotientMk_eq_iff (σ τ : A.inertiaSubgroup) :
    A.tameQuotientMk σ = A.tameQuotientMk τ ↔
      ((σ / τ : A.inertiaSubgroup) : G) ∈ A.wildInertiaSubgroup := by
  constructor
  · intro h
    have h' := congrArg A.tameQuotientEquivLowerFiltration h
    rw [A.tameQuotientEquivLowerFiltration_apply_mk,
      A.tameQuotientEquivLowerFiltration_apply_mk] at h'
    change ((σ / τ : A.inertiaSubgroup) : G) ∈
      A.lowerRamificationGroup 1
    exact
      (A.toLowerRamificationFiltration.tameQuotientMk_eq_iff σ τ).1 h'
  · intro h
    apply A.tameQuotientEquivLowerFiltration.injective
    rw [A.tameQuotientEquivLowerFiltration_apply_mk,
      A.tameQuotientEquivLowerFiltration_apply_mk]
    apply
      (A.toLowerRamificationFiltration.tameQuotientMk_eq_iff σ τ).2
    change ((σ / τ : A.inertiaSubgroup) : G) ∈
      A.lowerRamificationGroup 1 at h
    exact h

/-- Eliminate the action-defined tame quotient through inertia
representatives. -/
protected theorem tameQuotient_inductionOn
    {motive : A.tameQuotient → Prop} (q : A.tameQuotient)
    (h : ∀ σ : A.inertiaSubgroup, motive (A.tameQuotientMk σ)) :
    motive q := by
  obtain ⟨σ, rfl⟩ := A.tameQuotientMk_surjective q
  exact h σ

/-- The tame character attached to the chosen action probe.

For valued-extension applications the probe is the chosen uniformizer and the
action quotient is `σ ϖ / ϖ`; at this abstraction level the target is the
tame quotient `G_0/G_1`.  Residue-field unit realizations can be composed on
top once the concrete unit quotient has been constructed. -/
def tameCharacterOfUniformizer : A.inertiaSubgroup →* A.tameQuotient :=
  A.tameQuotientMk

/-- States the theorem `tameCharacterOfUniformizer_apply`. -/
@[simp] theorem tameCharacterOfUniformizer_apply (σ : A.inertiaSubgroup) :
    A.tameCharacterOfUniformizer σ =
      A.tameQuotientMk σ :=
  rfl

/-- The kernel of the action-probe tame character is wild inertia. -/
theorem tameCharacter_ker_eq_wildInertia :
    MonoidHom.ker A.tameCharacterOfUniformizer =
      (A.wildInertiaSubgroup).subgroupOf A.inertiaSubgroup := by
  ext σ
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf,
    A.tameCharacterOfUniformizer_apply, A.tameQuotientMk_eq_one_iff]

/-- States the theorem `mem_inertiaSubgroup_iff_actionDepthAtLeast`. -/
theorem mem_inertiaSubgroup_iff_actionDepthAtLeast (σ : G) :
    σ ∈ A.inertiaSubgroup ↔ A.actionDepthAtLeast 0 σ :=
  A.mem_lowerRamificationGroup_iff 0 σ

/-- States the theorem `mem_wildInertiaSubgroup_iff_actionDepthAtLeast`. -/
theorem mem_wildInertiaSubgroup_iff_actionDepthAtLeast (σ : G) :
    σ ∈ A.wildInertiaSubgroup ↔ A.actionDepthAtLeast 1 σ :=
  A.mem_lowerRamificationGroup_iff 1 σ

/-- Membership in inertia, expanded as a principal-unit condition on the action
quotient. -/
theorem mem_inertiaSubgroup_iff_actionQuotient (σ : G) :
    σ ∈ A.inertiaSubgroup ↔
      A.actionQuotient σ ∈ A.principalUnits.subgroup 0 :=
  A.mem_lowerRamificationGroup_iff_actionQuotient 0 σ

/-- Membership in wild inertia, expanded as a principal-unit condition on the
action quotient. -/
theorem mem_wildInertiaSubgroup_iff_actionQuotient (σ : G) :
    σ ∈ A.wildInertiaSubgroup ↔
      A.actionQuotient σ ∈ A.principalUnits.subgroup 1 :=
  A.mem_lowerRamificationGroup_iff_actionQuotient 1 σ

/-- States the theorem `wildInertiaSubgroup_le_inertiaSubgroup`. -/
theorem wildInertiaSubgroup_le_inertiaSubgroup :
    A.wildInertiaSubgroup ≤ A.inertiaSubgroup :=
  A.lowerRamificationGroup_antitone (Nat.zero_le 1)

/-- Defines `tameQuotientEquivQuotientKernel`. -/
def tameQuotientEquivQuotientKernel :
    A.tameQuotient ≃*
      A.toLowerRamificationFiltration.quotientKernelOfLe (Nat.zero_le 1) :=
  A.tameQuotientEquivLowerFiltration.trans
    A.toLowerRamificationFiltration.tameQuotientEquivQuotientKernel

/-- States the theorem `coe_tameQuotientEquivQuotientKernel_mk`. -/
@[simp] theorem coe_tameQuotientEquivQuotientKernel_mk
    (σ : A.inertiaSubgroup) :
    ((A.tameQuotientEquivQuotientKernel
        (A.tameQuotientMk σ) :
      A.toLowerRamificationFiltration.quotientKernelOfLe (Nat.zero_le 1)) :
      A.toLowerRamificationFiltration.quotient 1) =
      A.toLowerRamificationFiltration.quotientMk 1 (σ : G) := by
  exact
    A.toLowerRamificationFiltration.coe_tameQuotientEquivQuotientKernel_mk σ

/-- At every finite level `n ≥ 1`, the action-defined tame quotient is the
quotient of finite-level inertia by finite-level wild inertia:
`(G_0/G_n)/(G_1/G_n) ≃ G_0/G_1`. -/
def quotientInertiaByWildKernelEquivTameQuotient {n : ℕ} (hn : 1 ≤ n) :
    A.toLowerRamificationFiltration.quotientKernelOfLe
        (le_trans (Nat.zero_le 1) hn) ⧸
        (A.toLowerRamificationFiltration.quotientKernelOfLe hn).subgroupOf
          (A.toLowerRamificationFiltration.quotientKernelOfLe
            (le_trans (Nat.zero_le 1) hn)) ≃*
      A.tameQuotient :=
  (AntitoneNormalSubgroupFiltration.quotientInertiaByWildKernelEquivTameQuotient
    A.toLowerRamificationFiltration hn).trans
      A.tameQuotientEquivLowerFiltration.symm

/-- States the theorem `tameQuotientEquivQuotientKernel_quotientInertiaByWildKernel_mk'`. -/
theorem tameQuotientEquivQuotientKernel_quotientInertiaByWildKernel_mk'
    {n : ℕ} (hn : 1 ≤ n)
    (q :
      A.toLowerRamificationFiltration.quotientKernelOfLe
        (le_trans (Nat.zero_le 1) hn)) :
    A.tameQuotientEquivQuotientKernel
        (A.quotientInertiaByWildKernelEquivTameQuotient hn
          (QuotientGroup.mk'
            ((A.toLowerRamificationFiltration.quotientKernelOfLe hn).subgroupOf
              (A.toLowerRamificationFiltration.quotientKernelOfLe
                (le_trans (Nat.zero_le 1) hn))) q)) =
      A.toLowerRamificationFiltration.quotientKernelMapOfLe
        (Nat.zero_le 1) hn q :=
  AntitoneNormalSubgroupFiltration.tameQuotientEquivQuotientKernel_quotientInertiaByWildKernel_mk'
    A.toLowerRamificationFiltration hn q

/-- Cardinality form of the action-defined finite-level tame quotient
compatibility `(G_0/G_n)/(G_1/G_n) ≃ G_0/G_1`. -/
theorem card_quotientInertiaByWildKernel_eq_tameQuotient {n : ℕ}
    (hn : 1 ≤ n) [Finite G] :
    Nat.card
        (A.toLowerRamificationFiltration.quotientKernelOfLe
            (le_trans (Nat.zero_le 1) hn) ⧸
          (A.toLowerRamificationFiltration.quotientKernelOfLe hn).subgroupOf
            (A.toLowerRamificationFiltration.quotientKernelOfLe
              (le_trans (Nat.zero_le 1) hn))) =
      Nat.card A.tameQuotient := by
  calc
    _ = Nat.card
        A.toLowerRamificationFiltration.tameQuotient :=
      AntitoneNormalSubgroupFiltration.card_quotientInertiaByWildKernel_eq_tameQuotient
        A.toLowerRamificationFiltration hn
    _ = Nat.card A.tameQuotient :=
      Nat.card_congr A.tameQuotientEquivLowerFiltration.symm.toEquiv

/-- Kernel membership for the action-defined map `G/G_1 → G/G_0`, with a
representative already in inertia. -/
theorem mem_tameQuotientKernel_iff_exists_inertia_repr
    (q : A.toLowerRamificationFiltration.quotient 1) :
    q ∈ A.toLowerRamificationFiltration.quotientKernelOfLe (Nat.zero_le 1) ↔
      ∃ σ : A.inertiaSubgroup,
        A.toLowerRamificationFiltration.quotientMk 1 (σ : G) = q := by
  simpa only [toLowerRamificationFiltration_apply] using
    A.toLowerRamificationFiltration.mem_tameQuotientKernel_iff_exists_inertia_repr q

/-- Kernel membership for the action-defined map `G/G_1 → G/G_0`, expanded by
an action-quotient representative in `U^0`. -/
theorem mem_tameQuotientKernel_iff_exists_actionQuotient_mem_repr
    (q : A.toLowerRamificationFiltration.quotient 1) :
    q ∈ A.toLowerRamificationFiltration.quotientKernelOfLe (Nat.zero_le 1) ↔
      ∃ σ : G, A.actionQuotient σ ∈ A.principalUnits.subgroup 0 ∧
        A.toLowerRamificationFiltration.quotientMk 1 σ = q := by
  rw [A.mem_tameQuotientKernel_iff_exists_inertia_repr]
  constructor
  · rintro ⟨σ, hσ⟩
    exact ⟨(σ : G), (A.mem_inertiaSubgroup_iff_actionQuotient (σ : G)).1
      σ.property, hσ⟩
  · rintro ⟨σ, hσ, hq⟩
    exact ⟨⟨σ, (A.mem_inertiaSubgroup_iff_actionQuotient σ).2 hσ⟩, hq⟩

/-- Provides the instance `lowerRamificationGroup_subgroupOf_normal_instance`. -/
instance lowerRamificationGroup_subgroupOf_normal_instance (n : ℕ) :
    ((A.lowerRamificationGroup (n + 1)).subgroupOf
      (A.lowerRamificationGroup n)).Normal := by
  change ((A.toLowerRamificationFiltration.lower (n + 1)).subgroupOf
    (A.toLowerRamificationFiltration.lower n)).Normal
  infer_instance

/-- Representative criterion for the identity class in the action-defined tame
quotient `G_0/G_1`. -/
theorem tameQuotientMk_eq_one_iff_actionDepthAtLeast
    (σ : A.inertiaSubgroup) :
    A.tameQuotientMk σ = 1 ↔
      A.actionDepthAtLeast 1 (σ : G) := by
  exact (A.tameQuotientMk_eq_one_iff σ).trans
    (A.mem_wildInertiaSubgroup_iff_actionDepthAtLeast (σ : G))

/-- Representative criterion for the identity class in the action-defined tame
quotient `G_0/G_1`, expanded as membership of the action quotient in `U^1`. -/
theorem tameQuotientMk_eq_one_iff_actionQuotient_mem
    (σ : A.inertiaSubgroup) :
    A.tameQuotientMk σ = 1 ↔
      A.actionQuotient (σ : G) ∈ A.principalUnits.subgroup 1 :=
  (A.tameQuotientMk_eq_one_iff_actionDepthAtLeast σ).trans
    (A.actionDepthAtLeast_iff 1 (σ : G))

/-- Representative equality criterion in the action-defined tame quotient
`G_0/G_1`, in right-quotient form. -/
theorem tameQuotientMk_eq_iff_actionDepthAtLeast_div
    (σ τ : A.inertiaSubgroup) :
    A.tameQuotientMk σ = A.tameQuotientMk τ ↔
      A.actionDepthAtLeast 1 ((σ / τ : A.inertiaSubgroup) : G) := by
  exact (A.tameQuotientMk_eq_iff σ τ).trans
    (A.mem_wildInertiaSubgroup_iff_actionDepthAtLeast
      ((σ / τ : A.inertiaSubgroup) : G))

/-- Representative equality criterion in the action-defined tame quotient
`G_0/G_1`, in right-quotient form, expanded as membership of the action quotient
in `U^1`. -/
theorem tameQuotientMk_eq_iff_actionQuotient_div_mem
    (σ τ : A.inertiaSubgroup) :
    A.tameQuotientMk σ = A.tameQuotientMk τ ↔
      A.actionQuotient (((σ / τ : A.inertiaSubgroup) : G)) ∈
        A.principalUnits.subgroup 1 :=
  (A.tameQuotientMk_eq_iff_actionDepthAtLeast_div σ τ).trans
    (A.actionDepthAtLeast_iff 1 (((σ / τ : A.inertiaSubgroup) : G)))

/-- Representative equality criterion in the action-defined tame quotient
`G_0/G_1`, in left-quotient form. -/
theorem tameQuotientMk_eq_iff_actionDepthAtLeast_inv_mul
    (σ τ : A.inertiaSubgroup) :
    A.tameQuotientMk σ = A.tameQuotientMk τ ↔
      A.actionDepthAtLeast 1 ((τ⁻¹ * σ : A.inertiaSubgroup) : G) := by
  have hcomm :
      (((σ / τ : A.inertiaSubgroup) : G) ∈ A.wildInertiaSubgroup ↔
        ((τ⁻¹ * σ : A.inertiaSubgroup) : G) ∈ A.wildInertiaSubgroup) := by
    simpa [div_eq_mul_inv, Subgroup.mem_subgroupOf] using
      ((inferInstance :
        ((A.wildInertiaSubgroup).subgroupOf A.inertiaSubgroup).Normal).mem_comm_iff
          (a := σ) (b := τ⁻¹))
  exact (A.tameQuotientMk_eq_iff σ τ).trans
    (hcomm.trans (A.mem_wildInertiaSubgroup_iff_actionDepthAtLeast
      ((τ⁻¹ * σ : A.inertiaSubgroup) : G)))

/-- Representative equality criterion in the action-defined tame quotient
`G_0/G_1`, in left-quotient form, expanded as membership of the action quotient
in `U^1`. -/
theorem tameQuotientMk_eq_iff_actionQuotient_inv_mul_mem
    (σ τ : A.inertiaSubgroup) :
    A.tameQuotientMk σ = A.tameQuotientMk τ ↔
      A.actionQuotient (((τ⁻¹ * σ : A.inertiaSubgroup) : G)) ∈
        A.principalUnits.subgroup 1 :=
  (A.tameQuotientMk_eq_iff_actionDepthAtLeast_inv_mul σ τ).trans
    (A.actionDepthAtLeast_iff 1 (((τ⁻¹ * σ : A.inertiaSubgroup) : G)))

/-- Representative kernel criterion for the action-defined quotient map
`G/G_n → G/G_m`, expressed by the action-depth predicate. -/
theorem quotientMapOfLe_mk_eq_one_iff_actionDepthAtLeast {m n : ℕ}
    (hmn : m ≤ n) (σ : G) :
    A.toLowerRamificationFiltration.quotientMapOfLe hmn
        (A.toLowerRamificationFiltration.quotientMk n σ) = 1 ↔
      A.actionDepthAtLeast m σ := by
  exact
    (A.toLowerRamificationFiltration.quotientMapOfLe_mk_eq_one_iff hmn σ).trans
      (A.mem_lowerRamificationGroup_iff m σ)

/-- Representative kernel criterion for the action-defined quotient map
`G/G_n → G/G_m`, expanded as membership of the action quotient in `U^m`. -/
theorem quotientMapOfLe_mk_eq_one_iff_actionQuotient_mem {m n : ℕ}
    (hmn : m ≤ n) (σ : G) :
    A.toLowerRamificationFiltration.quotientMapOfLe hmn
        (A.toLowerRamificationFiltration.quotientMk n σ) = 1 ↔
      A.actionQuotient σ ∈ A.principalUnits.subgroup m :=
  (A.quotientMapOfLe_mk_eq_one_iff_actionDepthAtLeast hmn σ).trans
    (A.actionDepthAtLeast_iff m σ)

/-- Representative kernel-membership criterion for the action-defined quotient
map `G/G_n → G/G_m`, expanded as membership of the action quotient in `U^m`. -/
theorem quotientMapOfLe_mk_mem_ker_iff_actionQuotient_mem {m n : ℕ}
    (hmn : m ≤ n) (σ : G) :
    A.toLowerRamificationFiltration.quotientMk n σ ∈
        (A.toLowerRamificationFiltration.quotientMapOfLe hmn).ker ↔
      A.actionQuotient σ ∈ A.principalUnits.subgroup m := by
  exact
    (A.toLowerRamificationFiltration.quotientMapOfLe_mk_mem_ker_iff hmn σ).trans
      (A.mem_lowerRamificationGroup_iff_actionQuotient m σ)

/-- Representative equality criterion for the action-defined quotient map
`G/G_n → G/G_m`, in right-quotient form. -/
theorem quotientMapOfLe_mk_eq_iff_actionDepthAtLeast_div {m n : ℕ}
    (hmn : m ≤ n) (σ τ : G) :
    A.toLowerRamificationFiltration.quotientMapOfLe hmn
        (A.toLowerRamificationFiltration.quotientMk n σ) =
      A.toLowerRamificationFiltration.quotientMapOfLe hmn
        (A.toLowerRamificationFiltration.quotientMk n τ) ↔
      A.actionDepthAtLeast m (σ / τ) := by
  exact
    (A.toLowerRamificationFiltration.quotientMapOfLe_mk_eq_iff_div_mem
      hmn σ τ).trans (A.mem_lowerRamificationGroup_iff m (σ / τ))

/-- Representative equality criterion for the action-defined quotient map
`G/G_n → G/G_m`, in right-quotient form, expanded as membership of the action
quotient in `U^m`. -/
theorem quotientMapOfLe_mk_eq_iff_actionQuotient_div_mem {m n : ℕ}
    (hmn : m ≤ n) (σ τ : G) :
    A.toLowerRamificationFiltration.quotientMapOfLe hmn
        (A.toLowerRamificationFiltration.quotientMk n σ) =
      A.toLowerRamificationFiltration.quotientMapOfLe hmn
        (A.toLowerRamificationFiltration.quotientMk n τ) ↔
      A.actionQuotient (σ / τ) ∈ A.principalUnits.subgroup m :=
  (A.quotientMapOfLe_mk_eq_iff_actionDepthAtLeast_div hmn σ τ).trans
    (A.actionDepthAtLeast_iff m (σ / τ))

/-- Representative equality criterion for the action-defined quotient map
`G/G_n → G/G_m`, in left-quotient form. -/
theorem quotientMapOfLe_mk_eq_iff_actionDepthAtLeast_inv_mul {m n : ℕ}
    (hmn : m ≤ n) (σ τ : G) :
    A.toLowerRamificationFiltration.quotientMapOfLe hmn
        (A.toLowerRamificationFiltration.quotientMk n σ) =
      A.toLowerRamificationFiltration.quotientMapOfLe hmn
        (A.toLowerRamificationFiltration.quotientMk n τ) ↔
      A.actionDepthAtLeast m (τ⁻¹ * σ) := by
  simpa [toLowerRamificationFiltration_apply,
    mem_lowerRamificationGroup_iff] using
    A.toLowerRamificationFiltration.quotientMapOfLe_mk_eq_iff_inv_mul_mem
      hmn σ τ

/-- Representative equality criterion for the action-defined quotient map
`G/G_n → G/G_m`, in left-quotient form, expanded as membership of the action
quotient in `U^m`. -/
theorem quotientMapOfLe_mk_eq_iff_actionQuotient_inv_mul_mem {m n : ℕ}
    (hmn : m ≤ n) (σ τ : G) :
    A.toLowerRamificationFiltration.quotientMapOfLe hmn
        (A.toLowerRamificationFiltration.quotientMk n σ) =
      A.toLowerRamificationFiltration.quotientMapOfLe hmn
        (A.toLowerRamificationFiltration.quotientMk n τ) ↔
      A.actionQuotient (τ⁻¹ * σ) ∈ A.principalUnits.subgroup m :=
  (A.quotientMapOfLe_mk_eq_iff_actionDepthAtLeast_inv_mul hmn σ τ).trans
    (A.actionDepthAtLeast_iff m (τ⁻¹ * σ))

/-- Arbitrary-class kernel criterion for the action-defined quotient map
`G/G_n → G/G_m`, expressed by an action quotient representative in `U^m`. -/
theorem quotientMapOfLe_eq_one_iff_exists_actionQuotient_mem_repr
    {m n : ℕ} (hmn : m ≤ n)
    (q : A.toLowerRamificationFiltration.quotient n) :
    A.toLowerRamificationFiltration.quotientMapOfLe hmn q = 1 ↔
      ∃ σ : G, A.actionQuotient σ ∈ A.principalUnits.subgroup m ∧
        A.toLowerRamificationFiltration.quotientMk n σ = q := by
  simpa [toLowerRamificationFiltration_apply,
    mem_lowerRamificationGroup_iff_actionQuotient] using
    A.toLowerRamificationFiltration.quotientMapOfLe_eq_one_iff_exists_mem_repr
      hmn q

/-- Kernel-membership criterion for an arbitrary class in the action-defined
quotient map `G/G_n → G/G_m`, expressed by an action quotient representative
in `U^m`. -/
theorem quotientMapOfLe_mem_ker_iff_exists_actionQuotient_mem_repr
    {m n : ℕ} (hmn : m ≤ n)
    (q : A.toLowerRamificationFiltration.quotient n) :
    q ∈ (A.toLowerRamificationFiltration.quotientMapOfLe hmn).ker ↔
      ∃ σ : G, A.actionQuotient σ ∈ A.principalUnits.subgroup m ∧
        A.toLowerRamificationFiltration.quotientMk n σ = q := by
  simpa [toLowerRamificationFiltration_apply,
    mem_lowerRamificationGroup_iff_actionQuotient] using
    A.toLowerRamificationFiltration.quotientMapOfLe_mem_ker_iff_exists_mem_repr
      hmn q

/-- Membership in the named kernel subgroup of the action-defined quotient map
`G/G_n → G/G_m`, expressed by an action quotient representative in `U^m`. -/
theorem mem_quotientKernelOfLe_iff_exists_actionQuotient_mem_repr
    {m n : ℕ} (hmn : m ≤ n)
    (q : A.toLowerRamificationFiltration.quotient n) :
    q ∈ A.toLowerRamificationFiltration.quotientKernelOfLe hmn ↔
      ∃ σ : G, A.actionQuotient σ ∈ A.principalUnits.subgroup m ∧
        A.toLowerRamificationFiltration.quotientMk n σ = q := by
  simpa [toLowerRamificationFiltration_apply,
    mem_lowerRamificationGroup_iff_actionQuotient] using
    A.toLowerRamificationFiltration.mem_quotientKernelOfLe_iff_exists_mem_repr
      hmn q

/-- First isomorphism theorem inside action-defined ramification kernels:
`(G_l/G_n)/ker(G_l/G_n → G_l/G_m) ≃ G_l/G_m`, for `l ≤ m ≤ n`.
The kernel is identified with `G_m/G_n` by
`AntitoneNormalSubgroupFiltration.quotientKernelMapOfLe_ker_eq`. -/
def quotientKernelQuotientKerEquivQuotientKernelOfLe {l m n : ℕ}
    (hlm : l ≤ m) (hmn : m ≤ n) :
      A.toLowerRamificationFiltration.quotientKernelOfLe
        (le_trans hlm hmn) ⧸
        (A.toLowerRamificationFiltration.quotientKernelMapOfLe hlm hmn).ker ≃*
      A.toLowerRamificationFiltration.quotientKernelOfLe hlm :=
  AntitoneNormalSubgroupFiltration.quotientKernelQuotientKerEquivQuotientKernelOfLe
    A.toLowerRamificationFiltration hlm hmn

/-- States the theorem `quotientKernelQuotientKerEquivQuotientKernelOfLe_mk'`. -/
theorem quotientKernelQuotientKerEquivQuotientKernelOfLe_mk'
    {l m n : ℕ} (hlm : l ≤ m) (hmn : m ≤ n)
    (q :
      A.toLowerRamificationFiltration.quotientKernelOfLe
        (le_trans hlm hmn)) :
    A.quotientKernelQuotientKerEquivQuotientKernelOfLe hlm hmn
        (QuotientGroup.mk'
          (A.toLowerRamificationFiltration.quotientKernelMapOfLe hlm hmn).ker q) =
      A.toLowerRamificationFiltration.quotientKernelMapOfLe hlm hmn q :=
  AntitoneNormalSubgroupFiltration.quotientKernelQuotientKerEquivQuotientKernelOfLe_mk'
    A.toLowerRamificationFiltration hlm hmn q

/-- Second-isomorphism-style form for action-defined ramification kernels:
`(G_l/G_n)/(G_m/G_n) ≃ G_l/G_m`, for `l ≤ m ≤ n`. -/
def quotientKernelQuotientSubgroupOfEquivQuotientKernelOfLe {l m n : ℕ}
    (hlm : l ≤ m) (hmn : m ≤ n) :
      A.toLowerRamificationFiltration.quotientKernelOfLe
        (le_trans hlm hmn) ⧸
        (A.toLowerRamificationFiltration.quotientKernelOfLe hmn).subgroupOf
          (A.toLowerRamificationFiltration.quotientKernelOfLe
            (le_trans hlm hmn)) ≃*
      A.toLowerRamificationFiltration.quotientKernelOfLe hlm :=
  AntitoneNormalSubgroupFiltration.quotientKernelQuotientSubgroupOfEquivQuotientKernelOfLe
    A.toLowerRamificationFiltration hlm hmn

/-- States the theorem `quotientKernelQuotientSubgroupOfEquivQuotientKernelOfLe_mk'`. -/
theorem quotientKernelQuotientSubgroupOfEquivQuotientKernelOfLe_mk'
    {l m n : ℕ} (hlm : l ≤ m) (hmn : m ≤ n)
    (q :
      A.toLowerRamificationFiltration.quotientKernelOfLe
        (le_trans hlm hmn)) :
    A.quotientKernelQuotientSubgroupOfEquivQuotientKernelOfLe hlm hmn
        (QuotientGroup.mk'
          ((A.toLowerRamificationFiltration.quotientKernelOfLe hmn).subgroupOf
            (A.toLowerRamificationFiltration.quotientKernelOfLe
              (le_trans hlm hmn))) q) =
      A.toLowerRamificationFiltration.quotientKernelMapOfLe hlm hmn q :=
  AntitoneNormalSubgroupFiltration.quotientKernelQuotientSubgroupOfEquivQuotientKernelOfLe_mk'
    A.toLowerRamificationFiltration hlm hmn q

/-- Cardinality form of the action-defined second-isomorphism quotient
compatibility `(G_l/G_n)/(G_m/G_n) ≃ G_l/G_m`. -/
theorem card_quotientKernelQuotientSubgroupOfLe {l m n : ℕ}
    (hlm : l ≤ m) (hmn : m ≤ n) [Finite G] :
    Nat.card
        (A.toLowerRamificationFiltration.quotientKernelOfLe
            (le_trans hlm hmn) ⧸
          (A.toLowerRamificationFiltration.quotientKernelOfLe hmn).subgroupOf
            (A.toLowerRamificationFiltration.quotientKernelOfLe
              (le_trans hlm hmn))) =
      Nat.card (A.toLowerRamificationFiltration.quotientKernelOfLe hlm) :=
  AntitoneNormalSubgroupFiltration.card_quotientKernelQuotientSubgroupOfLe
    A.toLowerRamificationFiltration hlm hmn

/-- First isomorphism theorem for action-defined level-change maps:
`(G/G_n)/(G_m/G_n) ≃ G/G_m`. -/
def quotientQuotientKernelOfLeEquivQuotient
    {m n : ℕ} (hmn : m ≤ n) :
    A.toLowerRamificationFiltration.quotient n ⧸
        A.toLowerRamificationFiltration.quotientKernelOfLe hmn ≃*
      A.toLowerRamificationFiltration.quotient m :=
  A.toLowerRamificationFiltration.quotientQuotientKernelOfLeEquivQuotient hmn

/-- States the theorem `quotientQuotientKernelOfLeEquivQuotient_mk'`. -/
theorem quotientQuotientKernelOfLeEquivQuotient_mk'
    {m n : ℕ} (hmn : m ≤ n)
    (q : A.toLowerRamificationFiltration.quotient n) :
    A.quotientQuotientKernelOfLeEquivQuotient hmn
        (QuotientGroup.mk'
          (A.toLowerRamificationFiltration.quotientKernelOfLe hmn) q) =
      A.toLowerRamificationFiltration.quotientMapOfLe hmn q :=
  A.toLowerRamificationFiltration.quotientQuotientKernelOfLeEquivQuotient_mk'
    hmn q

/-- States the theorem `quotientQuotientKernelOfLeEquivQuotient_mk'_mk'`. -/
theorem quotientQuotientKernelOfLeEquivQuotient_mk'_mk'
    {m n : ℕ} (hmn : m ≤ n) (σ : G) :
    A.quotientQuotientKernelOfLeEquivQuotient hmn
        (QuotientGroup.mk'
          (A.toLowerRamificationFiltration.quotientKernelOfLe hmn)
          (A.toLowerRamificationFiltration.quotientMk n σ)) =
      A.toLowerRamificationFiltration.quotientMk m σ :=
  A.toLowerRamificationFiltration.quotientQuotientKernelOfLeEquivQuotient_mk'_mk'
    hmn σ

/-- The action-defined kernel subgroup for the identity level-change map is
trivial. -/
theorem quotientKernelOfLe_refl_eq_bot (n : ℕ) :
    A.toLowerRamificationFiltration.quotientKernelOfLe
      (le_rfl : n ≤ n) = ⊥ :=
  A.toLowerRamificationFiltration.quotientKernelOfLe_refl_eq_bot n

/-- Representative criterion for the image of an action-defined quotient class
to lie in a coarser kernel subgroup, expanded as membership of the action
quotient in `U^l`. -/
theorem quotientMapOfLe_mk_mem_quotientKernelOfLe_iff_actionQuotient_mem
    {l m n : ℕ} (hlm : l ≤ m) (hmn : m ≤ n) (σ : G) :
    A.toLowerRamificationFiltration.quotientMapOfLe hmn
        (A.toLowerRamificationFiltration.quotientMk n σ) ∈
      A.toLowerRamificationFiltration.quotientKernelOfLe hlm ↔
      A.actionQuotient σ ∈ A.principalUnits.subgroup l := by
  simpa [toLowerRamificationFiltration_apply,
    mem_lowerRamificationGroup_iff_actionQuotient] using
    A.toLowerRamificationFiltration.quotientMapOfLe_mk_mem_quotientKernelOfLe_iff
      hlm hmn σ

/-- Arbitrary-class criterion for the image of an action-defined quotient class
to lie in a coarser kernel subgroup, expressed by an action quotient
representative in `U^l`. -/
theorem quotientMapOfLe_mem_quotientKernelOfLe_iff_exists_actionQuotient_mem_repr
    {l m n : ℕ} (hlm : l ≤ m) (hmn : m ≤ n)
    (q : A.toLowerRamificationFiltration.quotient n) :
    A.toLowerRamificationFiltration.quotientMapOfLe hmn q ∈
        A.toLowerRamificationFiltration.quotientKernelOfLe hlm ↔
      ∃ σ : G, A.actionQuotient σ ∈ A.principalUnits.subgroup l ∧
        A.toLowerRamificationFiltration.quotientMk n σ = q := by
  rw [A.toLowerRamificationFiltration.quotientMapOfLe_mem_quotientKernelOfLe_iff
    hlm hmn q]
  exact
    A.mem_quotientKernelOfLe_iff_exists_actionQuotient_mem_repr
      (le_trans hlm hmn) q

/-- Arbitrary-class equality criterion for the action-defined quotient map
`G/G_n → G/G_m`, expressed by an action quotient representative of `q / r` in
`U^m`. -/
theorem quotientMapOfLe_eq_iff_exists_actionQuotient_mem_div_repr
    {m n : ℕ} (hmn : m ≤ n)
    (q r : A.toLowerRamificationFiltration.quotient n) :
    A.toLowerRamificationFiltration.quotientMapOfLe hmn q =
        A.toLowerRamificationFiltration.quotientMapOfLe hmn r ↔
      ∃ σ : G, A.actionQuotient σ ∈ A.principalUnits.subgroup m ∧
        A.toLowerRamificationFiltration.quotientMk n σ = q / r := by
  simpa [toLowerRamificationFiltration_apply,
    mem_lowerRamificationGroup_iff_actionQuotient] using
    A.toLowerRamificationFiltration.quotientMapOfLe_eq_iff_exists_mem_div_repr
      hmn q r

/-- At every finite level `N ≥ n + 1`, the action-defined `n`th graded piece
is the quotient of finite-level kernels `(G_n/G_N)/(G_{n+1}/G_N)`. -/
def quotientKernelByNextKernelEquivGradedPiece {n N : ℕ} (hN : n + 1 ≤ N) :
    A.toLowerRamificationFiltration.quotientKernelOfLe
        (le_trans (Nat.le_succ n) hN) ⧸
        (A.toLowerRamificationFiltration.quotientKernelOfLe hN).subgroupOf
          (A.toLowerRamificationFiltration.quotientKernelOfLe
            (le_trans (Nat.le_succ n) hN)) ≃*
      A.toLowerRamificationFiltration.gradedPiece n :=
  A.toLowerRamificationFiltration.quotientKernelByNextKernelEquivGradedPiece hN

/-- States the theorem `gradedPieceEquivQuotientKernel_quotientKernelByNextKernel_mk'`. -/
theorem gradedPieceEquivQuotientKernel_quotientKernelByNextKernel_mk'
    {n N : ℕ} (hN : n + 1 ≤ N)
    (q :
      A.toLowerRamificationFiltration.quotientKernelOfLe
        (le_trans (Nat.le_succ n) hN)) :
    A.toLowerRamificationFiltration.gradedPieceEquivQuotientKernel n
        (A.quotientKernelByNextKernelEquivGradedPiece hN
          (QuotientGroup.mk'
            ((A.toLowerRamificationFiltration.quotientKernelOfLe hN).subgroupOf
              (A.toLowerRamificationFiltration.quotientKernelOfLe
                (le_trans (Nat.le_succ n) hN))) q)) =
      A.toLowerRamificationFiltration.quotientKernelMapOfLe (Nat.le_succ n) hN q :=
  AntitoneNormalSubgroupFiltration.gradedPieceEquivQuotientKernel_quotientKernelByNextKernel_mk'
    A.toLowerRamificationFiltration hN q

/-- Cardinality form of the action-defined finite-level graded-piece
compatibility `(G_n/G_N)/(G_{n+1}/G_N) ≃ G_n/G_{n+1}`. -/
theorem card_quotientKernelByNextKernel_eq_gradedPiece {n N : ℕ}
    (hN : n + 1 ≤ N) [Finite G] :
    Nat.card
        (A.toLowerRamificationFiltration.quotientKernelOfLe
            (le_trans (Nat.le_succ n) hN) ⧸
          (A.toLowerRamificationFiltration.quotientKernelOfLe hN).subgroupOf
            (A.toLowerRamificationFiltration.quotientKernelOfLe
              (le_trans (Nat.le_succ n) hN))) =
      Nat.card (A.toLowerRamificationFiltration.gradedPiece n) :=
  AntitoneNormalSubgroupFiltration.card_quotientKernelByNextKernel_eq_gradedPiece
    A.toLowerRamificationFiltration hN

/-- Representative criterion for the identity class in the action-defined
graded piece `G_n/G_{n+1}`. -/
theorem gradedPieceMk_eq_one_iff_actionDepthAtLeast
    (n : ℕ) (σ : A.lowerRamificationGroup n) :
    A.toLowerRamificationFiltration.gradedPieceMk n σ = 1 ↔
      A.actionDepthAtLeast (n + 1) (σ : G) := by
  simpa [toLowerRamificationFiltration_apply,
    mem_lowerRamificationGroup_iff] using
    A.toLowerRamificationFiltration.gradedPieceMk_eq_one_iff n σ

/-- Representative criterion for the identity class in the action-defined
graded piece `G_n/G_{n+1}`, expanded as membership of the action quotient in
`U^{n+1}`. -/
theorem gradedPieceMk_eq_one_iff_actionQuotient_mem
    (n : ℕ) (σ : A.lowerRamificationGroup n) :
    A.toLowerRamificationFiltration.gradedPieceMk n σ = 1 ↔
      A.actionQuotient (σ : G) ∈ A.principalUnits.subgroup (n + 1) :=
  (A.gradedPieceMk_eq_one_iff_actionDepthAtLeast n σ).trans
    (A.actionDepthAtLeast_iff (n + 1) (σ : G))

/-- Representative equality criterion in the action-defined graded piece
`G_n/G_{n+1}`, in right-quotient form. -/
theorem gradedPieceMk_eq_iff_actionDepthAtLeast_div
    (n : ℕ) (σ τ : A.lowerRamificationGroup n) :
    A.toLowerRamificationFiltration.gradedPieceMk n σ =
      A.toLowerRamificationFiltration.gradedPieceMk n τ ↔
      A.actionDepthAtLeast (n + 1)
        ((σ / τ : A.lowerRamificationGroup n) : G) := by
  exact
    (A.toLowerRamificationFiltration.gradedPieceMk_eq_iff n σ τ).trans
      (A.mem_lowerRamificationGroup_iff (n + 1)
        ((σ / τ : A.lowerRamificationGroup n) : G))

/-- Representative equality criterion in the action-defined graded piece
`G_n/G_{n+1}`, in right-quotient form, expanded as membership of the action
quotient in `U^{n+1}`. -/
theorem gradedPieceMk_eq_iff_actionQuotient_div_mem
    (n : ℕ) (σ τ : A.lowerRamificationGroup n) :
    A.toLowerRamificationFiltration.gradedPieceMk n σ =
      A.toLowerRamificationFiltration.gradedPieceMk n τ ↔
      A.actionQuotient
          (((σ / τ : A.lowerRamificationGroup n) : G)) ∈
        A.principalUnits.subgroup (n + 1) :=
  (A.gradedPieceMk_eq_iff_actionDepthAtLeast_div n σ τ).trans
    (A.actionDepthAtLeast_iff (n + 1)
      (((σ / τ : A.lowerRamificationGroup n) : G)))

/-- Representative equality criterion in the action-defined graded piece
`G_n/G_{n+1}`, in left-quotient form. -/
theorem gradedPieceMk_eq_iff_actionDepthAtLeast_inv_mul
    (n : ℕ) (σ τ : A.lowerRamificationGroup n) :
    A.toLowerRamificationFiltration.gradedPieceMk n σ =
      A.toLowerRamificationFiltration.gradedPieceMk n τ ↔
      A.actionDepthAtLeast (n + 1)
        ((τ⁻¹ * σ : A.lowerRamificationGroup n) : G) := by
  exact
    (A.toLowerRamificationFiltration.gradedPieceMk_eq_iff_inv_mul_mem
      n σ τ).trans
      (A.mem_lowerRamificationGroup_iff (n + 1)
        ((τ⁻¹ * σ : A.lowerRamificationGroup n) : G))

/-- Representative equality criterion in the action-defined graded piece
`G_n/G_{n+1}`, in left-quotient form, expanded as membership of the action
quotient in `U^{n+1}`. -/
theorem gradedPieceMk_eq_iff_actionQuotient_inv_mul_mem
    (n : ℕ) (σ τ : A.lowerRamificationGroup n) :
    A.toLowerRamificationFiltration.gradedPieceMk n σ =
      A.toLowerRamificationFiltration.gradedPieceMk n τ ↔
      A.actionQuotient
          (((τ⁻¹ * σ : A.lowerRamificationGroup n) : G)) ∈
        A.principalUnits.subgroup (n + 1) :=
  (A.gradedPieceMk_eq_iff_actionDepthAtLeast_inv_mul n σ τ).trans
    (A.actionDepthAtLeast_iff (n + 1)
      (((τ⁻¹ * σ : A.lowerRamificationGroup n) : G)))

end ValuationActionRamification

end DiscreteValuationField

end

end RamificationTheory
