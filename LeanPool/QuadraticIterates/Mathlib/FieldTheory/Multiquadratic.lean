/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
import Mathlib.Algebra.Field.ZMod
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.Perfect
import Mathlib.FieldTheory.Relrank
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

import LeanPool.QuadraticIterates.Mathlib.Algebra.BigOperators
import LeanPool.QuadraticIterates.Mathlib.GroupTheory.PGroup

/-!
# Multiquadratic field extensions

The degree of a multiquadratic extension `L(√c₁, …, √cₘ)/L` over a field of characteristic `≠ 2`
is `2 ^ (m - dim V)`, where `V ≤ 𝔽₂^m` is the space of square relations between the radicands,
realized as the kernel of a linear map to `Lˣ/(Lˣ)²`; descent of squares along such extensions.

Auxiliary material for the formalization of M. Stoll, *Galois groups over ℚ of some iterated
polynomials*, Arch. Math. 59 (1992), 239-244; upstreaming candidates for Mathlib.
-/

/-- Adjoining a single square root `x` (with `x² ∈ L`) to a field `L` gives degree at most `2`. -/
theorem finrank_adjoin_sq_le {L : Type*} [Field L] {E : Type*} [Field E] [Algebra L E]
    {x : E} {c : L} (hc : x ^ 2 = algebraMap L E c) :
    Module.finrank L (IntermediateField.adjoin L {x}) ≤ 2 := by
  have hmonic := Polynomial.monic_X_pow_sub_C c (by norm_num : 2 ≠ 0)
  rw [IntermediateField.adjoin.finrank ⟨_, hmonic, by simp [hc]⟩]
  simpa using Polynomial.natDegree_le_natDegree (minpoly.min L x hmonic (by simp [hc]))

/-- Adjoining a finite set of square roots (each squaring into `L`) gives degree at most
`2 ^ |s|`. -/
theorem finrank_adjoin_finset_sq_le {L : Type*} [Field L] {E : Type*} [Field E] [Algebra L E]
    {s : Finset E} (hs : ∀ x ∈ s, ∃ c : L, x ^ 2 = algebraMap L E c) :
    Module.finrank L (IntermediateField.adjoin L (s : Set E)) ≤ 2 ^ s.card := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.coe_empty, Finset.card_empty, pow_zero,
      IntermediateField.adjoin_empty, IntermediateField.finrank_bot]
  | insert x t hxt ih =>
      have ihb := ih (fun y hy ↦ hs y (Finset.mem_insert_of_mem hy))
      set A := IntermediateField.adjoin L (t : Set E) with hA
      set B := IntermediateField.adjoin L ((insert x t : Finset E) : Set E) with hB
      have hAB : A ≤ B :=
        hA.symm ▸ hB.symm ▸ IntermediateField.adjoin.mono L (t : Set E)
          ((insert x t : Finset E) : Set E)
          (Finset.coe_subset.mpr (Finset.subset_insert x t))
      obtain ⟨c, hc⟩ := hs x (Finset.mem_insert_self x t)
      have hrel : A.relfinrank B ≤ 2 := by
        have hBeq : B = IntermediateField.restrictScalars L
            (IntermediateField.adjoin (↥A) ({x} : Set E)) := by
          rw [hB, Finset.coe_insert, Set.insert_eq, ← Set.union_comm,
            IntermediateField.adjoin_union,
            ← IntermediateField.restrictScalars_adjoin_eq_sup L A ({x} : Set E), hA]
        have hle : A ≤ IntermediateField.restrictScalars L
            (IntermediateField.adjoin (↥A) ({x} : Set E)) :=
          hAB.trans_eq hBeq
        rw [hBeq, IntermediateField.relfinrank_eq_finrank_of_le hle,
          IntermediateField.restrictScalars_injective L
            (IntermediateField.extendScalars_restrictScalars hle)]
        exact finrank_adjoin_sq_le (c := algebraMap L (↥A) c) (by
          rw [hc, IsScalarTower.algebraMap_apply L (↥A) E c])
      calc Module.finrank L B
          = Module.finrank L A * A.relfinrank B :=
            (IntermediateField.finrank_bot_mul_relfinrank hAB).symm
        _ ≤ 2 ^ t.card * 2 := Nat.mul_le_mul ihb hrel
        _ = 2 ^ (insert x t).card := by
              rw [Finset.card_insert_of_notMem hxt, pow_succ]

/-- Relative degree is monotone in the top field: `[B : A] ≤ [C : A]` for `A ≤ B ≤ C` with `C/A`
finite-dimensional. -/
theorem relfinrank_mono {F : Type*} [Field F] {E : Type*} [Field E] [Algebra F E]
    {A B C : IntermediateField F E} (hAB : A ≤ B) (hBC : B ≤ C)
    [FiniteDimensional (↥A) (↥(IntermediateField.extendScalars (le_trans hAB hBC)))] :
    A.relfinrank B ≤ A.relfinrank C := by
  simpa [IntermediateField.relfinrank_eq_finrank_of_le hAB,
    IntermediateField.relfinrank_eq_finrank_of_le (le_trans hAB hBC)] using
    Submodule.finrank_mono (R := ↥A) (M := E)
      (s := (IntermediateField.extendScalars hAB).toSubmodule)
      (t := (IntermediateField.extendScalars (le_trans hAB hBC)).toSubmodule)
      ((IntermediateField.extendScalars_le_extendScalars_iff hAB (le_trans hAB hBC)).mpr hBC)

section

variable {L : Type*} [Field L]

/-- The group `Lˣ/(Lˣ)²` of nonzero square classes of the field `L`, written additively so that
it becomes a `ZMod 2`-module. -/
abbrev SquareClasses (L : Type*) [Field L] : Type _ :=
  Additive (Lˣ ⧸ (powMonoidHom 2 : Lˣ →* Lˣ).range)

instance : Module (ZMod 2) (SquareClasses L) :=
  AddCommGroup.zmodModule (G := SquareClasses L) fun x ↦ by
    apply Additive.toMul.injective
    have hsq : Additive.toMul x ^ 2 = 1 := by
      refine QuotientGroup.induction_on (Additive.toMul x) fun u ↦ ?_
      rw [← QuotientGroup.mk_pow]
      exact (QuotientGroup.eq_one_iff _).mpr ⟨u, rfl⟩
    simpa [two_nsmul, pow_two] using hsq

open Classical in
/-- The class of a nonzero field element in `Lˣ/(Lˣ)²` (junk value `0` at `r = 0`). -/
noncomputable def sqClass (r : L) : SquareClasses L :=
  if hr : r = 0 then 0 else Additive.ofMul (QuotientGroup.mk (Units.mk0 r hr))

/-- The square class of a nonzero `r` vanishes iff `r` is a square in `L`. -/
theorem sqClass_eq_zero_iff {r : L} (hr : r ≠ 0) : sqClass r = 0 ↔ IsSquare r := by
  rw [sqClass, dite_eq_right hr,
    show (0 : SquareClasses L) = Additive.ofMul 1 from rfl,
    Additive.ofMul.apply_eq_iff_eq, QuotientGroup.eq_one_iff]
  constructor
  · rintro ⟨v, hv⟩
    have hcoe := congrArg Units.val hv
    simp only [powMonoidHom_apply, Units.val_pow_eq_pow_val, Units.val_mk0] at hcoe
    exact ⟨(v : L), by rw [← hcoe]; ring⟩
  · rintro ⟨t, ht⟩
    have ht0 : t ≠ 0 := fun h ↦ hr (by rw [ht, h, mul_zero])
    refine ⟨Units.mk0 t ht0, ?_⟩
    ext
    simp [ht, pow_two]

theorem sqClass_mul {r t : L} (hr : r ≠ 0) (ht : t ≠ 0) :
    sqClass (r * t) = sqClass r + sqClass t := by
  rw [sqClass, sqClass, sqClass, dite_eq_right hr, dite_eq_right ht,
    dite_eq_right (mul_ne_zero hr ht), ← ofMul_mul, ← QuotientGroup.mk_mul]
  congr 2
  ext
  simp

theorem sqClass_prod {ι : Type*} {s : Finset ι} {r : ι → L} (hr : ∀ i ∈ s, r i ≠ 0) :
    sqClass (∏ i ∈ s, r i) = ∑ i ∈ s, sqClass (r i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [sqClass]
  | insert a t ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha,
      sqClass_mul (hr a (Finset.mem_insert_self a t))
        (Finset.prod_ne_zero_iff.mpr fun i hi ↦ hr i (Finset.mem_insert_of_mem hi)),
      ih fun i hi ↦ hr i (Finset.mem_insert_of_mem hi)]

@[simp] theorem sqClass_zero : sqClass (0 : L) = 0 := by rw [sqClass, dite_eq_left rfl]

@[simp] theorem sqClass_one : sqClass (1 : L) = 0 :=
  (sqClass_eq_zero_iff one_ne_zero).mpr IsSquare.one

/-- `sqClass` sends a `zpow` to a `ZMod 2`-scalar multiple (the class is written additively). -/
theorem sqClass_zpow {x : L} (hx : x ≠ 0) (k : ℤ) : sqClass (x ^ k) = k • sqClass x := by
  rw [sqClass, sqClass, dite_eq_right (zpow_ne_zero k hx), dite_eq_right hx,
    show Units.mk0 (x ^ k) (zpow_ne_zero k hx) = (Units.mk0 x hx) ^ k from
      Units.ext (by push_cast; simp),
    QuotientGroup.mk_zpow, ofMul_zpow]

/-- A product over `s` is a square iff the classes in `Lˣ/(Lˣ)²` sum to zero. -/
theorem isSquare_prod_iff_sum_sqClass_eq_zero {ι : Type*} {s : Finset ι} {r : ι → L}
    (hr : ∀ i ∈ s, r i ≠ 0) : IsSquare (∏ i ∈ s, r i) ↔ ∑ i ∈ s, sqClass (r i) = 0 := by
  rw [← sqClass_prod hr, sqClass_eq_zero_iff (Finset.prod_ne_zero_iff.mpr hr)]

/-- `sqClass` linearises a product of `zpow`s: `[∏ rᵢ ^ eᵢ] = ∑ eᵢ • [rᵢ]`. -/
theorem sqClass_prod_zpow {ι : Type*} {s : Finset ι} {r : ι → L} (e : ι → ℤ)
    (hr : ∀ i ∈ s, r i ≠ 0) :
    sqClass (∏ i ∈ s, r i ^ e i) = ∑ i ∈ s, e i • sqClass (r i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a t ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha,
      sqClass_mul (zpow_ne_zero _ (hr a (Finset.mem_insert_self a t)))
        (Finset.prod_ne_zero_iff.mpr fun i hi ↦
          zpow_ne_zero _ (hr i (Finset.mem_insert_of_mem hi))),
      sqClass_zpow (hr a (Finset.mem_insert_self a t)),
      ih fun i hi ↦ hr i (Finset.mem_insert_of_mem hi)]

/-- The `𝔽₂`-relation submodule of a finite family of radicands `r : ι → L`: the kernel of
`ε ↦ ∑ ε i • [r i]` in `Lˣ/(Lˣ)²`. For nonzero radicands, `ε` is a relation iff
`∏_{i : ε i = 1} r i` is a square in `L` (see `mem_rootRelations`). -/
noncomputable def rootRelations {ι : Type*} [Fintype ι] (r : ι → L) :
    Submodule (ZMod 2) (ι → ZMod 2) :=
  LinearMap.ker (Fintype.linearCombination (ZMod 2) fun i ↦ sqClass (r i))

/-- `ε` is a root relation iff the product of the `r i` over `{i : ε i = 1}` is a square in
`L`. -/
theorem mem_rootRelations {ι : Type*} [Fintype ι] {r : ι → L} (hr : ∀ i, r i ≠ 0)
    {ε : ι → ZMod 2} :
    ε ∈ rootRelations r ↔ IsSquare (∏ i ∈ Finset.univ.filter (fun i ↦ ε i = 1), r i) := by
  rw [rootRelations, LinearMap.mem_ker, Fintype.linearCombination_apply,
    sum_zmod_two_smul_eq_sum_filter (fun i ↦ sqClass (r i)) ε,
    ← isSquare_prod_iff_sum_sqClass_eq_zero (fun i _ ↦ hr i)]

end

section

variable {L : Type*} [Field L] {E : Type*} [DecidableEq E]

/-- Extension by zero from (the coercion of) a finite set `s`, as a `ZMod 2`-linear map. -/
noncomputable def extendByZeroLM (s : Finset E) :
    (↥(s : Set E) → ZMod 2) →ₗ[ZMod 2] (E → ZMod 2) where
  toFun v x := if h : x ∈ s then v ⟨x, Finset.mem_coe.mpr h⟩ else 0
  map_add' a b := by funext x; by_cases h : x ∈ s <;> simp [h]
  map_smul' t a := by funext x; by_cases h : x ∈ s <;> simp [h]

theorem extendByZeroLM_injective (s : Finset E) :
    Function.Injective (extendByZeroLM (E := E) s) := by
  intro a b hab
  funext x
  simpa [extendByZeroLM, Finset.mem_coe.mp x.2] using congrFun hab x.1

/-- The `𝔽₂`-relation submodule of a multiquadratic extension: the extension by zero of the
relation submodule of the family `c|_s` (see `mem_multiquadraticRelations`). -/
noncomputable def multiquadraticRelations (s : Finset E) (c : E → L) :
    Submodule (ZMod 2) (E → ZMod 2) :=
  Submodule.map (extendByZeroLM s) (rootRelations fun x : ↥(s : Set E) ↦ c x.1)

/-- `ε ∈ multiquadraticRelations s c` iff `ε` is supported on `s` and
`∏_{x ∈ s, ε x = 1} c x` is a square in `L`. -/
theorem mem_multiquadraticRelations {s : Finset E} {c : E → L} (hc : ∀ x ∈ s, c x ≠ 0)
    {ε : E → ZMod 2} :
    ε ∈ multiquadraticRelations s c
      ↔ (∀ x ∉ s, ε x = 0) ∧ IsSquare (∏ x ∈ s.filter (fun x ↦ ε x = 1), c x) := by
  have hprodeq (ε : E → ZMod 2) :
      (∏ x ∈ s.filter (fun x ↦ ε x = 1), c x)
        = ∏ x ∈ Finset.univ.filter (fun x : ↥(s : Set E) ↦ ε x.1 = 1), c x.1 := by
    rw [Finset.prod_filter, Finset.prod_filter,
      ← Finset.prod_attach s (fun x ↦ if ε x = 1 then c x else 1)]
    exact Finset.prod_bij'
      (fun x _ ↦ (⟨x.1, by rw [Finset.mem_coe]; exact x.2⟩ : ↥(s : Set E)))
      (fun x _ ↦ (⟨x.1, by rw [← Finset.mem_coe]; exact x.2⟩ : {x // x ∈ s}))
      (fun x _ ↦ Finset.mem_univ _) (fun x _ ↦ Finset.mem_attach _ _)
      (fun x _ ↦ rfl) (fun x _ ↦ rfl) (fun x _ ↦ rfl)
  have hrne (x : ↥(s : Set E)) : c x.1 ≠ 0 := hc x.1 (Finset.mem_coe.mp x.2)
  constructor
  · rintro ⟨v, hv, rfl⟩
    refine ⟨fun x hx ↦ by simp [extendByZeroLM, hx], ?_⟩
    have hfilter : Finset.univ.filter (fun x : ↥(s : Set E) ↦ extendByZeroLM s v x.1 = 1)
        = Finset.univ.filter (fun x : ↥(s : Set E) ↦ v x = 1) :=
      Finset.filter_congr fun x _ ↦ by simp [extendByZeroLM, Finset.mem_coe.mp x.2]
    rw [hprodeq, hfilter]
    exact (mem_rootRelations hrne).mp hv
  · rintro ⟨hsupp, hsq⟩
    refine ⟨fun x : ↥(s : Set E) ↦ ε x.1, ?_, ?_⟩
    · rw [SetLike.mem_coe, mem_rootRelations hrne]
      rwa [hprodeq ε] at hsq
    · funext x
      by_cases hx : x ∈ s
      · simp [extendByZeroLM, hx]
      · simp [extendByZeroLM, hx, hsupp x hx]

end

/-- Adjoining a square root of `c` gives degree `1` if `c` is already a square in `L`, and `2`
otherwise. -/
theorem finrank_adjoin_sq_eq {L : Type*} [Field L] {E : Type*} [Field E] [Algebra L E]
    {x : E} {c : L} (hc : x ^ 2 = algebraMap L E c) [Decidable (IsSquare c)] :
    Module.finrank L (IntermediateField.adjoin L {x}) = if IsSquare c then 1 else 2 := by
  have hmem_iff : x ∈ (⊥ : IntermediateField L E) ↔ IsSquare c := by
    refine ⟨fun hx ↦ ?_, fun hsq ↦ ?_⟩
    · rw [IntermediateField.mem_bot] at hx
      obtain ⟨y, hy⟩ := hx
      exact ⟨y, (algebraMap L E).injective (by rw [map_mul, hy, ← hc]; ring)⟩
    · obtain ⟨y, hy⟩ := hsq
      have hfac : (x - algebraMap L E y) * (x + algebraMap L E y) = 0 := by
        rw [hy, map_mul] at hc; linear_combination hc
      rw [IntermediateField.mem_bot]
      rcases mul_eq_zero.mp hfac with h1 | h2
      · exact ⟨y, by linear_combination -h1⟩
      · exact ⟨-y, by rw [map_neg]; linear_combination -h2⟩
  have : FiniteDimensional L (IntermediateField.adjoin L {x}) :=
    IntermediateField.adjoin.finiteDimensional ⟨Polynomial.X ^ 2 - Polynomial.C c,
      Polynomial.monic_X_pow_sub_C c (by norm_num), by
        simp [hc]⟩
  have hone_iff : Module.finrank L (IntermediateField.adjoin L {x}) = 1 ↔ IsSquare c := by
    rw [IntermediateField.finrank_adjoin_simple_eq_one_iff, hmem_iff]
  split_ifs with hsq
  · rwa [hone_iff]
  · have hle2 := finrank_adjoin_sq_le hc
    have hpos : 0 < Module.finrank L (IntermediateField.adjoin L {x}) := Module.finrank_pos
    have hne1 := mt hone_iff.mp hsq
    lia

/-- One-step square descent: over `L(x)` with `x² = c` and `x ∉ L`, the image of `d ∈ L` is a
square iff `d` or `d · c` is a square in `L`. -/
theorem square_descent_step {L : Type*} [Field L] [NeZero (2 : L)] {E : Type*} [Field E]
    [Algebra L E] {x : E} {c : L} (hc : x ^ 2 = algebraMap L E c)
    (hx : x ∉ (⊥ : IntermediateField L E)) (d : L) :
    (∃ u v : L, algebraMap L E d = (algebraMap L E u + algebraMap L E v * x) ^ 2)
      ↔ (IsSquare d ∨ IsSquare (d * c)) := by
  have hli (p q : L) (hpq : algebraMap L E p + algebraMap L E q * x = 0) : p = 0 ∧ q = 0 := by
    by_cases hq : q = 0
    · subst hq
      simp only [map_zero, zero_mul, add_zero] at hpq
      exact ⟨(map_eq_zero _).mp hpq, rfl⟩
    · refine absurd ?_ hx
      have hqne : algebraMap L E q ≠ 0 := mt ((map_eq_zero (algebraMap L E)).mp ·) hq
      rw [show x = algebraMap L E (-p / q) by
        simpa [map_div₀, map_neg, eq_div_iff hqne] using (by linear_combination hpq)]
      exact IntermediateField.algebraMap_mem _ _
  constructor
  · rintro ⟨u, v, huv⟩
    have hexp : (algebraMap L E u + algebraMap L E v * x) ^ 2
        = algebraMap L E (u ^ 2 + v ^ 2 * c) + algebraMap L E (2 * u * v) * x := by
      simpa [map_ofNat] using (by linear_combination (algebraMap L E v * algebraMap L E v) * hc)
    rw [hexp] at huv
    obtain ⟨hd, huv0⟩ := hli (d - (u ^ 2 + v ^ 2 * c)) (-(2 * u * v)) (by
      simpa [map_sub, map_neg] using
        (by linear_combination huv : algebraMap L E d
          - algebraMap L E (u ^ 2 + v ^ 2 * c) + (-(algebraMap L E (2 * u * v))) * x = 0))
    have h2uv : (2 : L) * (u * v) = 0 := by linear_combination neg_eq_zero.mp huv0
    have huv_zero : u * v = 0 := (mul_eq_zero.mp h2uv).resolve_left two_ne_zero
    rcases mul_eq_zero.mp huv_zero with hu | hv
    · subst hu; exact Or.inr ⟨v * c, by rw [sub_eq_zero.mp hd]; ring⟩
    · subst hv; exact Or.inl ⟨u, by rw [sub_eq_zero.mp hd]; ring⟩
  · rintro (⟨w, hw⟩ | ⟨w, hw⟩)
    · exact ⟨w, 0, by rw [hw]; push_cast; ring⟩
    · by_cases hc0 : c = 0
      · exfalso
        exact hx ((pow_eq_zero_iff (n := 2) (by norm_num)).mp
          (by rw [hc, hc0, map_zero]) ▸ IntermediateField.zero_mem _)
      · refine ⟨0, w / c, ?_⟩
        have hd_eq : d = (w / c) ^ 2 * c := by field_simp [hc0]; simpa [pow_two] using hw
        rw [hd_eq]; push_cast; rw [zero_add, mul_pow, hc]

/-- For an intermediate field `K` of `E/L` and `e : L`, the image of `e` in `K` is a square
iff some element of `K` squares to the image of `e` in `E`. -/
theorem isSquare_algebraMap_iff {L : Type*} [Field L] {E : Type*} [Field E] [Algebra L E]
    (K : IntermediateField L E) (e : L) :
    IsSquare (algebraMap L ↥K e) ↔ ∃ z ∈ K, z ^ 2 = algebraMap L E e := by
  constructor
  · rintro ⟨w, hw⟩
    refine ⟨(w : E), w.2, ?_⟩
    rw [IsScalarTower.algebraMap_apply L ↥K E, hw, map_mul, IntermediateField.algebraMap_apply]
    ring
  · rintro ⟨z, hz, hz2⟩
    refine ⟨⟨z, hz⟩, ?_⟩
    apply (algebraMap ↥K E).injective
    rw [← IsScalarTower.algebraMap_apply L ↥K E, ← hz2]
    push_cast
    simp [pow_two]

/-- If `w` is a square root of `algebraMap e` lying outside an intermediate field `K`, then `e`
is not a square in `K`. -/
theorem not_isSquare_algebraMap_of_sqrt_notMem {L : Type*} [Field L] {E : Type*} [Field E]
    [Algebra L E] {K : IntermediateField L E} {e : L} {w : E}
    (hw : w ^ 2 = algebraMap L E e) (hwK : w ∉ K) :
    ¬ IsSquare (algebraMap L ↥K e) := by
  rw [isSquare_algebraMap_iff]
  rintro ⟨z, hzK, hz⟩
  have hfac : (w - z) * (w + z) = 0 := by rw [mul_comm, ← sq_sub_sq, hw, hz, sub_self]
  rcases mul_eq_zero.mp hfac with h | h
  · exact hwK ((show w = z by linear_combination h) ▸ hzK)
  · exact hwK ((show w = -z by linear_combination h) ▸ neg_mem hzK)

/-- An element of the base field is a square in the bottom intermediate field iff it is a square
in the base field. -/
theorem isSquare_algebraMap_bot_iff {L : Type*} [Field L] {E : Type*} [Field E] [Algebra L E]
    (x : L) :
    IsSquare (algebraMap L ↥(⊥ : IntermediateField L E) x) ↔ IsSquare x := by
  rw [show algebraMap L ↥(⊥ : IntermediateField L E) x = (IntermediateField.botEquiv L E).symm x
      from (IntermediateField.botEquiv_symm x).symm]
  exact ⟨fun h ↦ by simpa using IsSquare.map (IntermediateField.botEquiv L E) h,
    IsSquare.map (IntermediateField.botEquiv L E).symm⟩

/-- An element of the simple extension `F(y)` with `y² ∈ F` is exactly an `F`-linear combination
`u + v · y`. -/
theorem mem_adjoin_simple_sq {F : Type*} [Field F] {E : Type*} [Field E] [Algebra F E] {y : E}
    {a : F} (hy : y ^ 2 = algebraMap F E a) {z : E} :
    z ∈ IntermediateField.adjoin F {y}
      ↔ ∃ u v : F, z = algebraMap F E u + algebraMap F E v * y := by
  classical
  refine ⟨fun hz ↦ ?_, fun ⟨u, v, hz⟩ ↦ hz ▸ add_mem (IntermediateField.algebraMap_mem _ _)
    (mul_mem (IntermediateField.algebraMap_mem _ _) (IntermediateField.subset_adjoin _ _ rfl))⟩
  set f : Polynomial F := Polynomial.X ^ 2 - Polynomial.C a with hf
  have hfmonic : f.Monic := Polynomial.monic_X_pow_sub_C a (by norm_num)
  have hfaeval : (Polynomial.aeval y) f = 0 := by
    simp only [hf, map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, hy, sub_self]
  have hfdeg : f.natDegree = 2 := by rw [hf]; compute_degree!
  have hspan := Submodule.span_range_natDegree_eq_adjoin hfmonic hfaeval
  rw [hfdeg] at hspan
  have hzsub : z ∈ Subalgebra.toSubmodule (Algebra.adjoin F {y}) :=
    (IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
      (IsIntegral.isAlgebraic ⟨f, hfmonic, hfaeval⟩)) ▸ hz
  rw [← hspan] at hzsub
  have himg : (Finset.image (fun x ↦ y ^ x) (Finset.range 2) : Finset E) = {(1 : E), y} := by
    ext w
    simp only [Finset.mem_image, Finset.mem_range, Finset.mem_insert, Finset.mem_singleton]
    refine ⟨fun ⟨j, _, hj⟩ ↦ by interval_cases j <;> simp_all, fun h ↦ h.elim
      (fun hw ↦ ⟨0, by norm_num, by simp [hw]⟩) fun hw ↦ ⟨1, by norm_num, by simp [hw]⟩⟩
  rw [himg, Finset.coe_insert, Finset.coe_singleton, Submodule.mem_span_pair] at hzsub
  obtain ⟨u, v, huv⟩ := hzsub
  exact ⟨u, v, by rw [← huv]; simp [Algebra.smul_def]⟩

/-- Induction step of `square_descent` when the new radical `y` already lies in `L(s')`: adjoining
`y` changes nothing, so the descent set is unchanged up to `⊆ insert y s'`. -/
private theorem square_descent_insert_of_mem {L : Type*} [Field L] {E : Type*} [Field E]
    [DecidableEq E] [Algebra L E] {s' : Finset E} {y : E} {c : E → L}
    (hs : ∀ z ∈ insert y s', z ^ 2 = algebraMap L E (c z)) (hc : ∀ z ∈ insert y s', c z ≠ 0)
    (hyK : y ∈ IntermediateField.adjoin L (s' : Set E))
    (ih : ∀ e : L, (∃ z ∈ IntermediateField.adjoin L (s' : Set E), z ^ 2 = algebraMap L E e)
        ↔ ∃ t ⊆ s', IsSquare (e * ∏ i ∈ t, c i)) (d : L) :
    (∃ z ∈ IntermediateField.adjoin (↥(IntermediateField.adjoin L (s' : Set E))) ({y} : Set E),
        z ^ 2 = algebraMap L E d)
      ↔ ∃ t ⊆ insert y s', IsSquare (d * ∏ i ∈ t, c i) := by
  set K := IntermediateField.adjoin L (s' : Set E) with hK
  have hmem (z : E) : z ∈ IntermediateField.adjoin (↥K) ({y} : Set E) ↔ z ∈ K := by
    have hadj_eq : SetLike.coe (IntermediateField.adjoin (↥K) ({y} : Set E)) = SetLike.coe K := by
      rw [show IntermediateField.adjoin (↥K) ({y} : Set E) = ⊥ from
          IntermediateField.adjoin_simple_eq_bot_iff.mpr
            (IntermediateField.mem_bot.mpr ⟨⟨y, hyK⟩, rfl⟩),
        IntermediateField.coe_bot, hK,
        IntermediateField.adjoin_eq_range_algebraMap_adjoin L (s' : Set E)]
    simpa [SetLike.mem_coe] using
      (show z ∈ (IntermediateField.adjoin (↥K) ({y} : Set E) : Set E) ↔ z ∈ (K : Set E)
        by rw [hadj_eq])
  have hgenK : ∀ i ∈ insert y s', i ∈ K := by
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi'
    · exact hyK
    · rw [hK]; exact IntermediateField.subset_adjoin L _ hi'
  simp only [hmem]
  refine ⟨fun hz ↦ (ih d).mp hz |>.imp fun t ⟨ht, hsq⟩ ↦
    ⟨ht.trans (Finset.subset_insert y s'), hsq⟩, ?_⟩
  rintro ⟨t, ht, r, hr⟩
  set P : E := ∏ i ∈ t, i with hP
  have hPK : P ∈ K := Subalgebra.prod_mem K.toSubalgebra fun i hi ↦ hgenK i (ht hi)
  have hPsq : algebraMap L E (∏ i ∈ t, c i) = P ^ 2 := by
    rw [map_prod, hP, ← Finset.prod_pow]
    exact Finset.prod_congr rfl fun i hi ↦ (hs i (ht hi)).symm
  have hPne : P ≠ 0 := by
    rw [hP, Finset.prod_ne_zero_iff]
    exact fun i hi hzero ↦ hc i (ht hi)
      ((map_eq_zero (algebraMap L E)).mp (by rw [← hs i (ht hi), hzero]; ring))
  refine ⟨algebraMap L E r / P, div_mem (IntermediateField.algebraMap_mem K r) hPK, ?_⟩
  rw [div_pow, div_eq_iff (pow_ne_zero 2 hPne)]
  rw [← hPsq, ← map_mul, ← map_pow, hr]; ring_nf

/-- Induction step of `square_descent` when the new radical `y` is genuinely new (`y ∉ L(s')`):
one degree-`2` step via `square_descent_step`, tracking whether `y` enters the descent set. -/
private theorem square_descent_insert_of_notMem {L : Type*} [Field L] [NeZero (2 : L)] {E : Type*}
    [Field E] [DecidableEq E] [Algebra L E] {s' : Finset E} {y : E} (hys : y ∉ s') {c : E → L}
    (hy : y ^ 2 = algebraMap L E (c y)) (hyK : y ∉ IntermediateField.adjoin L (s' : Set E))
    (hbridge : ∀ e : L, IsSquare (algebraMap L (↥(IntermediateField.adjoin L (s' : Set E))) e)
        ↔ ∃ t ⊆ s', IsSquare (e * ∏ i ∈ t, c i)) (d : L) :
    (∃ z ∈ IntermediateField.adjoin (↥(IntermediateField.adjoin L (s' : Set E))) ({y} : Set E),
        z ^ 2 = algebraMap L E d)
      ↔ ∃ t ⊆ insert y s', IsSquare (d * ∏ i ∈ t, c i) := by
  set K := IntermediateField.adjoin L (s' : Set E) with hK
  have : NeZero (2 : ↥K) := ⟨by
    rw [← map_ofNat (algebraMap L ↥K) 2]
    exact (map_ne_zero_iff _ (algebraMap L ↥K).injective).mpr two_ne_zero⟩
  have hcyK : y ^ 2 = algebraMap (↥K) E (algebraMap L (↥K) (c y)) := by
    rw [hy, ← IsScalarTower.algebraMap_apply L (↥K) E]
  have hynotbot : y ∉ (⊥ : IntermediateField (↥K) E) := by
    rw [IntermediateField.mem_bot]; rintro ⟨w, hw⟩; exact hyK (hw ▸ w.2)
  have hstep := square_descent_step (L := ↥K) (E := E) hcyK hynotbot (algebraMap L (↥K) d)
  have hLbridge : (∃ u v : ↥K, algebraMap (↥K) E (algebraMap L (↥K) d)
        = (algebraMap (↥K) E u + algebraMap (↥K) E v * y) ^ 2)
      ↔ (∃ z ∈ IntermediateField.adjoin (↥K) ({y} : Set E), z ^ 2 = algebraMap L E d) := by
    rw [← IsScalarTower.algebraMap_apply L (↥K) E]
    simp only [mem_adjoin_simple_sq hcyK]
    exact ⟨fun ⟨u, v, huv⟩ ↦ ⟨_, ⟨u, v, rfl⟩, huv.symm⟩,
      fun ⟨_, ⟨u, v, hz⟩, hz2⟩ ↦ ⟨u, v, (hz ▸ hz2).symm⟩⟩
  rw [← hLbridge, hstep, ← map_mul, hbridge d, hbridge (d * c y)]
  constructor
  · rintro (⟨t, ht, hsq⟩ | ⟨t, ht, hsq⟩)
    · exact ⟨t, ht.trans (Finset.subset_insert y s'), hsq⟩
    · refine ⟨insert y t, Finset.insert_subset_insert y ht, ?_⟩
      rw [Finset.prod_insert fun h ↦ hys (ht h)]; simpa [mul_assoc] using hsq
  · rintro ⟨t, ht, hsq⟩
    by_cases hyt : y ∈ t
    · refine .inr ⟨t.erase y, fun a ha ↦ ?_, ?_⟩
      · rcases Finset.mem_insert.mp (ht (Finset.mem_of_mem_erase ha)) with rfl | h
        · exact absurd (Finset.mem_erase.mp ha).1 (by simp)
        · exact h
      · rw [show ∏ i ∈ t, c i = c y * ∏ i ∈ t.erase y, c i from by
          rw [← Finset.prod_insert (Finset.notMem_erase y t), Finset.insert_erase hyt]] at hsq
        simpa [mul_assoc] using hsq
    · refine .inl ⟨t, fun a ha ↦ ?_, hsq⟩
      rcases Finset.mem_insert.mp (ht ha) with rfl | h
      · exact absurd ha hyt
      · exact h

/-- Iterated square descent: some element of `L(s)` squares to `d` iff `d * ∏_{y ∈ t} c y` is a
square in `L` for some subset `t ⊆ s`. -/
theorem square_descent {L : Type*} [Field L] [NeZero (2 : L)] {E : Type*} [Field E] [Algebra L E]
    {s : Finset E} {c : E → L} (hs : ∀ y ∈ s, y ^ 2 = algebraMap L E (c y))
    (hc : ∀ y ∈ s, c y ≠ 0) (d : L) :
    (∃ z : E, z ∈ IntermediateField.adjoin L (s : Set E) ∧ z ^ 2 = algebraMap L E d)
      ↔ (∃ t : Finset E, t ⊆ s ∧ IsSquare (d * ∏ y ∈ t, c y)) := by
  classical
  revert hs hc d
  induction s using Finset.induction_on with
  | empty =>
    intro hs hc d
    simp only [Finset.coe_empty, IntermediateField.adjoin_empty]
    constructor
    · rintro ⟨z, hz, hz2⟩
      rw [IntermediateField.mem_bot] at hz
      obtain ⟨w, rfl⟩ := hz
      refine ⟨∅, by simp, w, ?_⟩
      apply (algebraMap L E).injective
      rw [Finset.prod_empty, mul_one, ← hz2]; push_cast; ring
    · rintro ⟨t, ht, hsq⟩
      obtain rfl := Finset.subset_empty.mp ht
      simp only [Finset.prod_empty, mul_one] at hsq
      obtain ⟨w, hw⟩ := hsq
      refine ⟨algebraMap L E w, IntermediateField.algebraMap_mem _ _, ?_⟩
      rw [hw]; push_cast; ring
  | insert y s' hys ih =>
    intro hs hc d
    have hy : y ^ 2 = algebraMap L E (c y) := hs y (Finset.mem_insert_self y s')
    have ih' := ih (fun z hz ↦ hs z (Finset.mem_insert_of_mem hz))
      (fun z hz ↦ hc z (Finset.mem_insert_of_mem hz))
    set K := IntermediateField.adjoin L (s' : Set E) with hK
    have hset : (IntermediateField.adjoin L ((insert y s' : Finset E) : Set E) : Set E)
        = (IntermediateField.adjoin (↥K) ({y} : Set E) : Set E) := by
      have h2 : (IntermediateField.adjoin L ((s' : Set E) ∪ ({y} : Set E)) : Set E)
          = (IntermediateField.adjoin (↥K) ({y} : Set E) : Set E) := by
        rw [← IntermediateField.adjoin_adjoin_left L (s' : Set E) ({y} : Set E)]; rfl
      rw [← h2]; congr 1; rw [Finset.coe_insert, Set.insert_eq, Set.union_comm]
    have hmemK (z : E) : z ∈ IntermediateField.adjoin L ((insert y s' : Finset E) : Set E)
        ↔ z ∈ IntermediateField.adjoin (↥K) ({y} : Set E) := by
      rw [← SetLike.mem_coe, hset, SetLike.mem_coe]
    simp only [hmemK]
    by_cases hyK : y ∈ K
    · exact square_descent_insert_of_mem hs hc hyK ih' d
    · have hbridge (e : L) : IsSquare (algebraMap L (↥K) e)
          ↔ ∃ t ⊆ s', IsSquare (e * ∏ y ∈ t, c y) :=
        (isSquare_algebraMap_iff K e).trans (ih' e)
      exact square_descent_insert_of_notMem hys hy hyK hbridge d

/-- The relation space of an `ι`-indexed family has `𝔽₂`-dimension at most `|ι|`. -/
theorem rootRelations_finrank_le {ι : Type*} [Fintype ι] {L : Type*} [Field L] (r : ι → L) :
    Module.finrank (ZMod 2) (rootRelations r) ≤ Fintype.card ι := by
  simpa [Module.finrank_pi] using Submodule.finrank_le (rootRelations r)

/-- `multiquadraticRelations s c` has `𝔽₂`-dimension at most `|s|`. -/
theorem multiquadraticRelations_finrank_le {L : Type*} [Field L] {E : Type*} [DecidableEq E]
    (s : Finset E) (c : E → L) :
    Module.finrank (ZMod 2) (multiquadraticRelations s c) ≤ s.card := by
  have hbr := (Submodule.equivMapOfInjective _ (extendByZeroLM_injective s)
    (rootRelations fun x : ↥(s : Set E) ↦ c x.1)).symm.finrank_eq
  have hcard : Fintype.card ↥(s : Set E) = s.card :=
    (Fintype.card_congr (Equiv.subtypeEquivRight fun x ↦ Finset.mem_coe)).trans
      (Fintype.card_coe s)
  rw [multiquadraticRelations, hbr, ← hcard]
  exact rootRelations_finrank_le (fun x : ↥(s : Set E) ↦ c x.1)

/-- `multiquadraticRelations s c` is finite-dimensional over `𝔽₂`. -/
theorem multiquadraticRelations_finite {L : Type*} [Field L] {E : Type*} [DecidableEq E]
    (s : Finset E) (c : E → L) :
    Module.Finite (ZMod 2) (multiquadraticRelations s c) :=
  Module.Finite.equiv (Submodule.equivMapOfInjective _ (extendByZeroLM_injective s) _)

/-- Intersecting `V (insert y s')` with the hyperplane `ε y = 0` recovers `V s'` (equal
`𝔽₂`-dimension). -/
theorem multiquadraticRelations_ker_finrank {L : Type*} [Field L] {E : Type*}
    [DecidableEq E] {s' : Finset E} {y : E} (hys : y ∉ s') {c : E → L}
    (hc : ∀ x ∈ insert y s', c x ≠ 0) (hc' : ∀ x ∈ s', c x ≠ 0) :
    Module.finrank (ZMod 2)
        (↥((multiquadraticRelations (insert y s') c : Submodule (ZMod 2) (E → ZMod 2))
          ⊓ (LinearMap.ker (LinearMap.proj y : (E → ZMod 2) →ₗ[ZMod 2] ZMod 2)
              : Submodule (ZMod 2) (E → ZMod 2))))
      = Module.finrank (ZMod 2) (multiquadraticRelations s' c) := by
  have heq : ((multiquadraticRelations (insert y s') c : Submodule (ZMod 2) (E → ZMod 2))
        ⊓ (LinearMap.ker (LinearMap.proj y : (E → ZMod 2) →ₗ[ZMod 2] ZMod 2)))
      = multiquadraticRelations s' c := by
    ext ε
    simp only [Submodule.mem_inf, LinearMap.mem_ker, LinearMap.proj_apply,
      mem_multiquadraticRelations hc, mem_multiquadraticRelations hc']
    constructor
    · rintro ⟨⟨hεsupp, hεsq⟩, hεy⟩
      refine ⟨fun x hx ↦ ?_, by simpa [Finset.filter_insert, hεy] using hεsq⟩
      by_cases hxy : x = y
      · rw [hxy]; exact hεy
      · exact hεsupp x (by simp [Finset.mem_insert, hxy, hx])
    · rintro ⟨hεsupp, hεsq⟩
      have hεy : ε y = 0 := hεsupp y hys
      refine ⟨⟨fun x hx ↦ hεsupp x fun hxs ↦ hx (Finset.mem_insert_of_mem hxs), ?_⟩, hεy⟩
      simpa [Finset.filter_insert, hεy] using hεsq
  rw [heq]

/-- Some relation of `V (insert y s')` has `y`-coordinate `1` iff `c y` is a square in
`L(s')`. -/
theorem multiquadraticRelations_ycoord {L : Type*} [Field L] [NeZero (2 : L)] {E : Type*}
    [Field E] [DecidableEq E] [Algebra L E] {s' : Finset E} {y : E} (hys : y ∉ s') {c : E → L}
    (hs : ∀ x ∈ insert y s', x ^ 2 = algebraMap L E (c x)) (hc : ∀ x ∈ insert y s', c x ≠ 0) :
    (∃ ε : E → ZMod 2, ε ∈ multiquadraticRelations (insert y s') c ∧ ε y = 1)
      ↔ IsSquare (algebraMap L (↥(IntermediateField.adjoin L (s' : Set E))) (c y)) := by
  set K := IntermediateField.adjoin L (s' : Set E) with hK
  have hKsq (e : L) : IsSquare (algebraMap L (↥K) e)
      ↔ (∃ z ∈ IntermediateField.adjoin L (s' : Set E), z ^ 2 = algebraMap L E e) :=
    isSquare_algebraMap_iff K e
  have hbridge : IsSquare (algebraMap L (↥K) (c y)) ↔ ∃ t ⊆ s', IsSquare (c y * ∏ x ∈ t, c x) := by
    rw [hKsq (c y), ← hK]
    exact square_descent
      (fun x hx ↦ hs x (Finset.mem_insert_of_mem hx))
      (fun x hx ↦ hc x (Finset.mem_insert_of_mem hx)) (c y)
  rw [hbridge]
  constructor
  · rintro ⟨ε, hεmem, hεy⟩
    obtain ⟨hεsupp, hεsq⟩ := (mem_multiquadraticRelations hc).mp hεmem
    refine ⟨s'.filter (fun x ↦ ε x = 1), Finset.filter_subset _ _, ?_⟩
    simpa [Finset.filter_insert, ite_eq_left hεy,
      Finset.prod_insert (fun h ↦ hys (Finset.mem_of_mem_filter y h))] using hεsq
  · rintro ⟨t, hts, hsq⟩
    have hsub : insert y t ⊆ insert y s' := Finset.insert_subset_insert _ hts
    refine ⟨fun x ↦ if x ∈ insert y t then 1 else 0,
      (mem_multiquadraticRelations hc).mpr ⟨?_, ?_⟩, ?_⟩
    · intro x hx
      by_cases hmem : x ∈ insert y t
      · exact absurd (hsub hmem) hx
      · simp [hmem]
    · have hfe : (insert y s').filter (fun x ↦ (if x ∈ insert y t then (1 : ZMod 2) else 0) = 1)
          = insert y t := by
        ext x; simp only [Finset.mem_filter]
        constructor
        · rintro ⟨hxins, hxval⟩
          by_cases hmem : x ∈ insert y t
          · exact hmem
          · simp [hmem] at hxval
        · intro hxit
          exact ⟨hsub hxit, by simp [hxit]⟩
      rw [hfe, Finset.prod_insert (fun h ↦ hys (hts h))]; exact hsq
    · simp

/-- Adjoining `y` raises `dim V` by `1` when `c y` is a square in `L(s')`, and leaves it
unchanged otherwise. -/
theorem multiquadraticRelations_insert_finrank {L : Type*} [Field L] [NeZero (2 : L)] {E : Type*}
    [Field E] [DecidableEq E] [Algebra L E] {s' : Finset E} {y : E} (hys : y ∉ s') {c : E → L}
    (hs : ∀ x ∈ insert y s', x ^ 2 = algebraMap L E (c x))
    (hc : ∀ x ∈ insert y s', c x ≠ 0) (hc' : ∀ x ∈ s', c x ≠ 0)
    [Decidable (IsSquare (algebraMap L (↥(IntermediateField.adjoin L (s' : Set E))) (c y)))] :
    Module.finrank (ZMod 2) (multiquadraticRelations (insert y s') c)
      = Module.finrank (ZMod 2) (multiquadraticRelations s' c)
        + (if IsSquare (algebraMap L (↥(IntermediateField.adjoin L (s' : Set E))) (c y))
            then 1 else 0) := by
  set K := IntermediateField.adjoin L (s' : Set E)
  set W := multiquadraticRelations (insert y s') c
  set V0 := multiquadraticRelations s' c
  let evy : W →ₗ[ZMod 2] ZMod 2 :=
    { toFun := fun v ↦ (v : E → ZMod 2) y
      map_add' := fun a b ↦ rfl
      map_smul' := fun r a ↦ rfl }
  have : Module.Finite (ZMod 2) W :=
    multiquadraticRelations_finite (insert y s') c
  have hrn := LinearMap.finrank_range_add_finrank_ker evy
  have hkermap : Submodule.map W.subtype (LinearMap.ker evy)
      = (W : Submodule (ZMod 2) (E → ZMod 2))
        ⊓ (LinearMap.ker (LinearMap.proj y : (E → ZMod 2) →ₗ[ZMod 2] ZMod 2)) := by
    ext e
    simp only [Submodule.mem_map, Submodule.mem_inf, LinearMap.mem_ker]
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact ⟨v.2, by simpa [evy] using hv⟩
    · rintro ⟨heW, hey⟩
      exact ⟨⟨e, heW⟩, by simpa [evy] using hey, rfl⟩
  have hker : Module.finrank (ZMod 2) (LinearMap.ker evy) = Module.finrank (ZMod 2) V0 := by
    rw [← Submodule.finrank_map_subtype_eq W (LinearMap.ker evy), hkermap]
    exact multiquadraticRelations_ker_finrank hys hc hc'
  have hyiff : (∃ ε : E → ZMod 2, ε ∈ W ∧ ε y = 1) ↔ IsSquare (algebraMap L (↥K) (c y)) :=
    multiquadraticRelations_ycoord hys hs hc
  have hrange : Module.finrank (ZMod 2) (LinearMap.range evy)
      = (if IsSquare (algebraMap L (↥K) (c y)) then 1 else 0) := by
    by_cases hsq : IsSquare (algebraMap L (↥K) (c y))
    · simp only [hsq, ite_true]
      obtain ⟨ε, hεW, hεy⟩ := hyiff.mpr hsq
      have hrangetop : LinearMap.range evy = ⊤ := by
        rw [LinearMap.range_eq_top]
        intro z
        exact ⟨z • ⟨ε, hεW⟩, by simp [evy, hεy]⟩
      rw [hrangetop, finrank_top]
      simp [Module.finrank_self]
    · simp only [hsq, ite_false]
      have hrangebot : LinearMap.range evy = ⊥ := by
        rw [Submodule.eq_bot_iff]
        intro z hz
        obtain ⟨v, hv⟩ := hz
        by_contra hzne
        refine hsq (hyiff.mp ⟨(v : E → ZMod 2), v.2, ?_⟩)
        have hz1 : z = 1 := by fin_cases z; exacts [absurd rfl hzne, rfl]
        simpa [hz1, evy] using hv
      rw [hrangebot, finrank_bot]
  rw [hrange, hker] at hrn
  split_ifs at hrn ⊢ <;> lia

/-- Degree of a multiquadratic extension: `[L(s) : L] = 2 ^ (|s| - dim V)`, where `V` is the
`𝔽₂`-space of square relations among the radicands. -/
theorem multiquadratic_degree {L : Type*} [Field L] [NeZero (2 : L)] {E : Type*} [Field E]
    [DecidableEq E] [Algebra L E] {s : Finset E} {c : E → L}
    (hs : ∀ x ∈ s, x ^ 2 = algebraMap L E (c x))
    (hc : ∀ x ∈ s, c x ≠ 0) :
    Module.finrank L (IntermediateField.adjoin L (s : Set E))
      = 2 ^ (s.card - Module.finrank (ZMod 2) (multiquadraticRelations s c)) := by
  classical
  revert hs hc
  induction s using Finset.induction_on with
  | empty => intro hs hc; simp
  | insert y s' hys ih =>
    intro hs hc
    have hs' : ∀ x ∈ s', x ^ 2 = algebraMap L E (c x) := fun x hx ↦
      hs x (Finset.mem_insert_of_mem hx)
    have hc' : ∀ x ∈ s', c x ≠ 0 := fun x hx ↦ hc x (Finset.mem_insert_of_mem hx)
    have ih' := ih hs' hc'
    set K := IntermediateField.adjoin L (s' : Set E) with hK
    have hdeg2 : Module.finrank (↥K) (IntermediateField.adjoin (↥K) ({y} : Set E))
        = if IsSquare (algebraMap L (↥K) (c y)) then 1 else 2 :=
      finrank_adjoin_sq_eq
        (by rw [hs y (Finset.mem_insert_self y s'), ← IsScalarTower.algebraMap_apply L (↥K) E])
    have hadjeq : IntermediateField.adjoin L ((insert y s' : Finset E) : Set E)
        = IntermediateField.restrictScalars L (IntermediateField.adjoin (↥K) ({y} : Set E)) := by
      rw [IntermediateField.restrictScalars_adjoin_eq_sup, hK,
        Finset.coe_insert, Set.insert_eq, Set.union_comm, IntermediateField.adjoin_union]
    have hle : K ≤ IntermediateField.restrictScalars L
        (IntermediateField.adjoin (↥K) ({y} : Set E)) := by
      rw [IntermediateField.restrictScalars_adjoin_eq_sup]; exact le_sup_left
    have htower : Module.finrank L (IntermediateField.adjoin L ((insert y s' : Finset E) : Set E))
        = Module.finrank L K
          * Module.finrank (↥K) (IntermediateField.adjoin (↥K) ({y} : Set E)) := by
      rw [hadjeq, ← IntermediateField.finrank_bot_mul_relfinrank hle,
        IntermediateField.relfinrank_eq_finrank_of_le hle]
      congr 1
    have hVincr : Module.finrank (ZMod 2) (multiquadraticRelations (insert y s') c)
        = Module.finrank (ZMod 2) (multiquadraticRelations s' c)
          + (if IsSquare (algebraMap L (↥K) (c y)) then 1 else 0) :=
      multiquadraticRelations_insert_finrank hys hs hc hc'
    have hVle : Module.finrank (ZMod 2) (multiquadraticRelations s' c) ≤ s'.card :=
      multiquadraticRelations_finrank_le s' c
    rw [htower, ih', hdeg2, hVincr, Finset.card_insert_of_notMem hys]
    set d := Module.finrank (ZMod 2) (multiquadraticRelations s' c)
    by_cases hsq : IsSquare (algebraMap L (↥K) (c y))
    · simp only [hsq, ite_true, mul_one]
      congr 1
      lia
    · simp only [hsq, ite_false, add_zero]
      rw [show s'.card + 1 - d = (s'.card - d) + 1 by lia, pow_succ]

/-- If a multiquadratic family `s` generates a field of maximal degree `2 ^ |s|` and `w` is a
new square root whose radicand is not a square in `L(s)`, then adjoining `w` doubles the degree. -/
theorem multiquadratic_degree_insert_of_maximal {L : Type*} [Field L] [NeZero (2 : L)] {E : Type*}
    [Field E] [Algebra L E] {s : Finset E} {w : E} (hws : w ∉ s) {c : E → L}
    (hs : ∀ x ∈ s, x ^ 2 = algebraMap L E (c x)) (hsw : w ^ 2 = algebraMap L E (c w))
    (hc : ∀ x ∈ s, c x ≠ 0) (hcw : c w ≠ 0)
    (hmax : Module.finrank L (IntermediateField.adjoin L (s : Set E)) = 2 ^ s.card)
    (hwnotsq : ¬ IsSquare (algebraMap L (↥(IntermediateField.adjoin L (s : Set E))) (c w))) :
    Module.finrank L (IntermediateField.adjoin L (insert w (s : Set E))) = 2 ^ (s.card + 1) := by
  classical
  have hs' : ∀ x ∈ insert w s, x ^ 2 = algebraMap L E (c x) := fun x hx ↦ by
    rcases Finset.mem_insert.mp hx with rfl | h; exacts [hsw, hs x h]
  have hc' : ∀ x ∈ insert w s, c x ≠ 0 := fun x hx ↦ by
    rcases Finset.mem_insert.mp hx with rfl | h; exacts [hcw, hc x h]
  have hrels0 : Module.finrank (ZMod 2) (multiquadraticRelations s c) = 0 := by
    have hdeg := multiquadratic_degree hs hc
    rw [hmax] at hdeg
    have hle := multiquadraticRelations_finrank_le s c
    have hexp : s.card = s.card - Module.finrank (ZMod 2) (multiquadraticRelations s c) :=
      Nat.pow_right_injective (by norm_num) hdeg
    lia
  have hins_fr : Module.finrank (ZMod 2) (multiquadraticRelations (insert w s) c) = 0 := by
    rw [multiquadraticRelations_insert_finrank hws hs' hc' hc, hrels0, ite_eq_right hwnotsq]
  have hdeg := multiquadratic_degree hs' hc'
  rw [Finset.coe_insert, hins_fr, Finset.card_insert_of_notMem hws] at hdeg
  simpa using hdeg

/-- Family form of `multiquadratic_degree_insert_of_maximal`: a maximal multiquadratic family
`x` of size `n` (square roots of `v`) gains a new square root `w` whose radicand is not a square
in `L(range x)`, doubling the degree. -/
theorem multiquadratic_degree_insert_family {n : ℕ} {L : Type*} [Field L] [NeZero (2 : L)]
    {E : Type*} [Field E] [Algebra L E] {x : Fin n → E} (hxinj : Function.Injective x)
    {v : Fin n → L} (hx : ∀ i, x i ^ 2 = algebraMap L E (v i)) (hv : ∀ i, v i ≠ 0)
    {w : E} (hw : w ∉ Set.range x) {c₀ : L} (hwc : w ^ 2 = algebraMap L E c₀) (hc₀ : c₀ ≠ 0)
    (hmax : Module.finrank L (IntermediateField.adjoin L (Set.range x)) = 2 ^ n)
    (hwnotsq : ¬ IsSquare (algebraMap L (↥(IntermediateField.adjoin L (Set.range x))) c₀)) :
    Module.finrank L (IntermediateField.adjoin L (insert w (Set.range x))) = 2 ^ (n + 1) := by
  classical
  set s : Finset E := Finset.univ.image x with hs
  have hrange : (s : Set E) = Set.range x := by rw [hs]; simp [Finset.coe_image]
  have hscard : s.card = n := by
    rw [hs, Finset.card_image_of_injective _ hxinj, Finset.card_univ, Fintype.card_fin]
  have hws : w ∉ s := by rw [← Finset.mem_coe, hrange]; exact hw
  set cf0 : E → L := Function.extend x v 1
  have hcf0 (i) : cf0 (x i) = v i := hxinj.extend_apply _ _ i
  set cfw : E → L := Function.update cf0 w c₀ with hcfw
  have hxw (i) : x i ≠ w := fun hi ↦ hw ⟨i, hi⟩
  have hcfw_x (i) : cfw (x i) = v i := by rw [hcfw, Function.update_of_ne (hxw i), hcf0 i]
  have hcfw_w : cfw w = c₀ := by rw [hcfw, Function.update_self]
  have hs_sq : ∀ y ∈ s, y ^ 2 = algebraMap L E (cfw y) := by
    intro y hy; obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp (hs ▸ hy); rw [hcfw_x]; exact hx i
  have hs_ne : ∀ y ∈ s, cfw y ≠ 0 := by
    intro y hy; obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp (hs ▸ hy); rw [hcfw_x]; exact hv i
  have hmax' : Module.finrank L (IntermediateField.adjoin L (s : Set E)) = 2 ^ s.card := by
    rw [hrange, hscard]; exact hmax
  have hwnotsq' :
      ¬ IsSquare (algebraMap L (↥(IntermediateField.adjoin L (s : Set E))) (cfw w)) := by
    rw [hrange, hcfw_w]; exact hwnotsq
  have hdeg := multiquadratic_degree_insert_of_maximal hws hs_sq
    (by rw [hcfw_w]; exact hwc) hs_ne (by rw [hcfw_w]; exact hc₀) hmax' hwnotsq'
  rwa [hrange, hscard] at hdeg

/-- The dimension of the relation space is invariant under reindexing the family by a
bijection. -/
theorem rootRelations_finrank_reindex {ι : Type*} [Fintype ι] {κ : Type*} [Fintype κ]
    {L : Type*} [Field L] (r : ι → L) (hr : ∀ i, r i ≠ 0) {r' : κ → L} (hr' : ∀ j, r' j ≠ 0)
    (e : ι ≃ κ) (he : ∀ i, r' (e i) = r i) :
    Module.finrank (ZMod 2) (rootRelations r) = Module.finrank (ZMod 2) (rootRelations r') := by
  classical
  set φ := LinearEquiv.piCongrLeft' (ZMod 2) (fun _ : ι ↦ ZMod 2) e
  have hprod (ε : ι → ZMod 2) : (∏ k ∈ Finset.univ.filter
      (fun k ↦ (φ ε) k = 1), r' k) = ∏ i ∈ Finset.univ.filter (fun i ↦ ε i = 1), r i := by
    refine Finset.prod_equiv e.symm (fun k ↦ ?_) (fun k _ ↦ ?_)
    · simp [Finset.mem_filter, φ, LinearEquiv.piCongrLeft'_apply]
    · rw [← he (e.symm k), Equiv.apply_symm_apply e k]
  have hmap : Submodule.map (φ : (ι → ZMod 2) →ₗ[ZMod 2] (κ → ZMod 2)) (rootRelations r)
      = rootRelations r' := by
    ext η
    simp only [Submodule.mem_map]
    constructor
    · rintro ⟨ε, hε, rfl⟩
      rw [mem_rootRelations hr']
      rw [mem_rootRelations hr] at hε
      simp only [LinearEquiv.coe_coe]
      rwa [hprod ε]
    · intro hη
      refine ⟨φ.symm η, ?_, by simp⟩
      rw [mem_rootRelations hr, ← hprod (φ.symm η)]
      rw [mem_rootRelations hr'] at hη
      simpa using hη
  rw [← hmap, LinearEquiv.finrank_map_eq]

/-- `multiquadraticRelations s c` has the same `𝔽₂`-dimension as the relation space of the
restricted family `c|_s`. -/
theorem multiquadraticRelations_finrank_eq_rootRelations {L : Type*} [Field L] {E : Type*}
    [DecidableEq E] (s : Finset E) (c : E → L) :
    Module.finrank (ZMod 2) (multiquadraticRelations s c)
      = Module.finrank (ZMod 2) (rootRelations fun x : ↥(s : Set E) ↦ c x.1) :=
  (Submodule.equivMapOfInjective _ (extendByZeroLM_injective s) _).symm.finrank_eq

/-- Family form of `multiquadratic_degree`: for an injective family `x : ι → E` of square roots
of nonzero radicands `r : ι → L`, the degree of `L(x i : i)` over `L` is
`2 ^ (|ι| - dim rootRelations r)`. -/
theorem multiquadratic_degree_family {ι : Type*} [Fintype ι] {L : Type*} [Field L] [NeZero (2 : L)]
    {E : Type*} [Field E] [Algebra L E] {x : ι → E} (hxinj : Function.Injective x)
    {r : ι → L} (hx : ∀ i, x i ^ 2 = algebraMap L E (r i)) (hr : ∀ i, r i ≠ 0) :
    Module.finrank L (IntermediateField.adjoin L (Set.range x))
      = 2 ^ (Fintype.card ι - Module.finrank (ZMod 2) (rootRelations r)) := by
  classical
  set s : Finset E := Finset.univ.image x with hs
  have hrange : (s : Set E) = Set.range x := by rw [hs]; simp [Finset.coe_image]
  have hscard : s.card = Fintype.card ι := by
    rw [hs, Finset.card_image_of_injective _ hxinj, Finset.card_univ]
  set cf : E → L := Function.extend x r 1 with hcf
  have hcf_x (i) : cf (x i) = r i := hxinj.extend_apply _ _ i
  have hs_sq : ∀ y ∈ s, y ^ 2 = algebraMap L E (cf y) := by
    intro y hy; obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp (hs ▸ hy); rw [hcf_x]; exact hx i
  have hs_ne : ∀ y ∈ s, cf y ≠ 0 := by
    intro y hy; obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp (hs ▸ hy); rw [hcf_x]; exact hr i
  set e : ↥(s : Set E) ≃ ι :=
    (Equiv.setCongr hrange).trans (Equiv.ofInjective x hxinj).symm with he
  have hxe (y : ↥(s : Set E)) : x (e y) = (y : E) :=
    congrArg Subtype.val ((Equiv.ofInjective x hxinj).apply_symm_apply (Equiv.setCongr hrange y))
  have hdim : Module.finrank (ZMod 2) (multiquadraticRelations s cf)
      = Module.finrank (ZMod 2) (rootRelations r) :=
    (multiquadraticRelations_finrank_eq_rootRelations s cf).trans
      (rootRelations_finrank_reindex (fun y : ↥(s : Set E) ↦ cf y.1)
        (fun y ↦ hs_ne y.1 (Finset.mem_coe.mp y.2)) hr e
        fun y ↦ by rw [← hcf_x (e y), hxe y])
  rw [← hrange, multiquadratic_degree hs_sq hs_ne, hscard, hdim]

/-- If every `g ∈ G` acts on the radicands through a field automorphism, the relation space is
invariant under the coordinate action. -/
theorem rootRelations_invariant {G : Type*} [Group G] {ι : Type*} [Fintype ι] [MulAction G ι]
    {L : Type*} [Field L] {r : ι → L} (hr : ∀ i, r i ≠ 0)
    (hcompat : ∀ g : G, ∃ φ : L ≃+* L, ∀ j, φ (r j) = r (g • j)) :
    ∀ (g : G) (v : ι → ZMod 2), v ∈ rootRelations r → (fun i ↦ v (g⁻¹ • i)) ∈ rootRelations r := by
  classical
  intro g v hv
  rw [mem_rootRelations hr] at hv ⊢
  obtain ⟨φ, hφ⟩ := hcompat g
  rw [show (∏ i ∈ Finset.univ.filter (fun i ↦ v (g⁻¹ • i) = 1), r i)
      = ∏ j ∈ Finset.univ.filter (fun j ↦ v j = 1), r (g • j) from by
    apply Finset.prod_nbij' (fun i ↦ g⁻¹ • i) (fun j ↦ g • j) <;>
      simp [inv_smul_smul, smul_inv_smul],
    Finset.prod_congr rfl (fun j _ ↦ (hφ j).symm), ← map_prod]
  exact IsSquare.map φ hv

/-- For a finite `2`-group acting pretransitively with automorphism-compatible radicands, a
nonzero relation space contains the all-ones vector. -/
theorem rootRelations_all_ones {G : Type*} [Group G] [Finite G] (hG : IsPGroup 2 G)
    {ι : Type*} [Fintype ι] [Nonempty ι] [MulAction G ι] [MulAction.IsPretransitive G ι]
    {L : Type*} [Field L] {r : ι → L} (hr : ∀ i, r i ≠ 0)
    (hcompat : ∀ g : G, ∃ φ : L ≃+* L, ∀ j, φ (r j) = r (g • j)) (hne : rootRelations r ≠ ⊥) :
    (fun _ ↦ 1) ∈ rootRelations r :=
invariant_submodule_all_ones hG (rootRelations r) (rootRelations_invariant hr hcompat) hne

/-- The all-ones vector is a relation iff `∏ i, r i` is a square in `L`. -/
theorem all_ones_mem_rootRelations {ι : Type*} [Fintype ι] {L : Type*} [Field L]
    {r : ι → L} (hr : ∀ i, r i ≠ 0) :
    (fun _ ↦ (1 : ZMod 2)) ∈ rootRelations r ↔ IsSquare (∏ i, r i) := by
  classical
  rw [mem_rootRelations hr, Finset.filter_true_of_mem (fun i _ ↦ rfl)]

section AdjoinSquareRoots

variable {F E : Type*} [Field F] [Field E] [Algebra F E]

/-- An `F`-automorphism fixes or negates any square root of an element of `F`. -/
lemma apply_eq_or_eq_neg_of_sq_eq_algebraMap (φ : E ≃ₐ[F] E) {y : E} {q : F}
    (hy : y ^ 2 = algebraMap F E q) : φ y = y ∨ φ y = -y :=
  sq_eq_sq_iff_eq_or_eq_neg.mp (by rw [← map_pow, hy, AlgEquiv.commutes])

/-- Such a subfield has exponent `2`: every `F`-automorphism of it is an involution. -/
lemma algEquiv_adjoin_sq_eq_one {t : Finset E}
    (ht : ∀ y ∈ t, ∃ q : F, y ^ 2 = algebraMap F E q)
    (τ : ↥(IntermediateField.adjoin F (t : Set E)) ≃ₐ[F]
          ↥(IntermediateField.adjoin F (t : Set E))) :
    τ ^ 2 = 1 := by
  have hgen (x : E) (hx : x ∈ (t : Set E)) :
      (τ ^ 2) ⟨x, IntermediateField.subset_adjoin F _ hx⟩
        = ⟨x, IntermediateField.subset_adjoin F _ hx⟩ := by
    obtain ⟨q, hq⟩ := ht x hx
    set g : ↥(IntermediateField.adjoin F (t : Set E)) :=
      ⟨x, IntermediateField.subset_adjoin F _ hx⟩ with hg
    have hgq : g ^ 2 = algebraMap F ↥(IntermediateField.adjoin F (t : Set E)) q := by
      apply Subtype.ext
      push_cast
      simpa [hg] using hq
    rcases apply_eq_or_eq_neg_of_sq_eq_algebraMap τ hgq with h | h
    · rw [pow_two, AlgEquiv.mul_apply, h, h]
    · rw [pow_two, AlgEquiv.mul_apply, h, map_neg, h, neg_neg]
  have key : (τ ^ 2).toAlgHom = AlgHom.id F _ := IntermediateField.adjoin_algHom_ext F hgen
  ext z
  simpa using DFunLike.congr_fun key z
variable [Normal F E]

/-- A subfield of `E` generated by square roots of elements of `F` is Galois over `F`. -/
lemma isGalois_adjoin_of_sq_eq_algebraMap [PerfectField F] {t : Finset E}
    (ht : ∀ y ∈ t, ∃ q : F, y ^ 2 = algebraMap F E q) :
    IsGalois F ↥(IntermediateField.adjoin F (t : Set E)) := by
  set K := IntermediateField.adjoin F (t : Set E) with hK
  have hmaple (σ : E ≃ₐ[F] E) : IntermediateField.map (σ : E →ₐ[F] E) K ≤ K := by
    rw [hK, IntermediateField.adjoin_map, IntermediateField.adjoin_le_iff]
    rintro x ⟨y, hyt, rfl⟩
    obtain ⟨q, hq⟩ := ht y hyt
    have hy_mem := IntermediateField.subset_adjoin F (t : Set E) hyt
    rcases apply_eq_or_eq_neg_of_sq_eq_algebraMap σ hq with h | h
    · simpa [h] using hy_mem
    · simpa [h] using neg_mem hy_mem
  have : Normal F ↥K := IntermediateField.normal_iff_forall_map_le'.mpr hmaple
  have := Algebra.IsAlgebraic.isSeparable_of_perfectField (K := F) (L := ↥K)
  exact IsGalois.mk

end AdjoinSquareRoots
