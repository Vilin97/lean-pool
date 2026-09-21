/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanPool.UniformSheafyTateDomains.AdicSpaces.ValuationContinuity

/-!
# Lemma 7.45: Non-open primes are supports in Spa

Given a complete affinoid ring `(A, A⁺)` with pair of definition `(A₀, I)` and
a non-open prime `𝔭` of `A`, there exists `v ∈ Spa(A, A⁺)` with `supp(v) ⊇ 𝔭`.

This file contains the proof assembly using the infrastructure from
`ValuationContinuity.lean` (continuity criteria, domination, coarsening,
`restrictToConvex`, and the v_ext extension construction).

## Main results

* `PairOfDefinition.exists_spa_point_via_restrictToConvex`: The full construction.
* `PairOfDefinition.exists_mem_spa_supp_ge_of_nonOpen_prime`: Wedhorn Lemma 7.45.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn2019adic], Lemma 7.45, Lemma 7.44
-/

/-! ### Section 7: Lemma 7.45 -- full proof

## Proof strategy (Wedhorn)

Following Wedhorn's Lemma 7.45:
1. Get `V₀` from the domination theorem with `range(A₀) ≤ V₀` and I-images
   landing in `V₀.nonunits`.
2. Apply the retraction `r` from (7.1.2): `restrictToConvex` with
   `H = convexGenerated(u₀⁻¹)` where `u₀` is a specific I-generator value.
3. Extend from `A₀` to `A` using topological nilpotency (Lemma 7.44(3)).
4. The extended valuation has `supp = 𝔭` and is continuous with a value group
   that is automatically MulArchimedean (rank ≤ 1).

The extension `v_ext(a) = v_r(s^n * a) * v_r(s)^{-n}` (where `s ∈ I \ 𝔭` is
topologically nilpotent and `n` is chosen so `s^n * a ∈ A₀`) requires proving
well-definedness, multiplicativity, the ultrametric inequality, and support = 𝔭.
-/

namespace PairOfDefinition

open ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A]
  [IsTopologicalRing A]

/-! ### Helper (a): Topological nilpotency gives `s^n * a ∈ A₀`

If `s` is topologically nilpotent in `A` and `A₀` is open, then for any `a : A`,
there exists `n` such that `s ^ n * a ∈ A₀`. This is Wedhorn's Lemma 7.44(1)
applied to the extension construction. -/

/-- For `s` topologically nilpotent and `A₀` open in `A`, there exists `n`
with `s ^ n * a ∈ A₀` (used in the extension construction, Wedhorn Lemma 7.44). -/
theorem exists_pow_mul_mem_A₀ (P : PairOfDefinition A) {s : A}
    (hs : IsTopologicallyNilpotent s) (a : A) : ∃ n : ℕ, s ^ n * a ∈ P.A₀ := by
  have h_cont : Continuous (· * a : A → A) := continuous_mul_const a
  have h_open : IsOpen {x : A | x * a ∈ P.A₀} :=
    P.isOpen.preimage h_cont
  have h_zero : (0 : A) ∈ {x : A | x * a ∈ P.A₀} := by
    simp only [Set.mem_setOf_eq, zero_mul, P.A₀.zero_mem]
  have h_nhds : {x : A | x * a ∈ P.A₀} ∈ nhds (0 : A) :=
    h_open.mem_nhds h_zero
  obtain ⟨n, hn⟩ := (hs.eventually h_nhds).exists
  exact ⟨n, hn⟩

omit [IsTopologicalRing A] in
/-- Monotonicity: if `s ^ n * a ∈ A₀` then `s ^ (n + k) * a ∈ A₀` for all `k`.
This follows because `s ^ (n + k) * a = s ^ k * (s ^ n * a)` and `A₀` is a subring. -/
theorem pow_mul_mem_A₀_of_le (P : PairOfDefinition A) {s : A} (hs : s ∈ P.A₀) {a : A}
    {n : ℕ} (hn : s ^ n * a ∈ P.A₀) (k : ℕ) : s ^ (n + k) * a ∈ P.A₀ := by
  rw [show n + k = k + n from by omega, pow_add, mul_assoc]
  exact P.A₀.mul_mem (P.A₀.pow_mem hs k) hn

/-! ### Helper (b)-(c): Extended valuation construction

The extension `v_ext : A → WithZero(H_gen.toSubgroup)` is defined by choosing
`n` such that `s^n * a ∈ A₀` and setting `v_ext(a) = v_r(s^n * a) * v_r(s)^{-n}`.

This requires proving:
- Well-definedness (independence of choice of `n`)
- Multiplicativity
- Ultrametric inequality
- v_ext(0) = 0, v_ext(1) = 1

These are proved in `vExt_well_defined` and the extracted helpers
`vExtFun_step`, `vExtFun_well_defined`, `vExtFun_map_mul`,
`vExtFun_map_add_le_max`. -/

omit [IsTopologicalRing A] in
/-- **Well-definedness of the extended valuation.** If `s ^ n * a ∈ A₀` and
`s ^ m * a ∈ A₀`, then the two definitions of `v_ext(a)` agree:
`v_r(s^n * a) * v_r(s)^{-n} = v_r(s^m * a) * v_r(s)^{-m}`.

Proof sketch: WLOG `n ≤ m`. Then `s^m * a = s^{m-n} * (s^n * a)`, so
`v_r(s^m * a) = v_r(s)^{m-n} * v_r(s^n * a)`. Dividing by `v_r(s)^m`
gives the same result as dividing `v_r(s^n * a)` by `v_r(s)^n`. -/
theorem vExt_well_defined {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
    (v : Valuation A Γ₀) {s : A} (hs_ne : v s ≠ 0) {a : A} {n m : ℕ}
    (_hn : s ^ n * a ∈ (P : PairOfDefinition A).A₀) (_hm : s ^ m * a ∈ P.A₀) :
    v (s ^ n * a) * (v s)⁻¹ ^ n = v (s ^ m * a) * (v s)⁻¹ ^ m := by
  have h1 : v (s ^ n * a) = v s ^ n * v a := by rw [map_mul, map_pow]
  have h2 : v (s ^ m * a) = v s ^ m * v a := by rw [map_mul, map_pow]
  rw [h1, h2]
  have hs_inv : ∀ k : ℕ, v s ^ k * (v s)⁻¹ ^ k = 1 := by
    intro k
    rw [← mul_pow, mul_inv_cancel₀ hs_ne, one_pow]
  calc v s ^ n * v a * (v s)⁻¹ ^ n
      = v s ^ n * (v s)⁻¹ ^ n * v a := by rw [mul_assoc, mul_comm (v a), mul_assoc]
    _ = 1 * v a := by rw [hs_inv]
    _ = v a := one_mul _
    _ = 1 * v a := (one_mul _).symm
    _ = v s ^ m * (v s)⁻¹ ^ m * v a := by rw [hs_inv]
    _ = v s ^ m * v a * (v s)⁻¹ ^ m := by
        rw [mul_assoc, mul_comm ((v s)⁻¹ ^ m), ← mul_assoc]

/-! ### Helper (d): Support of the extended valuation

The support of `v_ext` equals `𝔭`. The key point is:
- `a ∈ 𝔭 ⟹ s^n * a ∈ 𝔭` (since 𝔭 is an ideal) and `v_r(s^n * a) = 0`
  (since `v_r` restricted to `A₀` has support containing `𝔭 ∩ A₀`)
- `a ∉ 𝔭 ⟹ s^n * a ∉ 𝔭` (since `s ∉ 𝔭` and `𝔭` is prime) and
  `v_r(s^n * a) ≠ 0` -/

/-! ### Helper (e): Continuity of the extended valuation

The extended valuation is continuous when the restricted valuation on `A₀` is
continuous and `A₀` is open in `A`. This is Wedhorn's Lemma 7.44(2):
`v` on `A` is continuous iff `v|_{A₀}` is continuous on the open subring `A₀`. -/


/-- **Continuity transfer from open subring.** If `v` is a valuation on `A`,
`A₀` is an open subring, and `v|_{A₀}` (the restriction) is continuous
(in the subspace topology on `A₀`), then `v` is continuous on `A`.

This is Wedhorn's Lemma 7.44(2). The proof uses: for any `γ`, the set
`{a ∈ A | v(a) < γ}` is an additive subgroup containing the open set
`A₀.subtype '' {a ∈ A₀ | v(a) < γ}`, hence is open. -/
theorem isContinuous_of_restriction_isContinuous (P : PairOfDefinition A) {Γ₀ : Type*}
    [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation A Γ₀)
    (h_res : ∀ γ : Γ₀, IsOpen (P.A₀.subtype '' {a : P.A₀ | v (P.A₀.subtype a) < γ})) :
    v.IsContinuous := by
  intro γ
  by_cases hγ : γ = 0
  · subst hγ; simp only [not_lt_zero, Set.setOf_false, isOpen_empty]
  rw [show { a : A | v a < γ } =
    (v.ltAddSubgroup (Units.mk0 γ hγ) : Set A) from by ext; simp only [Set.mem_setOf_eq,
      Valuation.ltAddSubgroup, Units.val_mk0, AddSubgroup.coe_set_mk, AddSubmonoid.coe_set_mk,
      AddSubsemigroup.coe_set_mk]]
  apply AddSubgroup.isOpen_of_mem_nhds
  · have h_sub : P.A₀.subtype '' {a : P.A₀ | v (P.A₀.subtype a) < γ} ⊆
        (v.ltAddSubgroup (Units.mk0 γ hγ) : Set A) := by
      rintro _ ⟨a, ha, rfl⟩
      simp only [Valuation.ltAddSubgroup, Units.val_mk0]
      exact ha
    have h_zero : (0 : A) ∈ P.A₀.subtype '' {a : P.A₀ | v (P.A₀.subtype a) < γ} := by
      exact ⟨0, by simp only [Subring.subtype_apply, Set.mem_setOf_eq, ZeroMemClass.coe_zero,
        map_zero, zero_lt_iff.mpr hγ], rfl⟩
    exact Filter.mem_of_superset ((h_res γ).mem_nhds h_zero) h_sub

/-! ### Helper (f): A-plus boundedness

For `f ∈ A⁺ ⊆ A₀`, we have `v_ext(f) = v_r(f) ≤ 1` since `v_r ≤ 1` on `A₀`. -/

end PairOfDefinition

/-! ### Cofinal property for `WithZero` of `convexGenerated`

This lemma lifts the cofinal property from `convexGenerated` (the group) to
`WithZero(convexGenerated.toSubgroup)` (the value group). It is used in
`exists_spa_point_via_restrictToConvex` (Step 7) to establish that the
restricted valuation's bound has cofinal powers in the value group.

Note: The bound uses `u_max` (the inverse generator's inverse), whose membership
in `convexGenerated(u₀⁻¹)` follows directly from `self_mem_convexGenerated`. -/

namespace ConvexSubgroup

variable {Γ : Type*} [CommGroup Γ] [LinearOrder Γ] [IsOrderedMonoid Γ]

/-- **Cofinal property in `WithZero` of `convexGenerated` for the inverse generator.**

For `y > 1` in `Γ`, the element `y⁻¹ < 1` is in `convexGenerated(y)`, and its
powers are cofinal for `0` in `WithZero(convexGenerated(y).toSubgroup)`:
for every `γ > 0`, there exists `n` with `(y⁻¹)^n < γ`.

This is the `WithZero`-version of `exists_inv_pow_lt_of_mem_convexGenerated`,
specialized to the inverse of the generator. -/
theorem withZero_inv_pow_cofinal_of_convexGenerated {y : Γ} (hy : 1 < y) :
    ∀ (γ : WithZero (convexGenerated hy).toSubgroup), 0 < γ →
      ∃ n : ℕ,
        ((⟨y⁻¹, inv_mem (self_mem_convexGenerated hy)⟩ :
          (convexGenerated hy).toSubgroup) : WithZero _) ^ n < γ := by
  intro γ hγ
  obtain ⟨⟨δ, hδ_mem⟩, rfl⟩ := WithZero.ne_zero_iff_exists.mp (ne_of_gt hγ)
  obtain ⟨n, hn⟩ := exists_inv_pow_lt_of_mem_convexGenerated hy hδ_mem
  refine ⟨n, ?_⟩
  rw [← WithZero.coe_pow]
  exact WithZero.coe_lt_coe.mpr (Subtype.mk_lt_mk.mpr hn)

end ConvexSubgroup

namespace PairOfDefinition

open ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A]
  [IsTopologicalRing A]

/-! ### The restrictToConvex + v_ext construction (Wedhorn Lemma 7.44(3) + 7.45)

The key construction for Lemma 7.45: produce a continuous valuation on `A` with
support `𝔭` and value `≤ 1` on `A⁺`, using the `restrictToConvex` retraction
(Wedhorn 7.1.2) and extension from `A₀` to `A`.

**Strategy:**
1. Get `V₀` from the domination theorem (arbitrary rank).
2. Choose `a₀ ∈ I \ 𝔭`, set `u₀ = Units.mk0(V₀.valuation(φ(a₀)))`.
3. Let `H_gen = convexGenerated(u₀⁻¹)` and
   `v_r = (V₀.valuation ∘ φ).restrictToConvex H_gen hle` on `A₀`.
4. Extend `v_r` from `A₀` to `A` via `v_ext(a) = v_r(s^n * a) * v_r(s)^{-n}`.
5. Use `v_ext` directly as a `Valuation A (WithZero H_gen.toSubgroup)`.
6. Prove continuity using the cofinal property of `convexGenerated` (NOT MulArchimedean).
7. Prove `supp(v_ext) = 𝔭`, `v_ext ≤ 1` on `A⁺`.

The cofinal property comes from `withZero_inv_pow_cofinal_of_convexGenerated`:
for `u₀⁻¹ > 1`, the powers of `u₀ < 1` (= `(u₀⁻¹)⁻¹`) are cofinal in
`WithZero(convexGenerated(u₀⁻¹).toSubgroup)`.
-/

/-! ### Helpers for the v_ext construction

The following private lemmas factor out the algebraic steps of the
`v_ext(a) = v_r(s^n · a) · v_r(s)⁻ⁿ` construction used in Lemma 7.45.
They are stated with explicit parameters to keep each proof short. -/

omit [IsTopologicalRing A] in
theorem vExtFun_step (P : PairOfDefinition A) {Γ₀ : Type*}
    [LinearOrderedCommGroupWithZero Γ₀] (v_r : Valuation P.A₀ Γ₀) (v_s : Γ₀)
    {s : A} (hs_A₀ : s ∈ P.A₀) (hv_s : v_s = v_r ⟨s, hs_A₀⟩) (hv_r_s_ne : v_s ≠ 0)
    {a : A} (k j : ℕ) (hk : s ^ k * a ∈ P.A₀) :
    v_r ⟨s ^ k * a, hk⟩ * v_s⁻¹ ^ k =
    v_r ⟨s ^ (k + j) * a,
      P.pow_mul_mem_A₀_of_le hs_A₀ hk j⟩ *
      v_s⁻¹ ^ (k + j) := by
  have hfact : (⟨s ^ (k + j) * a,
      P.pow_mul_mem_A₀_of_le hs_A₀ hk j⟩ : P.A₀) =
      ⟨s, hs_A₀⟩ ^ j * ⟨s ^ k * a, hk⟩ :=
    Subtype.ext (show s ^ (k + j) * a = s ^ j * (s ^ k * a)
      from by rw [show k + j = j + k from by omega,
        pow_add, mul_assoc])
  have hval : v_r ⟨s ^ (k + j) * a,
      P.pow_mul_mem_A₀_of_le hs_A₀ hk j⟩ =
      v_s ^ j * v_r ⟨s ^ k * a, hk⟩ := by
    rw [hfact, map_mul, map_pow, hv_s]
  rw [hval, pow_add]
  set vr := v_r ⟨s ^ k * a, hk⟩
  have hc : v_s ^ j * v_s⁻¹ ^ j = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ hv_r_s_ne, one_pow]
  symm
  rw [mul_comm (v_s ^ j) vr, mul_assoc,
    mul_comm (v_s⁻¹ ^ k) (v_s⁻¹ ^ j),
    ← mul_assoc (v_s ^ j), hc, one_mul]

omit [IsTopologicalRing A] in
theorem vExtFun_well_defined (P : PairOfDefinition A) {Γ₀ : Type*}
    [LinearOrderedCommGroupWithZero Γ₀] (v_r : Valuation P.A₀ Γ₀) (v_s : Γ₀)
    {s : A} (hs_A₀ : s ∈ P.A₀) (hv_s : v_s = v_r ⟨s, hs_A₀⟩) (hv_r_s_ne : v_s ≠ 0)
    {a : A} (n m : ℕ) (hn : s ^ n * a ∈ P.A₀) (hm : s ^ m * a ∈ P.A₀) :
    v_r ⟨s ^ n * a, hn⟩ * v_s⁻¹ ^ n =
    v_r ⟨s ^ m * a, hm⟩ * v_s⁻¹ ^ m := by
  rw [vExtFun_step P v_r v_s hs_A₀ hv_s hv_r_s_ne n m hn,
    vExtFun_step P v_r v_s hs_A₀ hv_s hv_r_s_ne m n hm]
  exact congrArg₂ (· * ·)
    (congrArg v_r (Subtype.ext (show s ^ (n + m) * a =
      s ^ (m + n) * a from by rw [Nat.add_comm])))
    (show v_s⁻¹ ^ (n + m) = v_s⁻¹ ^ (m + n) from
      by rw [Nat.add_comm])

omit [IsTopologicalRing A] in
theorem vExtFun_map_mul (P : PairOfDefinition A) {Γ₀ : Type*}
    [LinearOrderedCommGroupWithZero Γ₀] (v_r : Valuation P.A₀ Γ₀) (v_s : Γ₀)
    {s x y : A} {nx ny : ℕ} (hnx : s ^ nx * x ∈ P.A₀) (hny : s ^ ny * y ∈ P.A₀)
    (hprod_mem : s ^ (nx + ny) * (x * y) ∈ P.A₀) :
    v_r ⟨s ^ (nx + ny) * (x * y), hprod_mem⟩ *
      v_s⁻¹ ^ (nx + ny) =
    (v_r ⟨s ^ nx * x, hnx⟩ * v_s⁻¹ ^ nx) *
      (v_r ⟨s ^ ny * y, hny⟩ * v_s⁻¹ ^ ny) := by
  have hfact : (⟨s ^ (nx + ny) * (x * y), hprod_mem⟩ :
      P.A₀) = ⟨s ^ nx * x, hnx⟩ * ⟨s ^ ny * y, hny⟩ :=
    Subtype.ext (show s ^ (nx + ny) * (x * y) =
      (s ^ nx * x) * (s ^ ny * y) from by ring)
  rw [hfact, map_mul, pow_add]
  exact mul_mul_mul_comm _ _ _ _

omit [IsTopologicalRing A] in
theorem vExtFun_map_add_le_max (P : PairOfDefinition A) {Γ₀ : Type*}
    [LinearOrderedCommGroupWithZero Γ₀] (v_r : Valuation P.A₀ Γ₀) (v_s : Γ₀)
    {s : A} {x y : A} {N : ℕ} (hNx : s ^ N * x ∈ P.A₀) (hNy : s ^ N * y ∈ P.A₀)
    (hNxy : s ^ N * (x + y) ∈ P.A₀) :
    v_r ⟨s ^ N * (x + y), hNxy⟩ * v_s⁻¹ ^ N ≤
    max (v_r ⟨s ^ N * x, hNx⟩ * v_s⁻¹ ^ N)
      (v_r ⟨s ^ N * y, hNy⟩ * v_s⁻¹ ^ N) := by
  have hsum : (⟨s ^ N * (x + y), hNxy⟩ : P.A₀) =
      ⟨s ^ N * x, hNx⟩ + ⟨s ^ N * y, hNy⟩ :=
    Subtype.ext (mul_add _ _ _)
  rw [hsum]
  set vx := v_r ⟨s ^ N * x, hNx⟩
  set vy := v_r ⟨s ^ N * y, hNy⟩
  set d := v_s⁻¹ ^ N
  have hult := v_r.map_add
    ⟨s ^ N * x, hNx⟩ ⟨s ^ N * y, hNy⟩
  have hmr : ∀ {a b : Γ₀}, a ≤ b → a * d ≤ b * d :=
    fun {a b} hab ↦ by
      rw [mul_comm a d, mul_comm b d]
      exact mul_le_mul_right hab d
  rcases le_max_iff.mp hult with h | h
  · exact le_max_of_le_left (hmr h)
  · exact le_max_of_le_right (hmr h)

/-- **Extension of a valuation from an open subring to the full ring** (Wedhorn Lemma 7.44(3)).

Given a valuation `v_r` on `A₀` and a topologically nilpotent element `s ∈ A₀` with
`v_r(s) ≠ 0`, constructs a valuation `v_ext` on `A` extending `v_r`. The extension is
`v_ext(a) = v_r(s^n * a) * v_r(s)^{-n}` where `n` is chosen so `s^n * a ∈ A₀`. -/
theorem exists_valuation_extension (P : PairOfDefinition A) {Γ₀ : Type*}
    [LinearOrderedCommGroupWithZero Γ₀] (v_r : Valuation P.A₀ Γ₀)
    {s : A} (hs_A₀ : s ∈ P.A₀) (hs_nil : IsTopologicallyNilpotent s)
    (hv_r_s_ne : v_r ⟨s, hs_A₀⟩ ≠ 0) :
    ∃ (v_ext : Valuation A Γ₀),
      (∀ a : P.A₀, v_ext (P.A₀.subtype a) = v_r a) ∧
      (∀ (a : A) (n : ℕ) (hn : s ^ n * a ∈ P.A₀),
        v_ext a = v_r ⟨s ^ n * a, hn⟩ * (v_r ⟨s, hs_A₀⟩)⁻¹ ^ n) := by
  classical
  have h_pow_mul : ∀ a : A, ∃ n : ℕ, s ^ n * a ∈ P.A₀ :=
    P.exists_pow_mul_mem_A₀ hs_nil
  set v_s := v_r ⟨s, hs_A₀⟩ with v_s_def
  let v_ext_fun : A → Γ₀ := fun a ↦
    let n := Nat.find (h_pow_mul a)
    v_r ⟨s ^ n * a, Nat.find_spec (h_pow_mul a)⟩ * v_s⁻¹ ^ n
  have v_ext_at : ∀ (a : A) (m : ℕ) (hm : s ^ m * a ∈ P.A₀),
      v_ext_fun a = v_r ⟨s ^ m * a, hm⟩ * v_s⁻¹ ^ m :=
    fun a m hm ↦ vExtFun_well_defined P v_r v_s hs_A₀ v_s_def
      hv_r_s_ne _ m (Nat.find_spec (h_pow_mul a)) hm
  have h_map_zero : v_ext_fun 0 = 0 := by
    rw [v_ext_at 0 0 (by simp [P.A₀.zero_mem])]
    simp only [pow_zero, one_mul, mul_one]
    have : (⟨(0 : A), P.A₀.zero_mem⟩ : P.A₀) = 0 := Subtype.ext rfl
    rw [this, map_zero]
  have h_map_one : v_ext_fun 1 = 1 := by
    rw [v_ext_at 1 0 (by simp [P.A₀.one_mem])]
    simp only [pow_zero, mul_one]
    have : (⟨(1 : A), P.A₀.one_mem⟩ : P.A₀) = 1 := Subtype.ext rfl
    rw [this, map_one]
  have h_map_mul : ∀ x y : A,
      v_ext_fun (x * y) = v_ext_fun x * v_ext_fun y := by
    intro x y
    set nx := Nat.find (h_pow_mul x); set ny := Nat.find (h_pow_mul y)
    have hnx := Nat.find_spec (h_pow_mul x); have hny := Nat.find_spec (h_pow_mul y)
    have hprod_mem : s ^ (nx + ny) * (x * y) ∈ P.A₀ := by
      rw [show s ^ (nx + ny) * (x * y) = (s ^ nx * x) * (s ^ ny * y) from by ring]
      exact P.A₀.mul_mem hnx hny
    rw [v_ext_at (x * y) (nx + ny) hprod_mem, v_ext_at x nx hnx, v_ext_at y ny hny]
    exact vExtFun_map_mul P v_r v_s hnx hny hprod_mem
  have h_map_add_le_max : ∀ x y : A,
      v_ext_fun (x + y) ≤ max (v_ext_fun x) (v_ext_fun y) := by
    intro x y
    set nx := Nat.find (h_pow_mul x); set ny := Nat.find (h_pow_mul y)
    have hnx := Nat.find_spec (h_pow_mul x); have hny := Nat.find_spec (h_pow_mul y)
    have hNx : s ^ (nx + ny) * x ∈ P.A₀ := P.pow_mul_mem_A₀_of_le hs_A₀ hnx ny
    have hNy : s ^ (nx + ny) * y ∈ P.A₀ := by
      rw [show nx + ny = ny + nx from by omega]
      exact P.pow_mul_mem_A₀_of_le hs_A₀ hny nx
    have hNxy : s ^ (nx + ny) * (x + y) ∈ P.A₀ := by
      rw [show s ^ (nx + ny) * (x + y) = s ^ (nx + ny) * x + s ^ (nx + ny) * y from
        mul_add _ _ _]
      exact P.A₀.add_mem hNx hNy
    rw [v_ext_at (x + y) (nx + ny) hNxy, v_ext_at x (nx + ny) hNx, v_ext_at y (nx + ny) hNy]
    exact vExtFun_map_add_le_max P v_r v_s hNx hNy hNxy
  let v_ext : Valuation A Γ₀ :=
    { toFun := v_ext_fun
      map_zero' := h_map_zero
      map_one' := h_map_one
      map_mul' := h_map_mul
      map_add_le_max' := h_map_add_le_max }
  refine ⟨v_ext, fun a ↦ ?_, fun a n hn ↦ ?_⟩
  · change v_ext_fun (P.A₀.subtype a) = v_r a
    have hmem : s ^ 0 * (P.A₀.subtype a) ∈ P.A₀ := by
      simp only [pow_zero, one_mul]; exact Subtype.coe_prop a
    rw [v_ext_at (P.A₀.subtype a) 0 hmem]
    simp only [pow_zero, one_mul, mul_one]
    exact congrArg v_r (Subtype.ext rfl)
  · exact v_ext_at a n hn

/-- The convex restriction of `V₀.valuation.comap (toFractionQuotient 𝔭)` vanishes on any
element of `A₀` whose image in `A` lies in the prime `𝔭` (since `toFractionQuotient 𝔭`
factors through `A / 𝔭`). -/
theorem restrictToConvex_comap_toFractionQuotient_eq_zero_of_mem_prime
    (P : PairOfDefinition A) {𝔭 : Ideal A} [𝔭.IsPrime]
    (V₀ : ValuationSubring (FractionRing (A ⧸ 𝔭)))
    (H : ConvexSubgroup V₀.ValueGroupˣ)
    (hle : ∀ r : P.A₀, (V₀.valuation.comap (P.toFractionQuotient 𝔭)) r ≤ 1)
    {b : P.A₀} (hb : (P.A₀.subtype b : A) ∈ 𝔭) :
    (V₀.valuation.comap (P.toFractionQuotient 𝔭)).restrictToConvex H hle b = 0 := by
  have hv₀_zero : (V₀.valuation.comap (P.toFractionQuotient 𝔭)) b = 0 := by
    rw [Valuation.comap_apply, show P.toFractionQuotient 𝔭 b =
        (algebraMap (A ⧸ 𝔭) (FractionRing (A ⧸ 𝔭))) ((Ideal.Quotient.mk 𝔭) (P.A₀.subtype b))
        from rfl,
      show (Ideal.Quotient.mk 𝔭) (P.A₀.subtype b) = 0 from
        Ideal.Quotient.eq_zero_iff_mem.mpr hb, map_zero, map_zero]
  rw [Valuation.restrictToConvex_unfold, dif_pos hv₀_zero]

/-- **Rank-1 extension (Wedhorn Lemma 7.45, Steps 3-7).**

Constructs a valuation `v_ext : Valuation A (WithZero H_gen.toSubgroup)` that is
continuous, has `supp(v_ext) ⊇ 𝔭`, and `v_ext ≤ 1` on `A⁺`. The value group
`WithZero(H_gen.toSubgroup)` admits cofinal powers (from `convexGenerated`),
which yields continuity without requiring `MulArchimedean`.

The proof uses `restrictToConvex` on `A₀` and extends to `A` via the
`v_ext(a) = v_r(s^n * a) * v_r(s)^{-n}` construction (Wedhorn Lemma 7.44(3)).
The algebraic sub-proofs (well-definedness, multiplicativity, ultrametric
inequality) are factored into `vExtFun_step`,
`vExtFun_well_defined`, `vExtFun_map_mul`, `vExtFun_map_add_le_max`. -/
theorem exists_spa_point_via_restrictToConvex (P : PairOfDefinition A)
    [IsAdicComplete P.I P.A₀] [PlusSubring A] {𝔭 : Ideal A} [𝔭.IsPrime]
    (h𝔭 : ¬IsOpen (𝔭 : Set A)) (hAplus_le_A₀ : (A⁺ : Set A) ⊆ P.A₀) :
    ∃ v ∈ Spa A A⁺, 𝔭 ≤ v.supp ∧ ¬P.idealOfDefinition ≤ v.supp := by
  haveI : IsDomain (A ⧸ 𝔭) := Ideal.Quotient.isDomain 𝔭
  obtain ⟨V₀, hrange₀, hnonunits₀⟩ := P.exists_valuationSubring_of_prime (𝔭 := 𝔭)
  obtain ⟨a₀, ha₀_I, ha₀_notp⟩ := P.exists_mem_I_not_mem_of_not_isOpen h𝔭
  set s := (P.A₀.subtype a₀ : A)
  have hs_nil : IsTopologicallyNilpotent s := P.isTopologicallyNilpotent_of_mem ha₀_I
  have _h_pow_mul : ∀ a : A, ∃ n : ℕ, s ^ n * a ∈ P.A₀ :=
    P.exists_pow_mul_mem_A₀ hs_nil
  set φ := P.toFractionQuotient 𝔭
  obtain ⟨S, hS⟩ := P.fg
  have hSne : S.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]; intro hS_eq
    have hI_bot : P.I = ⊥ := by rw [← hS, hS_eq, Finset.coe_empty, Ideal.span_empty]
    have ha₀_zero : a₀ = 0 := Ideal.mem_bot.mp (hI_bot ▸ ha₀_I)
    exact ha₀_notp (by rw [show s = P.A₀.subtype a₀ from rfl, ha₀_zero, map_zero]
                       exact 𝔭.zero_mem)
  set g_max := S.sup' hSne (fun t ↦ V₀.valuation (φ t)) with g_max_def
  have hg_lt1 : g_max < 1 := by
    rw [Finset.sup'_lt_iff]
    intro t ht
    exact P.pulledBackValuation_lt_one hnonunits₀
      (hS ▸ Ideal.subset_span (Finset.mem_coe.mpr ht))
  have ha₀_val_ne : V₀.valuation (φ a₀) ≠ 0 := by
    rw [ne_eq, Valuation.zero_iff]; intro h
    exact ha₀_notp (by
      simp only [φ, toFractionQuotient, RingHom.comp_apply, Subring.coe_subtype] at h
      exact Ideal.Quotient.eq_zero_iff_mem.mp
        ((IsFractionRing.injective (A ⧸ 𝔭) (FractionRing (A ⧸ 𝔭))).eq_iff.mp
          (h.trans (map_zero _).symm)))
  have hpb_eq : ∀ b : P.A₀, P.pulledBackValuation V₀ (P.A₀.subtype b) =
      V₀.valuation (φ b) := P.pulledBackValuation_eq_valuation_toFractionQuotient V₀
  have hpb_le_gmax : ∀ a : P.A₀, a ∈ P.I →
      P.pulledBackValuation V₀ (P.A₀.subtype a) ≤ g_max :=
    fun a ha ↦ valuation_le_on_ideal_of_le_on_generators (P.pulledBackValuation V₀)
      (P.pulledBackValuation_le_one hrange₀)
      hS (fun t ht ↦ hpb_eq t ▸ Finset.le_sup' (f := fun t ↦ V₀.valuation (φ t)) ht) ha
  have ha₀_val_le_gmax : V₀.valuation (φ a₀) ≤ g_max := by
    rw [← hpb_eq]; exact hpb_le_gmax a₀ ha₀_I
  have hg_ne0 : g_max ≠ 0 := ne_of_gt <|
    lt_of_lt_of_le (zero_lt_iff.mpr ha₀_val_ne) ha₀_val_le_gmax
  obtain ⟨t₀, ht₀_S, ht₀_val⟩ :=
    Finset.exists_mem_eq_sup' hSne (fun t ↦ V₀.valuation (φ t))
  have ht₀_I : t₀ ∈ P.I := hS ▸ Ideal.subset_span (Finset.mem_coe.mpr ht₀_S)
  have ht₀_notp : (P.A₀.subtype t₀ : A) ∉ 𝔭 := by
    intro h_in_p
    have : V₀.valuation (φ t₀) = 0 := by
      have hφ_zero : φ t₀ = 0 := by
        simp only [φ, toFractionQuotient, RingHom.comp_apply, Subring.coe_subtype]
        exact (map_eq_zero_iff _
          (IsFractionRing.injective (A ⧸ 𝔭) (FractionRing (A ⧸ 𝔭)))).mpr
            (Ideal.Quotient.eq_zero_iff_mem.mpr h_in_p)
      rw [hφ_zero, map_zero]
    exact hg_ne0 (by convert this using 1)
  clear a₀ ha₀_I ha₀_notp s hs_nil _h_pow_mul ha₀_val_ne ha₀_val_le_gmax
  set a₀ := t₀
  set s := (P.A₀.subtype a₀ : A)
  have ha₀_I : a₀ ∈ P.I := ht₀_I
  have ha₀_notp : s ∉ 𝔭 := ht₀_notp
  have hs_nil : IsTopologicallyNilpotent s := P.isTopologicallyNilpotent_of_mem ha₀_I
  have ha₀_val_eq : V₀.valuation (φ a₀) = g_max := ht₀_val.symm
  set u_max := Units.mk0 g_max hg_ne0
  have hu_max_lt1 : (u_max : V₀.ValueGroup) < 1 := hg_lt1
  have hu_max_inv_gt1 : (1 : V₀.ValueGroupˣ) < u_max⁻¹ :=
    one_lt_inv_of_inv hu_max_lt1
  set H_gen := ConvexSubgroup.convexGenerated hu_max_inv_gt1 with H_gen_def
  have hu_max_mem : u_max ∈ H_gen := by
    rw [show u_max = (u_max⁻¹)⁻¹ from (inv_inv u_max).symm]
    exact inv_mem (ConvexSubgroup.self_mem_convexGenerated hu_max_inv_gt1)
  set v₀_A₀ := V₀.valuation.comap φ with v₀_A₀_def
  have hle_A₀ : ∀ r : P.A₀, v₀_A₀ r ≤ 1 := fun r ↦ by
    simp only [v₀_A₀, Valuation.comap_apply]
    exact (ValuationSubring.valuation_le_one_iff V₀ _).mpr (hrange₀ ⟨r, rfl⟩)
  set v_r := v₀_A₀.restrictToConvex H_gen hle_A₀ with v_r_def
  have hv₀_a₀_ne : v₀_A₀ a₀ ≠ 0 := by
    intro h_eq
    apply ha₀_notp
    have : v₀_A₀ a₀ = V₀.valuation (φ a₀) := by rfl
    rw [this] at h_eq
    have hφ_zero : φ a₀ = 0 := V₀.valuation.zero_iff.mp h_eq
    simp only [φ, toFractionQuotient, RingHom.comp_apply, Subring.coe_subtype] at hφ_zero
    exact Ideal.Quotient.eq_zero_iff_mem.mp
      ((IsFractionRing.injective (A ⧸ 𝔭) (FractionRing (A ⧸ 𝔭))).eq_iff.mp
        (hφ_zero.trans (map_zero _).symm))
  have hu_a₀_mem : Units.mk0 (v₀_A₀ a₀) hv₀_a₀_ne ∈ H_gen := by
    have hu_eq : Units.mk0 (v₀_A₀ a₀) hv₀_a₀_ne = u_max :=
      Units.ext ha₀_val_eq
    rw [hu_eq]; exact hu_max_mem
  have hv_r_s_ne : v_r a₀ ≠ 0 :=
    ne_of_gt (Valuation.restrictToConvex_pos_of_mem
      v₀_A₀ H_gen hle_A₀ hv₀_a₀_ne hu_a₀_mem)
  suffices h_ext : ∃ (v_ext : Valuation A (WithZero H_gen.toSubgroup)),
      (∀ a ∈ 𝔭, v_ext a = 0) ∧
      (∀ a : P.A₀, v_ext (P.A₀.subtype a) = v_r a) ∧
      v_ext.IsContinuous ∧
      (∀ f ∈ (A⁺ : Set A), v_ext f ≤ 1) by
    obtain ⟨v_ext, hfwd, h_ext_A₀, hcont, hAplus⟩ := h_ext
    refine ⟨ofValuation v_ext, ⟨isContinuous_ofValuation_of _ hcont, ?_⟩, ?_, ?_⟩
    · intro f hf; change v_ext f ≤ v_ext 1; rw [map_one]; exact hAplus f hf
    · intro a ha; rw [supp_ofValuation]; exact (Valuation.mem_supp_iff _ _).mpr (hfwd a ha)
    · intro h_le
      have ha₀_in_J : (P.A₀.subtype a₀ : A) ∈ P.idealOfDefinition :=
        Ideal.mem_map_of_mem _ ha₀_I
      have ha₀_supp : (P.A₀.subtype a₀ : A) ∈ (ofValuation v_ext).supp :=
        h_le ha₀_in_J
      rw [supp_ofValuation, Valuation.mem_supp_iff] at ha₀_supp
      exact hv_r_s_ne (h_ext_A₀ a₀ ▸ ha₀_supp)
  classical
  have h_pow_mul : ∀ a : A, ∃ n : ℕ, s ^ n * a ∈ P.A₀ :=
    P.exists_pow_mul_mem_A₀ hs_nil
  suffices h_val : ∃ (v_ext : Valuation A (WithZero H_gen.toSubgroup)),
      (∀ a : P.A₀, v_ext (P.A₀.subtype a) = v_r a) ∧
      (∀ a : A, a ∈ 𝔭 → v_ext a = 0) by
    obtain ⟨v_ext, h_ext_A₀, h_ext_zero⟩ := h_val
    refine ⟨v_ext, ?_, h_ext_A₀, ?_, ?_⟩
    · intro a ha_p
      exact (Valuation.mem_supp_iff v_ext a).mpr (h_ext_zero a ha_p)
    · set g_cont : WithZero H_gen.toSubgroup :=
        ((⟨u_max, hu_max_mem⟩ : H_gen.toSubgroup) : WithZero H_gen.toSubgroup) with g_cont_def
      have hg_ne : g_cont ≠ 0 := WithZero.coe_ne_zero
      have hg_lt : g_cont < 1 := by
        rw [g_cont_def, show (1 : WithZero H_gen.toSubgroup) =
          ((1 : H_gen.toSubgroup) : WithZero _) from rfl]
        exact WithZero.coe_lt_coe.mpr (Subtype.mk_lt_mk.mpr (Units.val_lt_val.mp hu_max_lt1))
      have hg_bound : ∀ a : P.A₀, a ∈ P.I → v_ext (P.A₀.subtype a) ≤ g_cont := by
        intro a ha
        rw [h_ext_A₀ a]
        rw [v_r_def]
        by_cases hv_eq : v₀_A₀ a = 0
        · rw [Valuation.restrictToConvex_unfold, dif_pos hv_eq]; exact bot_le
        · by_cases hm : Units.mk0 (v₀_A₀ a) hv_eq ∈ H_gen
          · rw [Valuation.restrictToConvex_unfold, dif_neg hv_eq, dif_pos hm]
            rw [g_cont_def]
            exact WithZero.coe_le_coe.mpr (Subtype.mk_le_mk.mpr
              (Units.val_le_val.mp (hpb_le_gmax a ha)))
          · rw [Valuation.restrictToConvex_unfold, dif_neg hv_eq, dif_neg hm]; exact bot_le
      have h_le_ext : ∀ a : P.A₀, v_ext (P.A₀.subtype a) ≤ 1 := by
        intro a; rw [h_ext_A₀ a]
        exact Valuation.restrictToConvex_le_one v₀_A₀ H_gen hle_A₀ a
      have h_cofinal : ∀ γ : WithZero H_gen.toSubgroup, 0 < γ →
          ∃ n : ℕ, g_cont ^ n < γ := by
        intro γ hγ
        obtain ⟨n, hn⟩ := ConvexSubgroup.withZero_inv_pow_cofinal_of_convexGenerated
          hu_max_inv_gt1 γ hγ
        exact ⟨n, by simpa only [g_cont_def, inv_inv] using hn⟩
      exact Valuation.isContinuous_of_le_one_and_pow_cofinal P v_ext h_le_ext
        hg_bound h_cofinal
    · intro f hf
      have hf_A₀ : f ∈ P.A₀ := hAplus_le_A₀ hf
      have : v_ext f = v_ext (P.A₀.subtype ⟨f, hf_A₀⟩) := by
        simp only [Subring.subtype_apply]
      rw [this, h_ext_A₀ ⟨f, hf_A₀⟩]
      exact Valuation.restrictToConvex_le_one v₀_A₀ H_gen hle_A₀ ⟨f, hf_A₀⟩
  -- The valuation `v_ext` extending `v_r` from `A₀` to `A` is `exists_valuation_extension`
  -- (Wedhorn 7.44(3)); it remains to check it vanishes on `𝔭`.
  have hs_A₀ : s ∈ P.A₀ := Subtype.coe_prop a₀
  have hv_r_s_ne' : v_r ⟨s, hs_A₀⟩ ≠ 0 := by
    rwa [show (⟨s, hs_A₀⟩ : P.A₀) = a₀ from Subtype.ext rfl]
  obtain ⟨v_ext, h_ext_A₀, h_ext_at⟩ :=
    P.exists_valuation_extension v_r hs_A₀ hs_nil hv_r_s_ne'
  refine ⟨v_ext, h_ext_A₀, fun a ha_p ↦ ?_⟩
  obtain ⟨n, hn⟩ := h_pow_mul a
  have hv_r_zero : v_r ⟨s ^ n * a, hn⟩ = 0 :=
    P.restrictToConvex_comap_toFractionQuotient_eq_zero_of_mem_prime V₀ H_gen hle_A₀
      (𝔭.mul_mem_left _ ha_p)
  rw [h_ext_at a n hn, hv_r_zero, zero_mul]

/-! ### Full proof assembly -/

/-- **Lemma 7.45 of Wedhorn.** Non-open primes are supports in `Spa`.

Given a complete affinoid ring `(A, A⁺)` with pair of definition `(A₀, I)` and
a non-open prime `𝔭` of `A`, there exists `v ∈ Spa(A, A⁺)` with `supp(v) ⊇ 𝔭`.

Note: Wedhorn's Lemma 7.45 gives `supp ⊇ 𝔭` (not `= 𝔭`) in the general case.
The exact equality `supp = 𝔭` requires the rank-1 domination theorem (Bourbaki)
or the discrete topology case (already proved in `AdicSpectrum.lean`).

The proof uses `restrictToConvex` with `convexGenerated` to produce a continuous
valuation. The cofinal property of `convexGenerated` gives continuity directly,
avoiding the `MulArchimedean` intermediate.

References: Wedhorn, Adic Spaces, Lemma 7.45. -/
theorem exists_mem_spa_supp_ge_of_nonOpen_prime (P : PairOfDefinition A)
    [IsAdicComplete P.I P.A₀] [PlusSubring A] {𝔭 : Ideal A} [𝔭.IsPrime]
    (h𝔭 : ¬IsOpen (𝔭 : Set A)) (hAplus_le_A₀ : (A⁺ : Set A) ⊆ P.A₀) :
    ∃ v ∈ Spa A A⁺, 𝔭 ≤ v.supp ∧ ¬P.idealOfDefinition ≤ v.supp :=
  P.exists_spa_point_via_restrictToConvex h𝔭 hAplus_le_A₀

/-- **Wedhorn Lemma 7.45, `Cont`-level form** (no `A⁺` data): for a non-open prime `𝔭` of a
complete Huber ring there is a continuous *analytic* valuation `x` with `𝔭 ≤ supp x` and
`supp x ⊉ I`. Obtained from `exists_spa_point_via_restrictToConvex` by instantiating the
plus subring at the ring of definition itself (`A⁺ := A₀`, where `hAplus_le_A₀` is
`subset_rfl`); the `A⁺`-bound clause of `Spa`-membership is discarded.
Source: Wedhorn Lemma 7.45 (wedhorn.txt:3336). -/
theorem exists_cont_analytic_supp_ge_of_nonOpen_prime (P : PairOfDefinition A)
    [IsAdicComplete P.I P.A₀] {𝔭 : Ideal A} [𝔭.IsPrime]
    (h𝔭 : ¬IsOpen (𝔭 : Set A)) :
    ∃ x : Spv A, x ∈ Cont A ∧ 𝔭 ≤ x.supp ∧ ¬P.idealOfDefinition ≤ x.supp := by
  letI : PlusSubring A := ⟨P.A₀⟩
  obtain ⟨v, hv_spa, hsupp, hanalytic⟩ :=
    P.exists_spa_point_via_restrictToConvex h𝔭 (le_refl (P.A₀ : Set A))
  exact ⟨v, hv_spa.1, hsupp, hanalytic⟩

/-- **Containment form of complete-affinoid Spa-point existence (Wedhorn 7.45 + 7.51).**
For a maximal ideal `𝔪` of a complete affinoid ring `(A, A⁺)` with pair of definition `P`,
there is `v ∈ Spa(A, A⁺)` with `𝔪 ≤ supp(v)`.

* **Open case**: the trivial valuation on `A/𝔪` (Prop 7.51, `exists_mem_spa_supp_eq`)
  gives `supp(v) = 𝔪`, hence `𝔪 ≤ supp(v)`.
* **Non-open case**: Lemma 7.45 (`exists_mem_spa_supp_ge_of_nonOpen_prime`) gives
  `𝔪 ≤ supp(v)` directly.

Unlike the exact form `supp(v) = 𝔪` (which in the non-open case needs the rank-1
domination theorem), this **containment** form is axiom-clean and is exactly what the
Nullstellensatz unit criterion 7.52(2) consumes (a non-unit `f` lies in a maximal `𝔪`,
and `𝔪 ≤ supp(v)` already forces `v(f) = 0`). -/
theorem exists_spa_point_supp_ge_maxIdeal_of_complete
    [IsTopologicalRing A] (P : PairOfDefinition A) [IsAdicComplete P.I P.A₀]
    [PlusSubring A] (𝔪 : Ideal A) [𝔪.IsMaximal]
    (hAplus_le_A₀ : (A⁺ : Set A) ⊆ P.A₀) :
    ∃ v ∈ Spa A A⁺, 𝔪 ≤ v.supp := by
  by_cases h𝔪_open : IsOpen (𝔪 : Set A)
  · obtain ⟨v, hv, hsupp⟩ := exists_mem_spa_supp_eq 𝔪 h𝔪_open
    exact ⟨v, hv, le_of_eq hsupp.symm⟩
  · haveI : 𝔪.IsPrime := inferInstance
    obtain ⟨v, hv, hsupp, _⟩ :=
      P.exists_mem_spa_supp_ge_of_nonOpen_prime h𝔪_open hAplus_le_A₀
    exact ⟨v, hv, hsupp⟩

/-- **Wedhorn 7.52(2) for complete affinoid rings (Nullstellensatz unit criterion).**
For a complete affinoid ring `(A, A⁺)` with pair of definition `P`, an element `f` is a
unit iff `v(f) ≠ 0` for every `v ∈ Spa(A, A⁺)`.

This is the axiom-clean form: the reverse direction (non-vanishing ⟹ unit) is discharged
via `exists_spa_point_supp_ge_maxIdeal_of_complete` — a non-unit `f` lies in some maximal
ideal `𝔪`, which yields a Spa point `v` with `𝔪 ≤ supp(v)`, so `f ∈ supp(v)`, i.e.
`v(f) = 0`. Only the **containment** `𝔪 ≤ supp(v)` is needed, not the exact support
equality, so this avoids the rank-1 domination residual. -/
theorem isUnit_iff_forall_not_vle_zero_of_complete
    [IsTopologicalRing A] (P : PairOfDefinition A) [IsAdicComplete P.I P.A₀]
    [PlusSubring A] (hAplus_le_A₀ : (A⁺ : Set A) ⊆ P.A₀) (f : A) :
    IsUnit f ↔ ∀ v ∈ Spa A A⁺, ¬ v.vle f 0 := by
  refine ⟨fun hu v _ ↦ not_vle_zero_of_isUnit hu v, fun h ↦ ?_⟩
  by_contra hf
  obtain ⟨𝔪, h𝔪, hf𝔪⟩ :=
    Ideal.exists_le_maximal (Ideal.span {f}) (Ideal.span_singleton_ne_top hf)
  haveI := h𝔪
  obtain ⟨v, hv, hsupp⟩ := P.exists_spa_point_supp_ge_maxIdeal_of_complete 𝔪 hAplus_le_A₀
  exact h v hv ((v.mem_supp_iff f).mp (hsupp (hf𝔪 (Ideal.mem_span_singleton_self f))))

end PairOfDefinition

/-! ### Wedhorn Lemma 7.45, height-one form (assembly)

The `Cont`-level analytic point of `exists_cont_analytic_supp_ge_of_nonOpen_prime`,
vertically generized to height one by
`Valuation.coarsen_maxAvoid_isContinuous_mulArchimedean` (ValuationContinuity). The
value-group bookkeeping: transport the canonical valuation along `Γ₀ →*₀ WithZero Γ₀ˣ`,
coarsen, and pull `MulArchimedean` back to the canonical value group of the resulting
`Spv`-point along the strictly monotone `embed`/`embedding` chain. -/

section HeightOneAssembly

open ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

/-- The canonical splitting `Γ₀ →*₀ WithZero Γ₀ˣ` of a linearly ordered commutative
group-with-zero. -/
noncomputable def withZeroUnitsSplit (Γ₀ : Type*) [LinearOrderedCommGroupWithZero Γ₀] :
    Γ₀ →*₀ WithZero Γ₀ˣ where
  toFun γ := if h : γ = 0 then 0 else ↑(Units.mk0 γ h)
  map_zero' := by simp
  map_one' := by
    rw [dif_neg one_ne_zero]
    norm_cast
    exact Units.ext (by simp)
  map_mul' x y := by
    rcases eq_or_ne x 0 with rfl | hx
    · simp
    rcases eq_or_ne y 0 with rfl | hy
    · simp
    rw [dif_neg hx, dif_neg hy, dif_neg (mul_ne_zero hx hy), ← WithZero.coe_mul]
    exact congrArg _ (Units.ext (by simp))

theorem withZeroUnitsSplit_eq_zero_iff {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
    {γ : Γ₀} : withZeroUnitsSplit Γ₀ γ = 0 ↔ γ = 0 := by
  unfold withZeroUnitsSplit
  simp only [MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk]
  split_ifs with h
  · simp [h]
  · simp [h]

theorem withZeroUnitsSplit_apply_ne {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
    {γ : Γ₀} (h : γ ≠ 0) : withZeroUnitsSplit Γ₀ γ = ↑(Units.mk0 γ h) := by
  unfold withZeroUnitsSplit
  simp only [MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, dif_neg h]

theorem withZeroUnitsSplit_monotone (Γ₀ : Type*) [LinearOrderedCommGroupWithZero Γ₀] :
    Monotone (withZeroUnitsSplit Γ₀) := by
  intro a b hab
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  have hb : b ≠ 0 := fun h ↦ ha (le_antisymm (h ▸ hab) (zero_le' (a := a)))
  rw [withZeroUnitsSplit_apply_ne ha, withZeroUnitsSplit_apply_ne hb, WithZero.coe_le_coe,
    ← Units.val_le_val]
  simpa using hab

theorem withZeroUnitsSplit_lt_coe_iff {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
    {γ : Γ₀} {u : Γ₀ˣ} : withZeroUnitsSplit Γ₀ γ < ↑u ↔ γ < (u : Γ₀) := by
  rcases eq_or_ne γ 0 with rfl | h
  · simp [WithZero.zero_lt_coe, Units.zero_lt]
  · rw [withZeroUnitsSplit_apply_ne h, WithZero.coe_lt_coe, ← Units.val_lt_val]
    simp

namespace PairOfDefinition

/-- An open prime ideal contains the ideal of definition (`I`-image powers land in it,
then primality). -/
theorem idealOfDefinition_le_of_isOpen_of_isPrime (P : PairOfDefinition A)
    {J : Ideal A} [J.IsPrime] (hJ : IsOpen (J : Set A)) :
    P.idealOfDefinition ≤ J := by
  obtain ⟨N, -, hN⟩ := P.hasBasis_nhds_zero.mem_iff.mp (hJ.mem_nhds J.zero_mem)
  rw [idealOfDefinition, Ideal.map_le_iff_le_comap]
  intro b hb
  have hmem : (P.A₀.subtype (b ^ N) : A) ∈ J :=
    hN ⟨b ^ N, Ideal.pow_mem_pow hb N, rfl⟩
  rw [map_pow] at hmem
  exact ‹J.IsPrime›.mem_of_pow_mem N hmem

end PairOfDefinition

/-- `MulArchimedean` descends to the canonical value group of `ofValuation w` from the
codomain of `w`, along the strictly monotone `embed`/`embedding` chain. -/
theorem mulArchimedean_valueGroupWithZero_ofValuation {Γ₀' : Type*}
    [LinearOrderedCommGroupWithZero Γ₀'] [MulArchimedean Γ₀']
    (w : Valuation A Γ₀') :
    (letI : ValuativeRel A := ValuativeRel.ofValuation w
     MulArchimedean (ValuativeRel.ValueGroupWithZero A)) := by
  letI : ValuativeRel A := ValuativeRel.ofValuation w
  haveI := Valuation.Compatible.ofValuation w
  have h1 := ValuativeRel.ValueGroupWithZero.embed_strictMono w
  have h2 := MonoidWithZeroHom.ValueGroup₀.embedding_strictMono
    (f := MonoidWithZeroHom.ofClass w)
  exact MulArchimedean.comap
    ((MonoidWithZeroHom.ValueGroup₀.embedding.comp
      (ValuativeRel.ValueGroupWithZero.embed w)).toMonoidHom) (h2.comp h1)

namespace PairOfDefinition

/-- **Wedhorn Lemma 7.45, height-one analytic form (assembled).** For a non-open prime
`𝔭` of a complete Huber ring there is a continuous valuation `x` with `𝔭 ≤ supp x`,
non-open support, and `MulArchimedean` canonical value group (Wedhorn's height-one
vertical generization, Remarks 7.38/7.40(5)/4.12).
Source: Wedhorn Lemma 7.45 (wedhorn.txt:3336) + Remark 7.40(5). -/
theorem exists_heightOne_analytic_cont_supp_ge_of_nonOpen_prime'
    (P : PairOfDefinition A) [IsAdicComplete P.I P.A₀]
    {𝔭 : Ideal A} [𝔭.IsPrime] (h𝔭 : ¬IsOpen (𝔭 : Set A)) :
    ∃ x : Spv A, x ∈ Cont A ∧ 𝔭 ≤ x.supp ∧ ¬IsOpen (x.supp : Set A) ∧
      (letI : ValuativeRel A := x.toValuativeRel
       MulArchimedean (ValuativeRel.ValueGroupWithZero A)) := by
  classical
  obtain ⟨x₀, hx₀_cont, hx₀_supp, hx₀_an⟩ :=
    P.exists_cont_analytic_supp_ge_of_nonOpen_prime h𝔭
  letI : ValuativeRel A := x₀.toValuativeRel
  set v := ValuativeRel.valuation A with hv_def
  have hv_cont : v.IsContinuous := hx₀_cont
  have hsupp_eq : x₀.supp = v.supp :=
    @ValuativeRel.supp_eq_valuation_supp A _ x₀.toValuativeRel
  -- A generator of the ideal of definition outside the support.
  have hex : ∃ b ∈ P.I, (P.A₀.subtype b : A) ∉ x₀.supp := by
    by_contra hcon
    push_neg at hcon
    exact hx₀_an (Ideal.map_le_iff_le_comap.mpr fun b hb ↦ hcon b hb)
  obtain ⟨b, hb_I, hb_supp⟩ := hex
  set i : A := P.A₀.subtype b with hi_def
  have hi_nil : IsTopologicallyNilpotent i := P.isTopologicallyNilpotent_of_mem hb_I
  have hvi_ne : v i ≠ 0 := by
    intro h0
    exact hb_supp (hsupp_eq ▸ (Valuation.mem_supp_iff v i).mpr h0)
  -- `v i < 1` from continuity and topological nilpotence.
  have hvi_lt : v i < 1 := by
    have hopen : IsOpen {a : A | v a < 1} := hv_cont 1
    have h0mem : (0 : A) ∈ {a : A | v a < 1} := by simp
    obtain ⟨n, hn⟩ := (hi_nil.eventually (hopen.mem_nhds h0mem)).exists
    by_contra hge
    rw [not_lt] at hge
    refine absurd hn (not_lt.mpr ?_)
    calc (1 : ValuativeRel.ValueGroupWithZero A) = 1 ^ n := (one_pow n).symm
      _ ≤ (v i) ^ n := pow_le_pow_left' hge n
      _ = v (i ^ n) := (map_pow v i n).symm
  -- Transport along `Γ₀ →*₀ WithZero Γ₀ˣ`.
  set φ := withZeroUnitsSplit (ValuativeRel.ValueGroupWithZero A) with hφ_def
  set v' : Valuation A (WithZero (ValuativeRel.ValueGroupWithZero A)ˣ) :=
    v.map φ (withZeroUnitsSplit_monotone _) with hv'_def
  have hv'_apply : ∀ a : A, v' a = φ (v a) := fun a ↦ Valuation.map_apply _ _ _ _
  have hv'_cont : v'.IsContinuous := by
    intro δ
    rcases eq_or_ne δ 0 with rfl | hδ
    · simp only [not_lt_zero]
      exact isOpen_empty
    obtain ⟨u, rfl⟩ := WithZero.ne_zero_iff_exists.mp hδ
    have : {a : A | v' a < ↑u} = {a : A | v a < (u : ValuativeRel.ValueGroupWithZero A)} := by
      ext a
      rw [Set.mem_setOf_eq, Set.mem_setOf_eq, hv'_apply, withZeroUnitsSplit_lt_coe_iff]
    rw [this]
    exact hv_cont _
  have hv'_supp : v'.supp = v.supp := by
    ext a
    rw [Valuation.mem_supp_iff, Valuation.mem_supp_iff, hv'_apply,
      withZeroUnitsSplit_eq_zero_iff]
  -- The cofinal unit `g₀ := v i`.
  set g₀ : (ValuativeRel.ValueGroupWithZero A)ˣ := Units.mk0 (v i) hvi_ne with hg₀_def
  have hg₀_lt : g₀ < 1 := by
    rw [← Units.val_lt_val, hg₀_def]
    simpa using hvi_lt
  have hcof : ∀ γ : (ValuativeRel.ValueGroupWithZero A)ˣ, ∃ n : ℕ, g₀ ^ n ≤ γ := by
    intro γ
    obtain ⟨a, s, hval⟩ := ValuativeRel.exists_valuation_div_valuation_eq
      (γ : ValuativeRel.ValueGroupWithZero A)
    have hvs_ne : v (s : A) ≠ 0 := ValuativeRel.valuation_posSubmonoid_ne_zero s
    have hva_ne : v a ≠ 0 := by
      intro h0
      apply γ.ne_zero
      rw [← hval, h0, zero_div]
    -- continuity at `v a`: the sequence `i ^ n * s` enters `{v < v a}`.
    have hopen : IsOpen {c : A | v c < v a} := hv_cont _
    have h0mem : (0 : A) ∈ {c : A | v c < v a} := by
      simp [zero_lt_iff.mpr hva_ne]
    have htend : Filter.Tendsto (fun n : ℕ ↦ i ^ n * (s : A)) Filter.atTop (nhds 0) := by
      simpa using hi_nil.mul_const (s : A)
    obtain ⟨n, hn⟩ := (htend.eventually (hopen.mem_nhds h0mem)).exists
    refine ⟨n, ?_⟩
    rw [← Units.val_le_val]
    have hval_le : (v i) ^ n * v (s : A) ≤ v a := by
      have hlt : v (i ^ n * (s : A)) < v a := hn
      rw [map_mul, map_pow] at hlt
      exact le_of_lt hlt
    calc ((g₀ ^ n : (ValuativeRel.ValueGroupWithZero A)ˣ) : ValuativeRel.ValueGroupWithZero A)
        = (v i) ^ n := by simp [hg₀_def]
      _ ≤ v a / v (s : A) := (le_div_iff₀ (zero_lt_iff.mpr hvs_ne)).mpr hval_le
      _ = (γ : ValuativeRel.ValueGroupWithZero A) := hval
  -- Coarsen and package.
  obtain ⟨hw_cont, hw_arch⟩ :=
    v'.coarsen_maxAvoid_isContinuous_mulArchimedean hv'_cont hg₀_lt hcof
  set w := v'.coarsen (ConvexSubgroup.maxAvoid hg₀_lt.ne) with hw_def
  have hw_supp : w.supp = x₀.supp := by
    rw [hw_def, Valuation.coarsen_supp, hv'_supp, hsupp_eq]
  haveI : MulArchimedean
      (WithZero ((ValuativeRel.ValueGroupWithZero A)ˣ ⧸
        (ConvexSubgroup.maxAvoid hg₀_lt.ne).toSubgroup)) := by
    haveI := hw_arch
    infer_instance
  refine ⟨ofValuation w, isContinuous_ofValuation_of w hw_cont, ?_, ?_, ?_⟩
  · rw [supp_ofValuation, hw_supp]
    exact hx₀_supp
  · rw [supp_ofValuation, hw_supp]
    intro hopen
    exact hx₀_an (P.idealOfDefinition_le_of_isOpen_of_isPrime hopen)
  · exact mulArchimedean_valueGroupWithZero_ofValuation w

end PairOfDefinition

end HeightOneAssembly
