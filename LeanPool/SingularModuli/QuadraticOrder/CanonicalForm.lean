/-
Copyright (c) 2026 Lean Pool contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Caleb L. Geiger
-/

import LeanPool.SingularModuli.QuadraticOrder.Prime

/-!
# Layer 2b: Canonical Form for ideals of `QuadraticOrder` — scaffolding

This file is the first PR of the Lemma 3.2.4 (canonical form) sequence.
It introduces the central definitions and proves the structural
identity that the canonical ideal coincides with the plain `ℤ`-span
of its two generators.

For `d : ℤ`, a natural-number "prime power exponent" pair `(k, m)` with
`m/2 ≤ k ≤ m`, and an integer `A`, the **canonical ideal**

```
canonicalIdeal d p k m A = ⟨p^k, p^(m-k) · (τ - A)⟩
```

is the generic `𝔭`-primary ideal of `QuadraticOrder d` predicted by
Lemma 3.2.4. The integer pair `(k, A)` is **admissible** if `p^(2k-m)`
divides `A² - dA + (d²-d)/4` — equivalently, if `poly d` evaluated at
`A` is divisible by `p^(2k-m)`.

## Main results

* `canonicalIdeal` / `CanonicalAdmissible` — the two definitions.
* `canonicalZSpan` — the `ℤ`-submodule spanned by the two generators.
* `canonicalIdeal_eq_zSpan` — under `k ≤ m ≤ 2·k` and admissibility,
  the underlying additive subgroup of `canonicalIdeal` coincides with
  `canonicalZSpan`. The proof goes via τ-stability of `canonicalZSpan`.

The arithmetic content (index `= p^m`, existence and uniqueness of
canonical forms) is developed in subsequent PRs on top of this
scaffolding.
-/

namespace QuadraticOrder

variable {d : ℤ} {p k m : ℕ} {A : ℤ}

/-! ### Definitions -/

/-- The canonical ideal `⟨p^k, p^(m-k) · (τ - A)⟩` of `QuadraticOrder d`.
The intended parameter range is `m/2 ≤ k ≤ m` with `A` taken modulo
`p^(2k-m)`. -/
noncomputable def canonicalIdeal (d : ℤ) (p k m : ℕ) (A : ℤ) :
    Ideal (QuadraticOrder d) :=
  Ideal.span {(p : QuadraticOrder d) ^ k,
              (p : QuadraticOrder d) ^ (m - k) *
                (tau - (A : QuadraticOrder d))}

/-- A canonical-form parameter `(k, A)` is **admissible** at index `p^m`
if `p^(2k-m)` divides `A² - dA + (d²-d)/4` — equivalently, the integer
`(poly d).eval A` is divisible by `p^(2k-m)`.

The `ℕ`-subtraction `2 * k - m` is `0` whenever `2 * k < m`, in which
case the predicate is vacuous; this is used only in tandem with the
`m ≤ 2 * k` constraint. -/
def CanonicalAdmissible (d : ℤ) (p k m : ℕ) (A : ℤ) : Prop :=
  (p : ℤ) ^ (2 * k - m) ∣ A ^ 2 - d * A + (d ^ 2 - d) / 4

/-! ### The "Z-span" of the two canonical generators

We work with `canonicalZSpan := Submodule.span ℤ {p^k, p^(m-k)·(τ-A)}`
as an intermediate stepping stone: under the canonical hypotheses we
prove it coincides with `canonicalIdeal` as an additive subgroup, and
it admits the obvious `ℤ`-basis used in the determinant computation. -/

/-- The `ℤ`-span of the two canonical generators
`{p^k · 1, p^(m-k) · (τ - A)}` inside `QuadraticOrder d`. -/
noncomputable def canonicalZSpan (d : ℤ) (p k m : ℕ) (A : ℤ) :
    Submodule ℤ (QuadraticOrder d) :=
  Submodule.span ℤ
    {(p : QuadraticOrder d) ^ k,
     (p : QuadraticOrder d) ^ (m - k) * (tau - (A : QuadraticOrder d))}

private lemma p_pow_k_mem_zSpan :
    (p : QuadraticOrder d) ^ k ∈ canonicalZSpan d p k m A :=
  Submodule.subset_span (Set.mem_insert _ _)

private lemma p_pow_mk_tau_sub_A_mem_zSpan :
    (p : QuadraticOrder d) ^ (m - k) * (tau - (A : QuadraticOrder d)) ∈
        canonicalZSpan d p k m A :=
  Submodule.subset_span (Set.mem_insert_of_mem _ rfl)

/-! ### τ-stability of the generators

These two identities are the arithmetic core: they exhibit
`τ · g` as an integer linear combination of the two generators, for
each generator `g`. The first needs only `m ≤ 2·k`; the second also
needs admissibility. -/

/-- `τ · p^k = A • (p^k) + p^(2k-m) • (p^(m-k)·(τ-A))` — a `ℤ`-linear
combination of the two generators, lying in `canonicalZSpan` provided
`m ≤ 2·k`. -/
private lemma tau_mul_p_pow_k_mem_zSpan
    (hk_hi : k ≤ m) (hk_lo : m ≤ 2 * k) :
    tau (d := d) * (p : QuadraticOrder d) ^ k ∈ canonicalZSpan d p k m A := by
  -- (2k - m) + (m - k) = k under k ≤ m ≤ 2k (using ℕ-subtractions).
  have hsplit : k = (2 * k - m) + (m - k) := by omega
  have hpow : (p : QuadraticOrder d) ^ k =
      (p : QuadraticOrder d) ^ (2 * k - m) *
        (p : QuadraticOrder d) ^ (m - k) := by
    rw [← pow_add, ← hsplit]
  have hrw : tau (d := d) * (p : QuadraticOrder d) ^ k =
      (A : ℤ) • ((p : QuadraticOrder d) ^ k) +
        ((p ^ (2 * k - m) : ℕ) : ℤ) •
          ((p : QuadraticOrder d) ^ (m - k) *
            (tau - (A : QuadraticOrder d))) := by
    rw [hpow, zsmul_eq_mul, zsmul_eq_mul]
    push_cast
    ring
  rw [hrw]
  exact Submodule.add_mem _
    (Submodule.smul_mem _ _ p_pow_k_mem_zSpan)
    (Submodule.smul_mem _ _ p_pow_mk_tau_sub_A_mem_zSpan)

/-- `τ · (p^(m-k) · (τ - A)) = (d - A) • (p^(m-k)·(τ - A)) + (-E) • (p^k)`,
where `E` is the admissibility witness. Lies in `canonicalZSpan` under
`k ≤ m ≤ 2·k` and admissibility. -/
private lemma tau_mul_p_pow_mk_tau_sub_A_mem_zSpan
    (hk_hi : k ≤ m) (hk_lo : m ≤ 2 * k)
    (hA : CanonicalAdmissible d p k m A) :
    tau (d := d) * ((p : QuadraticOrder d) ^ (m - k) *
        (tau - (A : QuadraticOrder d))) ∈
      canonicalZSpan d p k m A := by
  obtain ⟨E, hE⟩ := hA
  set q : ℤ := (d ^ 2 - d) / 4 with hq_def
  have hk_eq : (m - k) + (2 * k - m) = k := by omega
  -- `p^(m-k) · (A² - dA + q) = p^k · E` in `ℤ` (and hence in `QuadraticOrder d`).
  have hcoef_int :
      ((p : ℤ) ^ (m - k)) * (A ^ 2 - d * A + q) = ((p : ℤ) ^ k) * E := by
    rw [hE]
    rw [show ((p : ℤ) ^ (m - k)) * (((p : ℤ) ^ (2 * k - m)) * E) =
          (((p : ℤ) ^ (m - k)) * ((p : ℤ) ^ (2 * k - m))) * E by ring,
        ← pow_add, hk_eq]
  have hcoef : ((p : QuadraticOrder d) ^ (m - k)) *
      ((A : QuadraticOrder d) ^ 2 - (d : QuadraticOrder d) * (A : QuadraticOrder d) +
        ((q : ℤ) : QuadraticOrder d)) =
      ((p : QuadraticOrder d) ^ k) * ((E : ℤ) : QuadraticOrder d) := by
    have := congrArg (fun z : ℤ => (z : QuadraticOrder d)) hcoef_int
    push_cast at this
    exact this
  have hττ : tau (d := d) * tau =
      (d : QuadraticOrder d) * tau - ((q : ℤ) : QuadraticOrder d) := by
    have h := tau_minimal_poly (d := d)
    rw [show tau (d := d) * tau = tau ^ 2 by ring]
    have : tau (d := d) ^ 2 = (d : ℤ) • tau - q • (1 : QuadraticOrder d) := by
      rw [hq_def] at *; linear_combination h
    rw [this, zsmul_eq_mul, zsmul_eq_mul, mul_one]
  -- The key algebraic identity.
  have hrw : tau (d := d) * ((p : QuadraticOrder d) ^ (m - k) *
      (tau - (A : QuadraticOrder d))) =
        ((d - A : ℤ)) • ((p : QuadraticOrder d) ^ (m - k) *
          (tau - (A : QuadraticOrder d))) +
        ((-E : ℤ)) • (p : QuadraticOrder d) ^ k := by
    rw [zsmul_eq_mul, zsmul_eq_mul]
    push_cast
    linear_combination
      ((p : QuadraticOrder d) ^ (m - k)) * hττ - hcoef
  rw [hrw]
  exact Submodule.add_mem _
    (Submodule.smul_mem _ _ p_pow_mk_tau_sub_A_mem_zSpan)
    (Submodule.smul_mem _ _ p_pow_k_mem_zSpan)

/-! ### R-stability of the Z-span -/

/-- Multiplication by `τ` preserves the Z-span. -/
private lemma zSpan_tau_mul_mem
    (hk_hi : k ≤ m) (hk_lo : m ≤ 2 * k) (hA : CanonicalAdmissible d p k m A)
    {x : QuadraticOrder d} (hx : x ∈ canonicalZSpan d p k m A) :
    tau (d := d) * x ∈ canonicalZSpan d p k m A := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    rcases hy with rfl | rfl
    · exact tau_mul_p_pow_k_mem_zSpan hk_hi hk_lo
    · exact tau_mul_p_pow_mk_tau_sub_A_mem_zSpan hk_hi hk_lo hA
  | zero => rw [mul_zero]; exact Submodule.zero_mem _
  | add a b _ _ ha hb => rw [mul_add]; exact Submodule.add_mem _ ha hb
  | smul c y _ hy => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ hy

/-- Multiplication by any element of `QuadraticOrder d` preserves the
Z-span. Proof: the `c ∈ QO d` satisfying `c · (Z-span) ⊆ Z-span` form a
`ℤ`-submodule containing `1` and `τ`, hence all of `QO d`. -/
private lemma zSpan_smul_mem
    (hk_hi : k ≤ m) (hk_lo : m ≤ 2 * k) (hA : CanonicalAdmissible d p k m A)
    (c : QuadraticOrder d) {x : QuadraticOrder d}
    (hx : x ∈ canonicalZSpan d p k m A) :
    c * x ∈ canonicalZSpan d p k m A := by
  let M : Submodule ℤ (QuadraticOrder d) :=
    { carrier := {c | ∀ y ∈ canonicalZSpan d p k m A,
                        c * y ∈ canonicalZSpan d p k m A}
      zero_mem' := fun y _ => by simp
      add_mem' := fun ha hb y hy => by
        rw [add_mul]; exact Submodule.add_mem _ (ha y hy) (hb y hy)
      smul_mem' := fun a c hc y hy => by
        change (a • c) * y ∈ _
        rw [smul_mul_assoc]
        exact Submodule.smul_mem _ _ (hc y hy) }
  have hM_one : (1 : QuadraticOrder d) ∈ M := fun y hy => by rwa [one_mul]
  have hM_tau : tau (d := d) ∈ M := fun y hy =>
    zSpan_tau_mul_mem hk_hi hk_lo hA hy
  -- Every basis element of `QO d` is in `M`: `basis.gen = tau` by `rfl`.
  have basis_mem : ∀ i : Fin (basis (d := d)).dim, (basis (d := d)).basis i ∈ M := by
    intro i
    rw [PowerBasis.coe_basis]
    have hi2 : i.val < 2 := by rw [← basis_dim]; exact i.isLt
    interval_cases h : i.val
    · simp only [h, pow_zero]; exact hM_one
    · simp only [h, pow_one]; exact hM_tau
  -- Hence `c ∈ M` via `Basis.sum_repr`.
  suffices c ∈ M by exact this x hx
  have hsum := (basis (d := d)).basis.sum_repr c
  rw [← hsum]
  exact Submodule.sum_mem _ (fun i _ =>
    Submodule.smul_mem _ _ (basis_mem i))

/-! ### Canonical ideal = canonical Z-span (under admissibility) -/

/-- Under `k ≤ m ≤ 2·k` and admissibility, the underlying additive
subgroup of `canonicalIdeal` coincides with the Z-span of its
two generators. -/
lemma canonicalIdeal_eq_zSpan
    (hk_hi : k ≤ m) (hk_lo : m ≤ 2 * k) (hA : CanonicalAdmissible d p k m A) :
    (canonicalIdeal d p k m A).restrictScalars ℤ = canonicalZSpan d p k m A := by
  apply le_antisymm
  · -- canonicalIdeal ⊆ Z-span: induct on membership in `Ideal.span`.
    intro x hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      rcases hy with rfl | rfl
      · exact p_pow_k_mem_zSpan
      · exact p_pow_mk_tau_sub_A_mem_zSpan
    | zero => exact Submodule.zero_mem _
    | add a b _ _ ha hb => exact Submodule.add_mem _ ha hb
    | smul c y _ hy => exact zSpan_smul_mem hk_hi hk_lo hA c hy
  · -- Z-span ⊆ canonicalIdeal: the two generators are in canonicalIdeal.
    rw [canonicalZSpan, Submodule.span_le]
    rintro y (rfl | rfl)
    · exact Submodule.subset_span (Set.mem_insert _ _)
    · exact Submodule.subset_span (Set.mem_insert_of_mem _ rfl)

end QuadraticOrder
