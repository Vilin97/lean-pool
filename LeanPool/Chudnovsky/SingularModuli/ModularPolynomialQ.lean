/-
Copyright (c) 2026 Xuanji Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuanji Li
-/

import LeanPool.Chudnovsky.SingularModuli.CosetOrbit
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.LinearAlgebra.Matrix.FixedDetMatrices
import Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities
import Mathlib.RingTheory.Polynomial.Vieta

/-!
# The modular polynomial `Φ_m ∈ ℚ[X, Y]` (Phase C, chunks B3–B5)

Third file of Track 1 of Phase C (see `Playground/Pi/PhaseC-PLAN.md`, §3.1 sub-lemmas
`(B3)`–`(B5)`, §6.4). This is the **keystone** of the whole singular-moduli program: every
downstream statement funnels through the identity `Φ_m(X, j τ) = ∏_i (X − f_i τ)` with
`ℚ`-coefficients, and no route avoids it.

For a **prime** `m` (kept generic; `m ∈ {41, 43, 61, 163}` are instantiated later) the file
builds, from the `m`-isogeny coset orbit `f m i` of `CosetOrbit.lean`:

* **(A) Root-of-unity averaging** `sum_zetaM_zpow_mul`
  (`∑_{b : ZMod m} ζ^{b·n} = m·[m ∣ n]`), the arithmetic heart of `(B3)`: it kills every
  power of the base variable `w` that is not a genuine power of the nome `q = w^m`. Proved
  in full.
* **(B) Power sums** `powerSum m k τ = ∑_i (f m i τ)^k`: `SL(2,ℤ)`-invariance
  (`powerSum_smul`, from the `S`/`T`-permutations of the orbit) and holomorphy
  (`mdifferentiable_powerSum`). Proved in full. Likewise the orbit polynomial
  `orbitPoly m τ = ∏_i (X − f_i τ)` and the `SL(2,ℤ)`-invariance / holomorphy of its
  coefficients (the elementary symmetric functions of the orbit).
* **(B4/B5) The q-expansion principle** `Sk_eq_poly_j` (the critical lemma): an
  `SL(2,ℤ)`-invariant, holomorphic function that is *meromorphic of finite order at the
  cusp with coefficients in a subring `R ⊆ ℂ`* is a polynomial in `j` of bounded degree
  with `R`-coefficients. Proved by **pole-order induction with coefficient tracking**; the
  algebraic heart (leading-coefficient cancellation against `j^N`, coefficients staying in
  `R`) is unconditional, and the two genuinely-analytic primitives — the *removable
  singularity / pole-reduction* step and the *Liouville base case* (bounded + invariant +
  holomorphic ⇒ constant) — are **gated behind explicit hypotheses**, `Valence.lean`-style,
  with their routes documented. (See `PhaseC-PLAN.md` §6.4 / §6.6: the base case is the
  plan-sanctioned single gate.)
* **(B5) Assembly** `PhiQ`: gated on `Sk_eq_poly_j` + the `(B3)` q-expansion structure, the
  modular polynomial `Φ_m ∈ ℚ[X][Y]` with `Φ_m(X, j τ) = ∏_i (X − f_i τ)`.

## Status of the analytic gates (see `PhaseC-PLAN.md` §6.4)

`Sk_eq_poly_j` and `PhiQ` take the deep analytic facts as hypotheses rather than `sorry`.
The whole file is **sorry-free**. The gated pieces, with routes, are documented at their
`TODO` blocks:

1. `poleReduction` — the removable-singularity step: subtracting `c·j^N` from a pole-order-`N`
   cusp-meromorphic function yields a pole-order-`(N−1)` one. Route: the cusp function of
   `(h − c j^N)·q^N` is analytic at `0` with value `0`, hence `= w·(analytic)`, so dividing
   by one power of the nome stays bounded. Mathlib: `AnalyticAt`, `cuspFunction`, the
   `qExpansion` ring-hom API of `NumberTheory/ModularForms/QExpansion.lean`.
2. `liouvilleBaseCase` — bounded + `SL(2,ℤ)`-invariant + holomorphic ⇒ constant. Route
   (`PhaseC-PLAN.md` §6.4): descend to the disc via the cusp function, use
   `exists_smul_mem_fd_j` (from `Valence.lean`) to reduce every value to a compact truncation
   of the fundamental domain, and conclude via the open-mapping / clopen argument.
3. `(B3)` q-expansion structure of the power sums (the `w`-averaging producing the honest
   `q`-Laurent expansion with `ℚ`-coefficients and finite pole order) — the input to `PhiQ`,
   documented at `PhiQ`.
-/

noncomputable section

namespace Chudnovsky

open UpperHalfPlane Complex ModularForm Finset Polynomial
open scoped Real Manifold MatrixGroups

variable {m : ℕ}

/-! ## (A) Root-of-unity averaging

The clean arithmetic fact powering `(B3)`: summing `ζ^{b·n}` over `b : ZMod m` (with
`ζ = zetaM m = exp(2πi/m)`) gives `m` when `m ∣ n` and `0` otherwise. In the `w`-expansion
of the orbit this averages the coset variable `ζ^b·w` down to the honest nome `q = w^m`. -/

/-- Reindex a sum over `ZMod m` by `ZMod.val` to a sum over `Finset.range m`. -/
lemma sum_zmod_eq_range {M : Type*} [AddCommMonoid M] (m : ℕ) [NeZero m] (g : ℕ → M) :
    ∑ b : ZMod m, g b.val = ∑ k ∈ Finset.range m, g k := by
  apply Finset.sum_nbij' (fun b : ZMod m ↦ b.val) (fun k : ℕ ↦ (k : ZMod m))
  · intro b _; exact Finset.mem_range.mpr (ZMod.val_lt b)
  · intro k _; exact Finset.mem_univ _
  · intro b _; exact ZMod.natCast_rightInverse b
  · intro k hk; exact ZMod.val_natCast_of_lt (Finset.mem_range.mp hk)
  · intro b _; rfl

/-- `ζ^n = 1 ↔ m ∣ n` for `ζ = zetaM m` a primitive `m`-th root of unity. -/
lemma zetaM_zpow_eq_one_iff [NeZero m] (n : ℤ) : zetaM m ^ n = 1 ↔ (m : ℤ) ∣ n := by
  have hm : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne m)
  have hc : (2 * π * Complex.I) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have hpow : zetaM m ^ n = Complex.exp ((n : ℂ) * (2 * π * Complex.I / m)) := by
    rw [zetaM, ← Complex.exp_int_mul]
  rw [hpow, Complex.exp_eq_one_iff]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    have h2 : (n : ℂ) / m = (k : ℂ) := by
      apply mul_right_cancel₀ hc
      rw [← hk]; ring
    have h3 : (n : ℂ) = ((m * k : ℤ) : ℂ) := by
      rw [(div_eq_iff hm).mp h2]; push_cast; ring
    exact_mod_cast h3
  · rintro ⟨k, rfl⟩
    refine ⟨k, ?_⟩
    push_cast
    field_simp

/-- **Root-of-unity averaging** `∑_{b : ZMod m} ζ^{b·n} = m·[m ∣ n]`. The `ζ^{bn}` factor
is exactly the `b`-dependence of the `w`-expansion of the coset orbit (`hasSum_f_some`), so
this lemma is what makes the power sums have honest `q`-Laurent expansions in `(B3)`. -/
lemma sum_zetaM_zpow_mul [NeZero m] (n : ℤ) :
    ∑ b : ZMod m, zetaM m ^ ((b.val : ℤ) * n) = if (m : ℤ) ∣ n then (m : ℂ) else 0 := by
  have hval : ∀ b : ZMod m, zetaM m ^ ((b.val : ℤ) * n) = (zetaM m ^ n) ^ b.val := by
    intro b
    rw [mul_comm, zpow_mul, zpow_natCast]
  simp_rw [hval]
  rw [sum_zmod_eq_range m (fun k ↦ (zetaM m ^ n) ^ k)]
  by_cases hdvd : (m : ℤ) ∣ n
  · rw [ite_eq_left hdvd, (zetaM_zpow_eq_one_iff n).mpr hdvd]
    simp
  · rw [ite_eq_right hdvd]
    have hx1 : zetaM m ^ n ≠ 1 := fun h ↦ hdvd ((zetaM_zpow_eq_one_iff n).mp h)
    rw [geom_sum_eq hx1]
    have hxm : (zetaM m ^ n) ^ m = 1 := by
      rw [← zpow_natCast (zetaM m ^ n) m, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast,
        zetaM_pow_m, one_zpow]
    rw [hxm, sub_self, zero_div]

/-! ## `SL(2,ℤ)`-invariance from the `S`, `T` generators

A plain function `h : ℍ → ℂ` invariant under the two generators `S`, `T` is invariant under
all of `SL(2,ℤ)` — the invariant matrices form a subgroup containing the generators. -/

/-- If `h` is invariant under `S` and `T` then it is invariant under all of `SL(2,ℤ)`. -/
lemma invariant_of_S_T {h : ℍ → ℂ}
    (hS : ∀ τ : ℍ, h (ModularGroup.S • τ) = h τ)
    (hT : ∀ τ : ℍ, h (ModularGroup.T • τ) = h τ)
    (γ : SL(2, ℤ)) (τ : ℍ) : h (γ • τ) = h τ := by
  let H : Subgroup SL(2, ℤ) :=
    { carrier := {g | ∀ σ : ℍ, h (g • σ) = h σ}
      one_mem' := fun σ ↦ by rw [one_smul]
      mul_mem' := fun {a b} ha hb σ ↦ by rw [mul_smul, ha, hb]
      inv_mem' := fun {a} ha σ ↦ by
        have hh := ha (a⁻¹ • σ)
        rw [smul_inv_smul] at hh
        exact hh.symm }
  have hle : Subgroup.closure ({ModularGroup.S, ModularGroup.T} : Set SL(2, ℤ)) ≤ H := by
    rw [Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact hS
    · exact hT
  rw [SpecialLinearGroup.SL2Z_generators] at hle
  exact hle (Subgroup.mem_top γ) τ

/-! ## (B) Power sums of the orbit

`powerSum m k τ = ∑_i (f m i τ)^k`. Being a symmetric function of the `SL(2,ℤ)`-permuted
orbit, it is `SL(2,ℤ)`-invariant; being a finite sum of powers of the holomorphic `f_i`, it
is holomorphic. -/

/-- The `k`-th power sum `∑_i (f m i τ)^k` of the coset orbit. -/
def powerSum (m : ℕ) [NeZero m] (k : ℕ) (τ : ℍ) : ℂ := ∑ i : Option (ZMod m), (f m i τ) ^ k

/-- `T`-invariance of the power sums (from `sum_orbit_T_smul`). -/
lemma powerSum_T [NeZero m] (k : ℕ) (τ : ℍ) :
    powerSum m k (ModularGroup.T • τ) = powerSum m k τ := by
  rw [modular_T_smul]
  exact sum_orbit_T_smul (fun z ↦ z ^ k) τ

/-- `S`-invariance of the power sums (from `sum_orbit_S_smul`; needs `m` prime). -/
lemma powerSum_S [Fact m.Prime] (k : ℕ) (τ : ℍ) :
    powerSum m k (ModularGroup.S • τ) = powerSum m k τ := by
  have : NeZero m := ⟨(Fact.out : m.Prime).ne_zero⟩
  exact sum_orbit_S_smul (fun z ↦ z ^ k) τ

/-- **`SL(2,ℤ)`-invariance of the power sums.** -/
lemma powerSum_smul [Fact m.Prime] (k : ℕ) (γ : SL(2, ℤ)) (τ : ℍ) :
    powerSum m k (γ • τ) = powerSum m k τ :=
  invariant_of_S_T (powerSum_S k) (powerSum_T k) γ τ

/-- Each power sum is holomorphic on `ℍ`. -/
lemma mdifferentiable_powerSum [NeZero m] (k : ℕ) : MDiff (powerSum m k) := by
  have heq : powerSum m k = ∑ i : Option (ZMod m), (fun τ : ℍ ↦ (f m i τ) ^ k) := by
    funext τ; simp [powerSum, Finset.sum_apply]
  rw [heq]
  exact MDifferentiable.sum (fun i _ ↦ (mdifferentiable_f i).pow k)

/-! ## (B) The orbit polynomial `∏_i (X − f_i τ)`

The generating polynomial of the orbit; its coefficients are (up to sign) the elementary
symmetric functions of `{f_i τ}`, which are `SL(2,ℤ)`-invariant and holomorphic. -/

/-- The orbit polynomial `∏_i (X − f_i τ) ∈ ℂ[X]`. -/
def orbitPoly (m : ℕ) [NeZero m] (τ : ℍ) : Polynomial ℂ :=
  ∏ i : Option (ZMod m), (X - C (f m i τ))

/-- The orbit polynomial is monic of degree `m + 1`. -/
lemma orbitPoly_monic [NeZero m] (τ : ℍ) : (orbitPoly m τ).Monic :=
  monic_prod_X_sub_C _ _

/-- The orbit polynomial is `S`-invariant. -/
lemma orbitPoly_S [Fact m.Prime] (τ : ℍ) :
    orbitPoly m (ModularGroup.S • τ) = orbitPoly m τ :=
  prod_orbit_S_smul (fun z ↦ X - C z) τ

/-- The orbit polynomial is `T`-invariant. -/
lemma orbitPoly_T [NeZero m] (τ : ℍ) :
    orbitPoly m (ModularGroup.T • τ) = orbitPoly m τ := by
  rw [modular_T_smul]; exact prod_orbit_T_smul (fun z ↦ X - C z) τ

/-- **`SL(2,ℤ)`-invariance of every coefficient** of the orbit polynomial: the coset orbit is
permuted by `γ`, so the product `∏_i (X − f_i τ)` — and hence each coefficient (an elementary
symmetric function of the orbit) — is unchanged. -/
lemma orbitPoly_smul [Fact m.Prime] (γ : SL(2, ℤ)) (τ : ℍ) :
    orbitPoly m (γ • τ) = orbitPoly m τ := by
  have : NeZero m := ⟨(Fact.out : m.Prime).ne_zero⟩
  ext n
  refine invariant_of_S_T (h := fun σ ↦ (orbitPoly m σ).coeff n) ?_ ?_ γ τ
  · intro σ; rw [orbitPoly_S σ]
  · intro σ; rw [orbitPoly_T σ]

/-! ### Holomorphy of the elementary symmetric functions

Each coefficient of `∏_i (X − C (a i τ))` is a polynomial expression in the holomorphic
`a i τ`, hence holomorphic. Proved by induction on the index finset (all coefficients at
once). -/

/-- Every coefficient of a product `∏_{i ∈ s} (X − C (a i τ))` of monic linear factors with
holomorphic roots `a i` is a holomorphic function of `τ`. -/
lemma mdifferentiable_coeff_prod_X_sub_C {ι : Type*} (a : ι → ℍ → ℂ)
    (ha : ∀ i, MDiff (a i)) (s : Finset ι) :
    ∀ n : ℕ, MDiff (fun τ : ℍ ↦ ((∏ i ∈ s, (X - C (a i τ))).coeff n : ℂ)) := by
  classical
  induction s using Finset.induction with
  | empty =>
    intro n
    have hconst : (fun τ : ℍ ↦ ((∏ i ∈ (∅ : Finset ι), (X - C (a i τ))).coeff n : ℂ))
        = fun _ : ℍ ↦ (if n = 0 then (1 : ℂ) else 0) := by
      funext τ; simp [coeff_one]
    rw [hconst]
    exact mdifferentiable_const
  | insert j s hj ih =>
    intro n
    -- coefficient of a linear factor is holomorphic
    have hc : ∀ p : ℕ, MDiff (fun τ : ℍ ↦ ((X - C (a j τ)).coeff p : ℂ)) := by
      intro p
      have heq : (fun τ : ℍ ↦ ((X - C (a j τ)).coeff p : ℂ))
          = fun τ : ℍ ↦ ((if 1 = p then (1 : ℂ) else 0) - (if p = 0 then a j τ else 0)) := by
        funext τ; simp only [coeff_sub, coeff_X, coeff_C]
      rw [heq]
      have h1 : MDiff (fun _ : ℍ ↦ (if 1 = p then (1 : ℂ) else 0)) := mdifferentiable_const
      have h2 : MDiff (fun τ : ℍ ↦ (if p = 0 then a j τ else 0)) := by
        by_cases hp0 : p = 0
        · simp only [hp0, ite_true]; exact ha j
        · simp only [hp0, ite_false]; exact mdifferentiable_const
      exact h1.sub h2
    -- expand the product coefficient via `coeff_mul` into a Pi-sum of holomorphic terms
    have hexp : (fun τ : ℍ ↦ ((∏ i ∈ insert j s, (X - C (a i τ))).coeff n : ℂ))
        = ∑ x ∈ Finset.antidiagonal n,
            (fun τ : ℍ ↦ (X - C (a j τ)).coeff x.1 * (∏ i ∈ s, (X - C (a i τ))).coeff x.2) := by
      funext τ
      rw [Finset.prod_insert hj, coeff_mul, Finset.sum_apply]
    rw [hexp]
    exact MDifferentiable.sum (fun (x : ℕ × ℕ) _ ↦ (hc x.1).mul (ih x.2))

/-- Each coefficient of the orbit polynomial is a holomorphic function of `τ`. -/
lemma mdifferentiable_orbitPoly_coeff [NeZero m] (n : ℕ) :
    MDiff (fun τ : ℍ ↦ (orbitPoly m τ).coeff n) :=
  mdifferentiable_coeff_prod_X_sub_C (fun i ↦ f m i)
    (fun i ↦ mdifferentiable_f i) Finset.univ n

/-! ## (B4/B5) The q-expansion principle `Sk_eq_poly_j`

The critical lemma of the whole singular-moduli program (`PhaseC-PLAN.md` §6.4). It says:
an `SL(2,ℤ)`-invariant, holomorphic function that is *meromorphic of finite order at the
cusp with coefficients in a subring `R ⊆ ℂ`* equals a polynomial in `j` of bounded degree
with `R`-coefficients. The proof is a **pole-order downward induction with coefficient
tracking**: the leading Laurent coefficient `c` lies in `R`; since `j = q⁻¹(1 + 744q + …)`
is monic with integer q-expansion, `h − c·jᴺ` has strictly smaller pole order while keeping
`R`-coefficients; the base case `N = 0` is bounded + invariant + holomorphic, hence
constant (Liouville).

### Cusp-meromorphy data

We package "meromorphic at the cusp, pole order `≤ N`, coefficients in `R`" as the property
that `τ ↦ h τ · q τ ^ N` is a genuine holomorphic q-expansion function (`1`-periodic on the
disc side, holomorphic on `ℍ`, bounded at `i∞`) whose q-expansion has all coefficients in
`R`. Then `h = q⁻ᴺ · (that holomorphic function)` is exactly a Laurent series of pole order
`≤ N` with `R`-coefficients. -/

/-- `h` is *cusp-meromorphic of pole order `≤ N` with `R`-coefficients*: the product
`h · qᴺ` is a holomorphic function with a `q`-expansion whose coefficients all lie in the
subring `R ⊆ ℂ`. -/
structure IsCuspMeroR (h : ℍ → ℂ) (N : ℕ) (R : Subring ℂ) : Prop where
  periodic : Function.Periodic ((fun τ : ℍ ↦ h τ * q τ ^ N) ∘ ofComplex) 1
  holo : MDiff (fun τ : ℍ ↦ h τ * q τ ^ N)
  bdd : IsBoundedAtImInfty (fun τ : ℍ ↦ h τ * q τ ^ N)
  coeff_mem : ∀ n, (qExpansion 1 (fun τ : ℍ ↦ h τ * q τ ^ N)).coeff n ∈ R

/-- The leading Laurent coefficient of a cusp-meromorphic function of pole order `≤ N`:
the constant q-expansion coefficient of `h · qᴺ` (i.e. the coefficient of `q⁻ᴺ` in `h`). -/
def cuspLeadCoeff (h : ℍ → ℂ) (N : ℕ) : ℂ :=
  (qExpansion 1 (fun τ : ℍ ↦ h τ * q τ ^ N)).coeff 0

/-
TODO (analytic gate 1 — the Liouville base case; `PhaseC-PLAN.md` §6.4).

`liouvilleBaseCase` below is the plan-sanctioned base-case gate (`PhaseC-PLAN.md` §6.4): a
bounded, `SL(2,ℤ)`-invariant, holomorphic function on `ℍ` is constant. Route to discharge it:

  * `IsCuspMeroR h 0 R` gives that `h` itself is `1`-periodic, holomorphic and bounded at
    `i∞`, so its cusp function `H := cuspFunction 1 h` is analytic on the unit disc
    (`analyticAt_cuspFunction_zero`) and `h τ = H (q τ)` with `q τ → 0` at `i∞`.
  * `SL(2,ℤ)`-invariance + `exists_smul_mem_fd_j` (`Valence.lean`) reduce every value of `h`
    to the closed fundamental domain; splitting `𝒟` into the compact truncation
    `𝒟 ∩ {Im ≤ T}` and the cusp neighbourhood `{Im > T}` (where `h = H ∘ q` with `q` in a
    small disc), `h(ℍ)` is contained in a compact set.
  * If `h` were nonconstant, `H` would be a nonconstant analytic function, hence open
    (open-mapping theorem), so `H(disc)` — which contains `h(ℍ)` — would be open; a nonempty
    open *and* compact subset of the connected space `ℂ` is impossible. Hence `h` is constant,
    equal to its q-expansion constant term `= cuspLeadCoeff h 0 ∈ R`.

Mathlib assets: `analyticAt_cuspFunction_zero`, `cuspFunction_apply_zero`,
`AnalyticAt.eventually_eq_or_...`/open-mapping (`Analysis/Complex/OpenMapping`),
`ModularGroup.exists_smul_mem_fd`, compactness of the truncated fundamental domain.

TODO (analytic gate 2 — the pole-reduction / removable-singularity step).

`poleReduction` below states that subtracting `c · j^{N+1}` (with `c` the leading Laurent
coefficient) from a pole-order-`(N+1)` cusp-meromorphic function yields a pole-order-`N`
one, still with `R`-coefficients. Route: the cusp function of `(h − c·j^{N+1})·q^{N+1}`
equals `cuspFunction(h·q^{N+1}) − c·(jqInt)^{N+1}`-expansion, which is analytic at `0` with
value `c − c·1 = 0` (using `constantCoeff_jqInt = 1` from `JFunction.lean`); an analytic
germ vanishing at `0` is `w · (analytic)`, so dividing by one power of the nome keeps the
function bounded, giving `IsCuspMeroR … N R`. Coefficient tracking: the `q`-expansion of the
reduced `h·q^{N+1}` is `qExpansion(h·q^{N+1}) − c·(jqInt)^{N+1}` (a difference of `R`-series,
since `jqInt` has ℤ-coefficients and `ℤ ⊆ R`), and dividing by `X` shifts coefficients,
staying in `R`. Mathlib assets: the `qExpansion` ring-hom API (`qExpansion_mul`,
`qExpansion_sub`, `qExpansion_smul`) of `NumberTheory/ModularForms/QExpansion.lean`, and
`PowerSeries.X`-cancellation. This is the "coefficient-tracking" bookkeeping of §6.4.
-/

/-- **Liouville base case (analytic gate 1 — now discharged).** A holomorphic, `SL(2,ℤ)`-invariant
function on `ℍ` that is cusp-meromorphic of pole order `≤ 0` with `R`-coefficients (i.e.
`1`-periodic, holomorphic and bounded at `i∞`, its q-expansion having coefficients in `R`)
is **constant**, and its
value is the q-expansion constant term, which lies in `R`.

**Route** (maximum modulus, `PhaseC-PLAN.md` §6.4). Descend to the unit disc via the cusp function
`H := cuspFunction 1 h`, which is analytic on `Metric.ball 0 1`
(`differentiableOn_cuspFunction_ball`) and satisfies `H (q τ) = h τ` (`eq_cuspFunction`). By
`SL(2,ℤ)`-invariance and the fundamental-domain
reduction `ModularGroup.exists_smul_mem_fd`, every value `H z` on the punctured disc is *matched in
modulus* by a value `H w` with `‖w‖ ≤ e^{-π}`: the pre-image `τ` of `z ≠ 0` moves into `𝒟`, where
`3 ≤ 4·(Im)²` forces `Im ≥ 1/2` and hence `‖q‖ ≤ e^{-π}`. The maximum-modulus principle in the form
`Complex.eq_const_of_exists_le` then makes `H` constant on the whole disc, so `h τ = H 0`; and
`H 0 = (qExpansion 1 h).coeff 0 ∈ R` by `cuspFunction_apply_zero` / `qExpansion_coeff_zero`. -/
theorem liouvilleBaseCase (R : Subring ℂ) (h : ℍ → ℂ)
    (hinv : ∀ (γ : SL(2, ℤ)) (τ : ℍ), h (γ • τ) = h τ) (hholo : MDiff h)
    (hmero : IsCuspMeroR h 0 R) :
    ∃ c ∈ R, ∀ τ : ℍ, h τ = c := by
  -- `IsCuspMeroR h 0 R` is data about `h` itself (the `q⁰` factor is `1`)
  have hfun : (fun τ : ℍ ↦ h τ * q τ ^ 0) = h := by funext τ; rw [pow_zero, mul_one]
  have hper : Function.Periodic (h ∘ ofComplex) 1 := by
    have := hmero.periodic; rwa [hfun] at this
  have hbdd : IsBoundedAtImInfty h := by
    have := hmero.bdd; rwa [hfun] at this
  have hcoeff : (qExpansion 1 h).coeff 0 ∈ R := by
    have := hmero.coeff_mem 0; rwa [hfun] at this
  -- the cusp function `H = cuspFunction 1 h` and the identity `H (q τ) = h τ`
  have heqH : ∀ τ : ℍ, cuspFunction 1 h (q τ) = h τ := fun τ ↦
    eq_cuspFunction τ one_ne_zero hper
  have hanaAt : AnalyticAt ℂ (cuspFunction 1 h) 0 :=
    analyticAt_cuspFunction_zero one_pos hper hholo hbdd
  have hdiff : DifferentiableOn ℂ (cuspFunction 1 h) (Metric.ball 0 1) :=
    differentiableOn_cuspFunction_ball one_pos hper hholo hbdd
  -- radius data for the truncated fundamental domain
  have hr_nn : (0 : ℝ) ≤ Real.exp (-π) := (Real.exp_pos _).le
  have hr_lt : Real.exp (-π) < 1 := by
    rw [Real.exp_lt_one_iff]; exact neg_lt_zero.mpr Real.pi_pos
  -- the maximum-modulus hypothesis: every disc value is matched on `closedBall 0 e^{-π}`
  have hmax : ∀ z ∈ Metric.ball (0 : ℂ) 1, ∃ w ∈ Metric.closedBall (0 : ℂ) (Real.exp (-π)),
      ‖cuspFunction 1 h z‖ ≤ ‖cuspFunction 1 h w‖ := by
    intro z hz
    rw [mem_ball_zero_iff] at hz
    by_cases hz0 : z = 0
    · exact ⟨0, Metric.mem_closedBall_self hr_nn, le_of_eq (by rw [hz0])⟩
    · -- realise `z` as `q τ`, then reduce `τ` into the fundamental domain `𝒟`
      have him := Function.Periodic.im_invQParam_pos_of_norm_lt_one one_pos hz hz0
      have hqτ : q (UpperHalfPlane.mk (Function.Periodic.invQParam 1 z) him) = z := by
        change Function.Periodic.qParam 1
          ((UpperHalfPlane.mk (Function.Periodic.invQParam 1 z) him : ℍ) : ℂ) = z
        rw [UpperHalfPlane.coe_mk]
        exact Function.Periodic.qParam_right_inv one_ne_zero hz0
      set τ : ℍ := UpperHalfPlane.mk (Function.Periodic.invQParam 1 z) him
      obtain ⟨γ, hmem⟩ := ModularGroup.exists_smul_mem_fd τ
      refine ⟨q (γ • τ), ?_, ?_⟩
      · -- `Im (γ • τ) ≥ 1/2` in `𝒟`, hence `‖q (γ • τ)‖ ≤ e^{-π}`
        rw [mem_closedBall_zero_iff, norm_q]
        have him_half : (1 : ℝ) / 2 ≤ (γ • τ).im := by
          nlinarith [ModularGroup.three_le_four_mul_im_sq_of_mem_fd hmem, (γ • τ).im_pos]
        exact Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos, him_half])
      · -- moduli match: `‖H z‖ = ‖h τ‖ = ‖h (γ • τ)‖ = ‖H (q (γ • τ))‖`
        rw [← hqτ, heqH τ, heqH (γ • τ), hinv γ τ]
  -- maximum modulus principle: `H` is constant on the disc with value `H 0`
  have hconst := eq_const_of_exists_le hdiff hr_nn hr_lt hmax
  -- identify `H 0` with the `q`-expansion constant term (which lies in `R`)
  have hH0 : cuspFunction 1 h 0 = (qExpansion 1 h).coeff 0 := by
    rw [cuspFunction_apply_zero one_pos hanaAt hper, qExpansion_coeff_zero one_pos hanaAt hper]
  refine ⟨(qExpansion 1 h).coeff 0, hcoeff, fun τ ↦ ?_⟩
  have hzb : q τ ∈ Metric.ball (0 : ℂ) 1 := mem_ball_zero_iff.mpr (norm_q_lt_one τ)
  have hval := hconst hzb
  rw [Function.const_apply] at hval
  rw [← heqH τ, hval, hH0]

/-- **The q-expansion principle (critical lemma `Sk_eq_poly_j`), gated on the two analytic
primitives.** Any `SL(2,ℤ)`-invariant holomorphic function `h` that is cusp-meromorphic of
pole order `≤ N` with `R`-coefficients equals a polynomial in `j` of degree `≤ N` with all
coefficients in the subring `R`. The **pole-order downward induction with coefficient
tracking** is proved here in full; the two genuinely-analytic inputs — the Liouville base
case (`base`) and the removable-singularity pole-reduction step (`step`) — are taken as
hypotheses (see the `TODO` blocks above for their routes). -/
theorem Sk_eq_poly_j
    (base : ∀ (R : Subring ℂ) (h : ℍ → ℂ),
      (∀ (γ : SL(2, ℤ)) (τ : ℍ), h (γ • τ) = h τ) → MDiff h → IsCuspMeroR h 0 R →
        ∃ c ∈ R, ∀ τ : ℍ, h τ = c)
    (step : ∀ (N : ℕ) (R : Subring ℂ) (h : ℍ → ℂ),
      (∀ (γ : SL(2, ℤ)) (τ : ℍ), h (γ • τ) = h τ) → MDiff h → IsCuspMeroR h (N + 1) R →
        IsCuspMeroR (fun τ ↦ h τ - cuspLeadCoeff h (N + 1) * (j τ) ^ (N + 1)) N R) :
    ∀ (N : ℕ) (R : Subring ℂ) (h : ℍ → ℂ),
      (∀ (γ : SL(2, ℤ)) (τ : ℍ), h (γ • τ) = h τ) → MDiff h → IsCuspMeroR h N R →
      ∃ P : Polynomial ℂ, (∀ i, P.coeff i ∈ R) ∧ P.natDegree ≤ N ∧
        ∀ τ : ℍ, h τ = P.eval (j τ) := by
  intro N
  induction N with
  | zero =>
    intro R h hinv hholo hmero
    obtain ⟨c, hcR, hc⟩ := base R h hinv hholo hmero
    refine ⟨C c, ?_, ?_, ?_⟩
    · intro i
      rw [coeff_C]
      split
      · exact hcR
      · exact R.zero_mem
    · simp [natDegree_C]
    · intro τ; rw [hc τ, eval_C]
  | succ N ih =>
    intro R h hinv hholo hmero
    set c : ℂ := cuspLeadCoeff h (N + 1) with hc_def
    have hcR : c ∈ R := hmero.coeff_mem 0
    -- the reduced function `h' = h - c·j^{N+1}`
    set h' : ℍ → ℂ := fun τ ↦ h τ - c * (j τ) ^ (N + 1) with hh'_def
    have hinv' : ∀ (γ : SL(2, ℤ)) (τ : ℍ), h' (γ • τ) = h' τ := by
      intro γ τ
      simp only [hh'_def, hinv γ τ, j_smul γ τ]
    have hholo' : MDiff h' := by
      have : MDiff (fun τ : ℍ ↦ c * (j τ) ^ (N + 1)) :=
        mdifferentiable_const.mul (mdifferentiable_j.pow (N + 1))
      exact hholo.sub this
    have hmero' : IsCuspMeroR h' N R := step N R h hinv hholo hmero
    obtain ⟨P', hP'coeff, hP'deg, hP'eval⟩ := ih R h' hinv' hholo' hmero'
    -- assemble `P = P' + c·X^{N+1}`
    refine ⟨P' + C c * X ^ (N + 1), ?_, ?_, ?_⟩
    · intro i
      rw [coeff_add, coeff_C_mul, coeff_X_pow]
      refine R.add_mem (hP'coeff i) (R.mul_mem hcR ?_)
      split
      · exact R.one_mem
      · exact R.zero_mem
    · refine (natDegree_add_le _ _).trans ?_
      refine max_le (hP'deg.trans (Nat.le_succ N)) ?_
      refine (natDegree_mul_le).trans ?_
      simp [natDegree_C]
    · intro τ
      rw [eval_add, eval_mul, eval_C, eval_pow, eval_X, ← hP'eval τ]
      simp only [hh'_def]
      ring

/-- **The q-expansion principle with the Liouville base case discharged.** Since
`liouvilleBaseCase` closes the base-case gate of `Sk_eq_poly_j`, only the pole-reduction /
removable-singularity step `step` remains as a hypothesis: any `SL(2,ℤ)`-invariant holomorphic `h`
that is cusp-meromorphic of pole order `≤ N` with `R`-coefficients equals a degree-`≤ N` polynomial
in `j` with coefficients in `R`. -/
theorem Sk_eq_poly_j_of_step
    (step : ∀ (N : ℕ) (R : Subring ℂ) (h : ℍ → ℂ),
      (∀ (γ : SL(2, ℤ)) (τ : ℍ), h (γ • τ) = h τ) → MDiff h → IsCuspMeroR h (N + 1) R →
        IsCuspMeroR (fun τ ↦ h τ - cuspLeadCoeff h (N + 1) * (j τ) ^ (N + 1)) N R) :
    ∀ (N : ℕ) (R : Subring ℂ) (h : ℍ → ℂ),
      (∀ (γ : SL(2, ℤ)) (τ : ℍ), h (γ • τ) = h τ) → MDiff h → IsCuspMeroR h N R →
      ∃ P : Polynomial ℂ, (∀ i, P.coeff i ∈ R) ∧ P.natDegree ≤ N ∧
        ∀ τ : ℍ, h τ = P.eval (j τ) :=
  Sk_eq_poly_j liouvilleBaseCase step

/-! ## (B5) Assembly: the modular polynomial `Φ_m ∈ ℚ[X][Y]`

The `SL(2,ℤ)`-invariant coefficients of `orbitPoly m τ = ∏_i (X − f_i τ)` are the elementary
symmetric functions of the orbit. Feeding each (via Newton's identities from the power sums,
plus `Sk_eq_poly_j`) to the q-expansion principle expresses it as a `ℚ`-polynomial in `j`.
Packaging those `ℚ`-polynomials as the `Y`-coefficients yields `Φ_m ∈ ℚ[Y][X]` with the
defining identity `Φ_m(X, j τ) = ∏_i (X − f_i τ)`.

Here we deliver the **final packaging step** unconditionally: given the per-coefficient
`ℚ`-rationality (`hrat`, the output of `(B3)` + `Sk_eq_poly_j`), we build `Φ_m` and prove the
identity. -/

/-- Specialization of a `ℚ[Y][X]`-polynomial at `Y = Y₀ ∈ ℂ`: map each `ℚ[Y]`-coefficient to
its value at `Y₀`, landing in `ℂ[X]`. Applied at `Y₀ = j τ` this is `Φ_m(X, j τ)`. -/
def specializeY (Y₀ : ℂ) : Polynomial (Polynomial ℚ) →+* Polynomial ℂ :=
  Polynomial.mapRingHom (Polynomial.aeval Y₀).toRingHom

/-- The degree of the orbit polynomial is at most `m + 1` (it is the product of `m + 1`
linear factors). -/
lemma orbitPoly_natDegree_le [NeZero m] (τ : ℍ) : (orbitPoly m τ).natDegree ≤ m + 1 := by
  rw [orbitPoly]
  refine (natDegree_prod_le Finset.univ (fun i ↦ X - C (f m i τ))).trans ?_
  refine (Finset.sum_le_sum (fun i _ ↦ natDegree_X_sub_C_le (f m i τ))).trans ?_
  rw [Finset.sum_const, smul_eq_mul, mul_one, Finset.card_univ, Fintype.card_option, ZMod.card]

/-- **The modular polynomial `Φ_m ∈ ℚ[Y][X]`, assembled from the per-coefficient
`ℚ`-rationality.** Given that each coefficient of `∏_i (X − f_i τ)` is a `ℚ`-polynomial in
`j τ` (the output of `(B3)` + `Sk_eq_poly_j`), there is `Φ_m ∈ ℚ[Y][X]` with the keystone
identity `∏_i (X − f_i τ) = Φ_m(X, j τ)` for every `τ`. This is the object consumed by
`ModularPolynomialZ.lean` / `Rationality.lean` / `MasserA1.lean`. -/
theorem exists_PhiQ [Fact m.Prime]
    (hrat : ∀ n : ℕ, ∃ Q : Polynomial ℚ, ∀ τ : ℍ,
      (orbitPoly m τ).coeff n = (Polynomial.aeval (j τ)) Q) :
    ∃ PhiQ : Polynomial (Polynomial ℚ),
      ∀ τ : ℍ, orbitPoly m τ = specializeY (j τ) PhiQ := by
  have : NeZero m := ⟨(Fact.out : m.Prime).ne_zero⟩
  choose Q hQ using hrat
  refine ⟨∑ n ∈ Finset.range (m + 2), C (Q n) * X ^ n, ?_⟩
  -- coefficients of the packaged polynomial
  have hPcoeff : ∀ k : ℕ, (∑ n ∈ Finset.range (m + 2), C (Q n) * X ^ n).coeff k
      = if k < m + 2 then Q k else 0 := by
    intro k
    rw [finsetSum_coeff]
    simp only [coeff_C_mul, coeff_X_pow, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
      Finset.mem_range]
  intro τ
  ext k
  rw [specializeY, coe_mapRingHom, coeff_map, hPcoeff]
  by_cases hk : k < m + 2
  · rw [ite_eq_left hk]
    exact hQ k τ
  · rw [ite_eq_right hk, map_zero]
    exact coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (orbitPoly_natDegree_le τ) (by omega))

end Chudnovsky

/-! ## Analytic gate 2 (pole reduction): `poleReduction`

This appended section discharges the `step` hypothesis of `Sk_eq_poly_j` — the
removable-singularity / pole-order-reduction step. Given `h` cusp-meromorphic of pole order
`≤ N+1` with `R`-coefficients and leading Laurent coefficient `c = cuspLeadCoeff h (N+1)`, the
function `h − c·j^{N+1}` is cusp-meromorphic of pole order `≤ N` with `R`-coefficients.

The analytic heart is the general lemma `divByQ`: if `F` is a holomorphic `q`-expansion function
whose expansion has zero constant term, then `F/q` is again such a function, with `q`-expansion
coefficients shifted down by one (`dslope`/removable-singularity at the cusp). The algebraic heart
(`j·q` has integer `q`-expansion with leading coefficient `1`, so the `q^{-(N+1)}` term cancels and
all coefficients stay in `R`) is done via the `qExpansion` ring-hom API from `JFunction.lean`. -/

namespace Chudnovsky

open UpperHalfPlane Complex ModularForm EisensteinSeries Finset Polynomial
open scoped Real Manifold MatrixGroups

/-- Raw-function version of `qExpansion_coeff_unique`: if `cuspFunction 1 F` is analytic at `0`
and `F τ = ∑ c n · q τ ^ n` for all `τ`, then `c n` is the `n`-th `q`-expansion coefficient. -/
lemma qExpansion_coeff_unique_raw {F : ℍ → ℂ} {c : ℕ → ℂ}
    (hFan : AnalyticAt ℂ (cuspFunction 1 F) 0)
    (hFper : Function.Periodic (F ∘ ofComplex) 1) (hFholo : MDiff F)
    (hFbdd : IsBoundedAtImInfty F)
    (hF : ∀ τ : ℍ, HasSum (fun n ↦ c n • q τ ^ n) (F τ)) (n : ℕ) :
    c n = (qExpansion 1 F).coeff n := by
  have hball1 := hasFPowerSeriesOnBall_cuspFunction one_pos hFan hF
  have hsum2 : ∀ τ : ℍ, HasSum (fun m ↦ (qExpansion 1 F).coeff m • q τ ^ m) (F τ) :=
    hasSum_qExpansion one_pos hFper hFholo hFbdd
  have hball2 := hasFPowerSeriesOnBall_cuspFunction one_pos hFan hsum2
  have heq := hball1.hasFPowerSeriesAt.eq_formalMultilinearSeries hball2.hasFPowerSeriesAt
  have hcoeff := congr_arg (fun p : FormalMultilinearSeries ℂ ℂ ℂ ↦ p.coeff n) heq
  simpa [FormalMultilinearSeries.coeff_ofScalars] using hcoeff

/-- The cusp function of the constant function `1` is the constant function `1`. -/
lemma cuspFunction_one_eq : cuspFunction 1 (1 : ℍ → ℂ) = 1 := by
  ext w
  rcases eq_or_ne w 0 with rfl | hw
  · simpa [cuspFunction, Function.Periodic.cuspFunction]
      using! tendsto_const_nhds.limUnder_eq
  · simp [cuspFunction, Function.Periodic.cuspFunction_eq_of_nonzero 1 _ hw]

/-- Powers preserve cusp-analyticity, and the `q`-expansion of a power is the power of the
`q`-expansion. -/
lemma qExpansion_pow_of_analytic {F : ℍ → ℂ} (hF : AnalyticAt ℂ (cuspFunction 1 F) 0) :
    ∀ n : ℕ, AnalyticAt ℂ (cuspFunction 1 (F ^ n)) 0 ∧
      qExpansion 1 (F ^ n) = qExpansion 1 F ^ n := by
  intro n
  induction n with
  | zero =>
    refine ⟨?_, ?_⟩
    · rw [pow_zero, cuspFunction_one_eq]; exact analyticAt_const
    · rw [pow_zero, pow_zero, qExpansion_one]
  | succ n ih =>
    obtain ⟨ihan, ihq⟩ := ih
    have hcf : cuspFunction 1 (F ^ (n + 1)) = cuspFunction 1 (F ^ n) * cuspFunction 1 F := by
      rw [pow_succ F n]; exact cuspFunction_mul ihan.continuousAt hF.continuousAt
    refine ⟨?_, ?_⟩
    · rw [hcf]; exact ihan.mul hF
    · rw [pow_succ F n, qExpansion_mul ihan hF, ihq, pow_succ]

/-- **The pole-reduction primitive.** If `F` is `1`-periodic, holomorphic and bounded at `i∞`,
its `q`-expansion has zero constant term, and `G·q = F`, then `G` is bounded at `i∞` and its
`q`-expansion is that of `F` shifted down by one coefficient. Proof: `G τ = dslope (cuspFunction
1 F) 0 (q τ)`, which is analytic/continuous at `0` since `cuspFunction 1 F 0 = 0` (removable
singularity); boundedness follows by continuity, and the coefficient shift from the `HasSum`
expansion of `F` after dividing by `q`. -/
lemma divByQ {F G : ℍ → ℂ}
    (hFper : Function.Periodic (F ∘ ofComplex) 1) (hFholo : MDiff F)
    (hFbdd : IsBoundedAtImInfty F) (hF0 : (qExpansion 1 F).coeff 0 = 0)
    (hGper : Function.Periodic (G ∘ ofComplex) 1) (hGholo : MDiff G)
    (hGF : ∀ τ : ℍ, G τ * q τ = F τ) :
    IsBoundedAtImInfty G ∧ ∀ n, (qExpansion 1 G).coeff n = (qExpansion 1 F).coeff (n + 1) := by
  have hFan : AnalyticAt ℂ (cuspFunction 1 F) 0 :=
    analyticAt_cuspFunction_zero one_pos hFper hFholo hFbdd
  have hΦ0 : cuspFunction 1 F 0 = 0 := by
    rw [cuspFunction_apply_zero one_pos hFan hFper, ← qExpansion_coeff_zero one_pos hFan hFper]
    exact hF0
  have hqne : ∀ τ : ℍ, q τ ≠ 0 := fun τ ↦ by rw [q_eq]; exact Complex.exp_ne_zero _
  have hcf : ∀ τ : ℍ, cuspFunction 1 F (q τ) = F τ := fun τ ↦ eq_cuspFunction τ one_ne_zero hFper
  have hGeq : ∀ τ : ℍ, G τ = dslope (cuspFunction 1 F) 0 (q τ) := by
    intro τ
    rw [dslope_of_ne _ (hqne τ), slope_def_field, hΦ0, sub_zero, sub_zero, hcf τ,
      eq_div_iff (hqne τ)]
    exact hGF τ
  have hcont : ContinuousAt (dslope (cuspFunction 1 F) 0) 0 :=
    continuousAt_dslope_same.mpr hFan.differentiableAt
  have htendq : Filter.Tendsto (fun τ : ℍ ↦ q τ) atImInfty (nhds 0) :=
    qParam_tendsto_atImInfty one_pos
  have hGbdd : IsBoundedAtImInfty G := by
    have htendG : Filter.Tendsto G atImInfty (nhds (dslope (cuspFunction 1 F) 0 0)) := by
      rw [funext hGeq]; exact hcont.tendsto.comp htendq
    exact htendG.isBigO_one ℝ
  refine ⟨hGbdd, ?_⟩
  have hGan : AnalyticAt ℂ (cuspFunction 1 G) 0 :=
    analyticAt_cuspFunction_zero one_pos hGper hGholo hGbdd
  intro n
  have hFsum : ∀ τ : ℍ, HasSum (fun m ↦ (qExpansion 1 F).coeff m • q τ ^ m) (F τ) :=
    hasSum_qExpansion one_pos hFper hFholo hFbdd
  have hGsum : ∀ τ : ℍ,
      HasSum (fun k ↦ (qExpansion 1 F).coeff (k + 1) • q τ ^ k) (G τ) := by
    intro τ
    have h1 : HasSum (fun k ↦ (qExpansion 1 F).coeff (k + 1) • q τ ^ (k + 1)) (F τ) := by
      have hraw := (hasSum_nat_add_iff' 1).mpr (hFsum τ)
      simpa [Finset.sum_range_one, hF0] using hraw
    have h2 := h1.mul_right (q τ)⁻¹
    have hsimp : (fun k ↦ ((qExpansion 1 F).coeff (k + 1) • q τ ^ (k + 1)) * (q τ)⁻¹)
        = fun k ↦ (qExpansion 1 F).coeff (k + 1) • q τ ^ k := by
      funext k
      rw [smul_mul_assoc, pow_succ, mul_assoc, mul_inv_cancel₀ (hqne τ), mul_one]
    rw [hsimp] at h2
    have hFG : F τ * (q τ)⁻¹ = G τ := by
      rw [← hGF τ, mul_assoc, mul_inv_cancel₀ (hqne τ), mul_one]
    rwa [hFG] at h2
  exact (qExpansion_coeff_unique_raw hGan hGper hGholo hGbdd hGsum n).symm

/-- `j·q = E₄³ · (∏ₙ (1 − qⁿ)²⁴)⁻¹` : the simple pole of `j` is cancelled by the zero of `q`
(reconstructed from `discriminant_eq_q_prod` and `j_mul_discriminant`, all public). -/
private lemma jq_eq_inv_recon (τ : ℍ) :
    j τ * q τ = E₄ τ ^ 3 * (∏' n : ℕ, (1 - eta_q n ↑τ) ^ 24)⁻¹ := by
  have hΔ : discriminant τ = q τ * ∏' n : ℕ, (1 - eta_q n ↑τ) ^ 24 := discriminant_eq_q_prod τ
  have hP0 : (∏' n : ℕ, (1 - eta_q n ↑τ) ^ 24) ≠ 0 := fun h0 ↦
    discriminant_ne_zero τ (by rw [hΔ, h0, mul_zero])
  rw [eq_mul_inv_iff_mul_eq₀ hP0, mul_assoc, ← hΔ]
  exact j_mul_discriminant τ

/-- `j·q` is bounded at the cusp (it tends to `1`). -/
private lemma isBoundedAtImInfty_jq_recon : IsBoundedAtImInfty (fun τ : ℍ ↦ j τ * q τ) := by
  have heq : (fun τ : ℍ ↦ j τ * q τ)
      = ⇑E₄ * (⇑E₄ * (⇑E₄ * fun τ : ℍ ↦ (∏' n : ℕ, (1 - eta_q n ↑τ) ^ 24)⁻¹)) := by
    funext τ
    simp only [Pi.mul_apply]
    rw [jq_eq_inv_recon τ]
    ring
  rw [heq]
  have hE : IsBoundedAtImInfty ⇑E₄ := ModularFormClass.bdd_at_infty E₄
  have hPinv : Filter.Tendsto (fun τ : ℍ ↦ (∏' n : ℕ, (1 - eta_q n ↑τ) ^ 24)⁻¹)
      atImInfty (nhds 1) := by
    simpa using tendsto_atImInfty_tprod_one_sub_eta_q_pow.inv₀ one_ne_zero
  have hPb : IsBoundedAtImInfty (fun τ : ℍ ↦ (∏' n : ℕ, (1 - eta_q n ↑τ) ^ 24)⁻¹) :=
    hPinv.isBigO_one ℝ
  exact Filter.BoundedAtFilter.mul hE (Filter.BoundedAtFilter.mul hE
    (Filter.BoundedAtFilter.mul hE hPb))

private lemma periodic_jq_recon :
    Function.Periodic ((fun τ : ℍ ↦ j τ * q τ) ∘ ofComplex) 1 :=
  periodic_comp_ofComplex_of_vadd (fun τ ↦ by rw [j_vadd_one, q_vadd_one])

private lemma analyticAt_cuspFunction_jq_recon :
    AnalyticAt ℂ (cuspFunction 1 (fun τ : ℍ ↦ j τ * q τ)) 0 :=
  analyticAt_cuspFunction_zero one_pos periodic_jq_recon mdifferentiable_j_mul_q
    isBoundedAtImInfty_jq_recon

/-- Every power of `j·q` is bounded at the cusp. -/
private lemma isBoundedAtImInfty_jq_pow (n : ℕ) :
    IsBoundedAtImInfty (fun τ : ℍ ↦ (j τ * q τ) ^ n) := by
  induction n with
  | zero =>
    simp only [pow_zero]
    exact Filter.const_boundedAtFilter atImInfty (1 : ℂ)
  | succ n ih =>
    have hmul : (fun τ : ℍ ↦ (j τ * q τ) ^ (n + 1))
        = (fun τ : ℍ ↦ (j τ * q τ) ^ n) * (fun τ : ℍ ↦ j τ * q τ) := by
      funext τ; simp [pow_succ]
    rw [hmul]
    exact Filter.BoundedAtFilter.mul ih isBoundedAtImInfty_jq_recon

/-- **Analytic gate 2 — the pole-reduction step of `Sk_eq_poly_j`.** Subtracting the leading
Laurent term `c·j^{N+1}` (with `c = cuspLeadCoeff h (N+1)`) from a pole-order-`(N+1)`
cusp-meromorphic function of `R`-coefficients yields a pole-order-`N` one, still with
`R`-coefficients. This closes the `step` hypothesis of `Sk_eq_poly_j`. -/
theorem poleReduction (N : ℕ) (R : Subring ℂ) (h : ℍ → ℂ)
    (hinv : ∀ (γ : SL(2, ℤ)) (τ : ℍ), h (γ • τ) = h τ) (hholo : MDiff h)
    (hmero : IsCuspMeroR h (N + 1) R) :
    IsCuspMeroR (fun τ ↦ h τ - cuspLeadCoeff h (N + 1) * (j τ) ^ (N + 1)) N R := by
  set c : ℂ := cuspLeadCoeff h (N + 1) with hc_def
  have hcR : c ∈ R := hmero.coeff_mem 0
  -- `T`-periodicity of `h`
  have hhvadd : ∀ τ : ℍ, h ((1 : ℝ) +ᵥ τ) = h τ := by
    intro τ
    have := hinv ModularGroup.T τ
    rwa [modular_T_smul] at this
  -- analytic data for `g = h·q^{N+1}` and `(j·q)^{N+1}`
  have gan : AnalyticAt ℂ (cuspFunction 1 (fun τ : ℍ ↦ h τ * q τ ^ (N + 1))) 0 :=
    analyticAt_cuspFunction_zero one_pos hmero.periodic hmero.holo hmero.bdd
  have jq_an : AnalyticAt ℂ (cuspFunction 1 (fun τ : ℍ ↦ j τ * q τ)) 0 :=
    analyticAt_cuspFunction_jq_recon
  have hJpeq : (fun τ : ℍ ↦ (j τ * q τ) ^ (N + 1)) = (fun τ : ℍ ↦ j τ * q τ) ^ (N + 1) := by
    funext τ; simp only [Pi.pow_apply]
  have hpow := qExpansion_pow_of_analytic jq_an (N + 1)
  rw [← hJpeq] at hpow
  obtain ⟨jqpow_an, hjqpow_qexp⟩ := hpow
  rw [qExpansion_j_mul_q] at hjqpow_qexp
  -- decomposition `F = g − c·(j·q)^{N+1}`
  have hFdecomp : (fun τ : ℍ ↦ (h τ - c * (j τ) ^ (N + 1)) * q τ ^ (N + 1))
      = (fun τ : ℍ ↦ h τ * q τ ^ (N + 1)) - c • (fun τ : ℍ ↦ (j τ * q τ) ^ (N + 1)) := by
    funext τ
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hcsmul_an : AnalyticAt ℂ (cuspFunction 1 (c • (fun τ : ℍ ↦ (j τ * q τ) ^ (N + 1)))) 0 := by
    rw [cuspFunction_smul jqpow_an.continuousAt]
    exact jqpow_an.const_smul
  have hFqexp : qExpansion 1 (fun τ : ℍ ↦ (h τ - c * (j τ) ^ (N + 1)) * q τ ^ (N + 1))
      = qExpansion 1 (fun τ : ℍ ↦ h τ * q τ ^ (N + 1))
        - c • (PowerSeries.map (Int.castRingHom ℂ) jqInt) ^ (N + 1) := by
    rw [hFdecomp, qExpansion_sub gan hcsmul_an, qExpansion_smul jqpow_an c, hjqpow_qexp]
  -- leading-coefficient facts
  have hcoeffA0 : PowerSeries.coeff 0 (qExpansion 1 (fun τ : ℍ ↦ h τ * q τ ^ (N + 1))) = c := by
    rw [hc_def]; rfl
  have hmap0 : PowerSeries.constantCoeff (PowerSeries.map (Int.castRingHom ℂ) jqInt) = 1 := by
    have := j_mul_q_qExpansion_coeff_zero
    rwa [qExpansion_j_mul_q, PowerSeries.coeff_zero_eq_constantCoeff_apply] at this
  have hcoeffJ0 :
      PowerSeries.coeff 0 ((PowerSeries.map (Int.castRingHom ℂ) jqInt) ^ (N + 1)) = 1 := by
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, map_pow, hmap0, one_pow]
  -- the `F`-side hypotheses of `divByQ`
  have hFper : Function.Periodic
      ((fun τ : ℍ ↦ (h τ - c * (j τ) ^ (N + 1)) * q τ ^ (N + 1)) ∘ ofComplex) 1 :=
    periodic_comp_ofComplex_of_vadd (fun τ ↦ by
      simp only [hhvadd, j_vadd_one, q_vadd_one])
  have hh'holo : MDiff (fun τ : ℍ ↦ h τ - c * (j τ) ^ (N + 1)) :=
    hholo.sub (mdifferentiable_const.mul (mdifferentiable_j.pow (N + 1)))
  have hFholo : MDiff (fun τ : ℍ ↦ (h τ - c * (j τ) ^ (N + 1)) * q τ ^ (N + 1)) :=
    hh'holo.mul (mdifferentiable_q.pow (N + 1))
  have hFbdd : IsBoundedAtImInfty
      (fun τ : ℍ ↦ (h τ - c * (j τ) ^ (N + 1)) * q τ ^ (N + 1)) := by
    rw [hFdecomp, sub_eq_add_neg]
    exact hmero.bdd.add ((isBoundedAtImInfty_jq_pow (N + 1)).smul c).neg
  have hF0 : (qExpansion 1
      (fun τ : ℍ ↦ (h τ - c * (j τ) ^ (N + 1)) * q τ ^ (N + 1))).coeff 0 = 0 := by
    rw [hFqexp, map_sub, PowerSeries.coeff_smul, hcoeffJ0, hcoeffA0]
    simp
  -- the `G`-side hypotheses of `divByQ`
  have hGper : Function.Periodic
      ((fun τ : ℍ ↦ (h τ - c * (j τ) ^ (N + 1)) * q τ ^ N) ∘ ofComplex) 1 :=
    periodic_comp_ofComplex_of_vadd (fun τ ↦ by
      simp only [hhvadd, j_vadd_one, q_vadd_one])
  have hGholo : MDiff (fun τ : ℍ ↦ (h τ - c * (j τ) ^ (N + 1)) * q τ ^ N) :=
    hh'holo.mul (mdifferentiable_q.pow N)
  have hGF : ∀ τ : ℍ,
      (fun τ : ℍ ↦ (h τ - c * (j τ) ^ (N + 1)) * q τ ^ N) τ * q τ
        = (fun τ : ℍ ↦ (h τ - c * (j τ) ^ (N + 1)) * q τ ^ (N + 1)) τ := by
    intro τ
    change (h τ - c * (j τ) ^ (N + 1)) * q τ ^ N * q τ
      = (h τ - c * (j τ) ^ (N + 1)) * q τ ^ (N + 1)
    rw [mul_assoc, ← pow_succ]
  obtain ⟨hGbdd, hGcoeff⟩ := divByQ hFper hFholo hFbdd hF0 hGper hGholo hGF
  -- assemble the reduced cusp-meromorphy datum
  refine ⟨hGper, hGholo, hGbdd, fun n ↦ ?_⟩
  have hc := hGcoeff n
  rw [hFqexp] at hc
  rw [hc, map_sub, PowerSeries.coeff_smul, smul_eq_mul]
  refine R.sub_mem (hmero.coeff_mem (n + 1)) (R.mul_mem hcR ?_)
  rw [← map_pow, PowerSeries.coeff_map, eq_intCast (Int.castRingHom ℂ)]
  exact intCast_mem R _

/-- **The q-expansion principle, fully unconditional.** Both analytic gates of `Sk_eq_poly_j`
are now discharged — the Liouville base case (`liouvilleBaseCase`) and the pole-reduction step
(`poleReduction`) — so an `SL(2,ℤ)`-invariant holomorphic `h` that is cusp-meromorphic of pole
order `≤ N` with `R`-coefficients equals a degree-`≤ N` polynomial in `j` with `R`-coefficients,
with no remaining hypotheses. -/
theorem Sk_eq_poly_j_closed :
    ∀ (N : ℕ) (R : Subring ℂ) (h : ℍ → ℂ),
      (∀ (γ : SL(2, ℤ)) (τ : ℍ), h (γ • τ) = h τ) → MDiff h → IsCuspMeroR h N R →
      ∃ P : Polynomial ℂ, (∀ i, P.coeff i ∈ R) ∧ P.natDegree ≤ N ∧
        ∀ τ : ℍ, h τ = P.eval (j τ) :=
  Sk_eq_poly_j liouvilleBaseCase poleReduction

/-! ## (B3) The power sums are cusp-meromorphic with `ℚ`-coefficients

This appended section discharges the last remaining gate of the keystone: the `hrat` input of
`exists_PhiQ`. For a **prime** `m`, every power sum `powerSum m k` is `SL(2,ℤ)`-invariant,
holomorphic and cusp-meromorphic of pole order `≤ m·k` with `ℚ` (indeed `ℤ`)-coefficients, hence
(via `Sk_eq_poly_j_closed`) a `ℚ`-polynomial in `j`. Newton's identities then push this to the
elementary symmetric functions (the orbit-polynomial coefficients), delivering the unconditional
keystone `exists_PhiQ_closed`.

The analytic heart is the **root-of-unity averaging** `sum_zetaM_zpow_mul`: writing each orbit
value's `q`-expansion in the honest base variable `w = wParam m τ` (with `w^m = q τ`), the
coset points contribute `w`-powers `ζ^{b·n}` whose `b`-sum collapses to a genuine `q`-Laurent
series. -/

variable {m : ℕ}

/-- The subring `ℚ ⊆ ℂ` (image of the rational cast). -/
def RQ : Subring ℂ := (Rat.castHom ℂ).range

lemma intCast_mem_RQ (n : ℤ) : (n : ℂ) ∈ RQ := intCast_mem RQ n

/-- `w^{m²·k} = q^{m·k}`: the top `w`-power equals the `q`-power that clears the pole. -/
lemma wParam_pow_mk [NeZero m] (k : ℕ) (τ : ℍ) :
    wParam m τ ^ (m ^ 2 * k) = q τ ^ (m * k) := by
  rw [show m ^ 2 * k = m * (m * k) by ring, pow_mul, wParam_pow_m]

/-- **Per-point `k`-fold `q`-expansion of `j·q`.** For any `σ : ℍ`,
`(j σ · q σ)^k = ∑ₙ (jqInt^k)ₙ · q σ ^ n` with the integer coefficients of `jqInt^k`. -/
lemma hasSum_jqPow_at (k : ℕ) (σ : ℍ) :
    HasSum (fun n : ℕ ↦ ((PowerSeries.coeff n (jqInt ^ k) : ℤ) : ℂ) * q σ ^ n)
      ((j σ * q σ) ^ k) := by
  have hper : Function.Periodic (((fun τ : ℍ ↦ j τ * q τ) ^ k) ∘ ofComplex) 1 :=
    periodic_comp_ofComplex_of_vadd (fun τ ↦ by
      simp only [Pi.pow_apply, j_vadd_one, q_vadd_one])
  have hholo : MDiff ((fun τ : ℍ ↦ j τ * q τ) ^ k) := mdifferentiable_j_mul_q.pow k
  have hbdd : IsBoundedAtImInfty ((fun τ : ℍ ↦ j τ * q τ) ^ k) := isBoundedAtImInfty_jq_pow k
  have hqe : qExpansion 1 ((fun τ : ℍ ↦ j τ * q τ) ^ k)
      = PowerSeries.map (Int.castRingHom ℂ) (jqInt ^ k) := by
    rw [(qExpansion_pow_of_analytic analyticAt_cuspFunction_jq_recon k).2, qExpansion_j_mul_q,
      map_pow]
  have h := hasSum_qExpansion one_pos hper hholo hbdd σ
  rw [hqe] at h
  simpa only [Pi.pow_apply, PowerSeries.coeff_map, eq_intCast, smul_eq_mul, q] using h

/-- `‖wParam m τ‖ ≤ 1` (since `‖wParam‖^m = ‖q τ‖ < 1`). -/
lemma norm_wParam_le_one [NeZero m] (τ : ℍ) : ‖wParam m τ‖ ≤ 1 := by
  have hm : m ≠ 0 := NeZero.ne m
  rw [← pow_le_one_iff_of_nonneg (norm_nonneg _) hm, ← norm_pow, wParam_pow_m]
  exact (norm_q_lt_one τ).le

/-- `‖zetaM m‖ = 1` (a root of unity). -/
lemma norm_zetaM_eq_one [NeZero m] : ‖zetaM m‖ = 1 := by
  have hm : m ≠ 0 := NeZero.ne m
  have h : ‖zetaM m‖ ^ m = 1 := by rw [← norm_pow, zetaM_pow_m, norm_one]
  refine le_antisymm ?_ ?_
  · rw [← pow_le_one_iff_of_nonneg (norm_nonneg _) hm, h]
  · rw [← one_le_pow_iff_of_nonneg (norm_nonneg _) hm, h]

/-- `‖gB‖ ≤ 1`, where `gB` is the bounded multiplier appearing in the `some b` orbit term. -/
lemma norm_gB_le_one [NeZero m] (k : ℕ) (b : ZMod m) (τ : ℍ) :
    ‖zetaM m ^ (-(↑b.val * ↑k : ℤ)) * wParam m τ ^ ((m ^ 2 - 1) * k)‖ ≤ 1 := by
  rw [norm_mul, norm_zpow, norm_pow, norm_zetaM_eq_one, one_zpow, one_mul]
  exact pow_le_one₀ (norm_nonneg _) (norm_wParam_le_one τ)

/-- The `none` orbit term of `powerSum·q^{mk}` is `(j·q)ᵏ` composed with the isogeny `τ ↦ m·τ`. -/
lemma Fi_none_eq [NeZero m] (k : ℕ) (τ : ℍ) :
    (f m none τ) ^ k * q τ ^ (m * k) = (j (AInf m • τ) * q (AInf m • τ)) ^ k := by
  rw [f_none, mul_pow, q_AInf_smul, ← pow_mul, wParam_pow_mk]

/-- The `some b` orbit term of `powerSum·q^{mk}` factors as `(j·q)ᵏ∘(coset) · gB` with `‖gB‖≤1`. -/
lemma Fi_some_eq [NeZero m] (k : ℕ) (b : ZMod m) (τ : ℍ) :
    (f m (some b) τ) ^ k * q τ ^ (m * k)
      = (j (Acol m b.val • τ) * q (Acol m b.val • τ)) ^ k
        * (zetaM m ^ (-(↑b.val * ↑k : ℤ)) * wParam m τ ^ ((m ^ 2 - 1) * k)) := by
  have hz : zetaM m ≠ 0 := zetaM_ne_zero
  rw [f_some, ← wParam_pow_mk k τ, q_Acol_smul]
  have key : wParam m τ ^ (m ^ 2 * k)
      = (zetaM m ^ (↑b.val : ℤ) * wParam m τ) ^ k
        * (zetaM m ^ (-(↑b.val * ↑k : ℤ)) * wParam m τ ^ ((m ^ 2 - 1) * k)) := by
    rw [mul_pow, show (zetaM m ^ (↑b.val : ℤ)) ^ k = zetaM m ^ ((↑b.val : ℤ) * ↑k) from by
        rw [← zpow_natCast (zetaM m ^ (↑b.val : ℤ)) k, ← zpow_mul], mul_mul_mul_comm,
      ← zpow_add₀ hz, add_neg_cancel, zpow_zero, one_mul, ← pow_add]
    congr 1
    have hM : 1 ≤ m ^ 2 := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero 2 (NeZero.ne m))
    have hk : k ≤ m ^ 2 * k := Nat.le_mul_of_pos_left k (by omega)
    rw [Nat.sub_one_mul]; omega
  rw [mul_pow, key]; ring

/-- A function bounded by `1` in norm is bounded at `i∞`. -/
lemma isBoundedAtImInfty_of_norm_le_one {g : ℍ → ℂ} (hg : ∀ τ, ‖g τ‖ ≤ 1) :
    IsBoundedAtImInfty g :=
  Asymptotics.isBigO_of_le atImInfty (fun τ ↦ by simpa using hg τ)

/-- `(j·q)ᵏ` composed with an upper-triangular isogeny `A` (lower-left entry `0`) is bounded at
`i∞`, since the isogeny pushes towards the cusp. -/
lemma isBoundedAtImInfty_jqPow_comp (k : ℕ) (A : GL (Fin 2) ℝ) (hA : A 1 0 = 0) :
    IsBoundedAtImInfty (fun τ : ℍ ↦ (j (A • τ) * q (A • τ)) ^ k) := by
  have hb : (fun σ : ℍ ↦ (j σ * q σ) ^ k) =O[atImInfty] (1 : ℍ → ℝ) := isBoundedAtImInfty_jq_pow k
  have ht : Filter.Tendsto (fun τ : ℍ ↦ A • τ) atImInfty atImInfty := tendsto_smul_atImInfty hA
  change (fun τ : ℍ ↦ (j (A • τ) * q (A • τ)) ^ k) =O[atImInfty] (fun _ : ℍ ↦ (1 : ℝ))
  have h := hb.comp_tendsto ht
  simpa only [Function.comp_def, Pi.one_apply] using h

/-- **Boundedness at the cusp.** `powerSum m k · q^{mk}` is bounded at `i∞`: each orbit term is a
bounded `(j·q)ᵏ`-value (composed with an isogeny) times a factor of norm `≤ 1`. -/
lemma isBoundedAtImInfty_powerSum_mul_qpow [Fact m.Prime] (k : ℕ) :
    IsBoundedAtImInfty (fun τ : ℍ ↦ powerSum m k τ * q τ ^ (m * k)) := by
  have : NeZero m := ⟨(Fact.out : m.Prime).ne_zero⟩
  have hsum : (fun τ : ℍ ↦ powerSum m k τ * q τ ^ (m * k))
      = ∑ i : Option (ZMod m), (fun τ : ℍ ↦ (f m i τ) ^ k * q τ ^ (m * k)) := by
    funext τ; simp only [powerSum, Finset.sum_apply, Finset.sum_mul]
  rw [hsum]
  refine (Filter.boundedFilterSubalgebra ℂ atImInfty).sum_mem (fun i _ ↦ ?_)
  cases i with
  | none =>
    change IsBoundedAtImInfty (fun τ : ℍ ↦ (f m none τ) ^ k * q τ ^ (m * k))
    rw [funext (fun τ ↦ Fi_none_eq k τ)]
    have hAI : (AInf m) 1 0 = 0 := by simp [val_AInf]
    exact isBoundedAtImInfty_jqPow_comp k (AInf m) hAI
  | some b =>
    change IsBoundedAtImInfty (fun τ : ℍ ↦ (f m (some b) τ) ^ k * q τ ^ (m * k))
    have heq : (fun τ : ℍ ↦ (f m (some b) τ) ^ k * q τ ^ (m * k))
        = (fun τ : ℍ ↦ (j (Acol m b.val • τ) * q (Acol m b.val • τ)) ^ k)
          * (fun τ : ℍ ↦ zetaM m ^ (-(↑b.val * ↑k : ℤ)) * wParam m τ ^ ((m ^ 2 - 1) * k)) := by
      funext τ; simp only [Pi.mul_apply]; exact Fi_some_eq k b τ
    have hAc : (Acol m b.val) 1 0 = 0 := by simp [val_Acol]
    rw [heq]
    exact Filter.BoundedAtFilter.mul (isBoundedAtImInfty_jqPow_comp k (Acol m b.val) hAc)
      (isBoundedAtImInfty_of_norm_le_one (fun τ ↦ norm_gB_le_one k b τ))

/-! ### The averaging: `q`-series of the `some b` orbit terms -/

/-- The summand identity feeding the root-of-unity average: the `n`-th term of the `some b`
orbit `q`-expansion, rewritten so the `b`-dependence is exactly `ζ^{b·(n-k)}`. -/
lemma coset_summand_eq (k : ℕ) (b : ZMod m) (τ : ℍ) (n : ℕ) :
    ((PowerSeries.coeff n (jqInt ^ k) : ℤ) : ℂ)
        * (zetaM m ^ (↑b.val : ℤ) * wParam m τ) ^ n
        * (zetaM m ^ (-(↑b.val * ↑k : ℤ)) * wParam m τ ^ ((m ^ 2 - 1) * k))
      = ((PowerSeries.coeff n (jqInt ^ k) : ℤ) : ℂ)
        * zetaM m ^ ((↑b.val : ℤ) * ((n : ℤ) - (k : ℤ))) * wParam m τ ^ ((m ^ 2 - 1) * k + n) := by
  have hz : zetaM m ≠ 0 := zetaM_ne_zero
  rw [show (zetaM m ^ (↑b.val : ℤ) * wParam m τ) ^ n
        = zetaM m ^ ((↑b.val : ℤ) * ↑n) * wParam m τ ^ n from by
      rw [mul_pow, ← zpow_natCast (zetaM m ^ (↑b.val : ℤ)) n, ← zpow_mul],
    show (m ^ 2 - 1) * k + n = n + (m ^ 2 - 1) * k from by ring, pow_add,
    show ((↑b.val : ℤ) * ((n : ℤ) - (k : ℤ)))
        = (↑b.val : ℤ) * ↑n + (-(↑b.val * ↑k : ℤ)) from by ring,
    zpow_add₀ hz]
  ring

/-- **Per-coset `q`-expansion of the `some b` orbit term.** After multiplying `(j·q)ᵏ∘(coset)`
by the pole-clearing factor, the `n`-th coefficient carries the `b`-dependence `ζ^{b·(n-k)}`. -/
lemma hasSum_coset_some [NeZero m] (k : ℕ) (b : ZMod m) (τ : ℍ) :
    HasSum (fun n : ℕ ↦ ((PowerSeries.coeff n (jqInt ^ k) : ℤ) : ℂ)
        * zetaM m ^ ((↑b.val : ℤ) * ((n : ℤ) - (k : ℤ))) * wParam m τ ^ ((m ^ 2 - 1) * k + n))
      ((f m (some b) τ) ^ k * q τ ^ (m * k)) := by
  have h0 := hasSum_jqPow_at k (Acol m (b.val : ℤ) • τ)
  have h1 := h0.mul_right (zetaM m ^ (-(↑b.val * ↑k : ℤ)) * wParam m τ ^ ((m ^ 2 - 1) * k))
  rw [← Fi_some_eq k b τ] at h1
  simp only [q_Acol_smul] at h1
  have hfun : (fun n : ℕ ↦ ((PowerSeries.coeff n (jqInt ^ k) : ℤ) : ℂ)
        * zetaM m ^ ((↑b.val : ℤ) * ((n : ℤ) - (k : ℤ))) * wParam m τ ^ ((m ^ 2 - 1) * k + n))
      = fun n : ℕ ↦ ((PowerSeries.coeff n (jqInt ^ k) : ℤ) : ℂ)
        * (zetaM m ^ (↑b.val : ℤ) * wParam m τ) ^ n
        * (zetaM m ^ (-(↑b.val * ↑k : ℤ)) * wParam m τ ^ ((m ^ 2 - 1) * k)) :=
    funext (fun n ↦ (coset_summand_eq k b τ n).symm)
  rw [hfun]; exact h1

/-- Integer `q`-coefficients of the averaged coset contribution `∑_b (f_b)ᵏ·q^{mk}`. -/
def CAint (m k p : ℕ) : ℤ :=
  if (m ^ 2 - 1) * k ≤ m * p then (m : ℤ) * PowerSeries.coeff (m * p - (m ^ 2 - 1) * k) (jqInt ^ k)
  else 0

/-- Integer `q`-coefficients of the `∞`-coset contribution `(f_∞)ᵏ·q^{mk}`. -/
def CIint (m k p : ℕ) : ℤ :=
  if m ∣ p then PowerSeries.coeff (p / m) (jqInt ^ k) else 0

lemma aux_kadd [NeZero m] (k : ℕ) : k + (m ^ 2 - 1) * k = m ^ 2 * k := by
  have hM : 1 ≤ m ^ 2 := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero 2 (NeZero.ne m))
  have hk : k ≤ m ^ 2 * k := Nat.le_mul_of_pos_left k (by omega)
  rw [Nat.sub_one_mul]; omega

/-- **`q`-expansion of the `∞`-coset term.** `(f_∞)ᵏ·q^{mk}` is the honest `q`-series with
integer coefficients `CIint`. -/
lemma hasSum_I [NeZero m] (k : ℕ) (τ : ℍ) :
    HasSum (fun p : ℕ ↦ (CIint m k p : ℂ) * q τ ^ p) ((f m none τ) ^ k * q τ ^ (m * k)) := by
  have h0 := hasSum_jqPow_at k (AInf m • τ)
  rw [← Fi_none_eq k τ] at h0
  have hqAInf : q (AInf m • τ) = q τ ^ m := by
    rw [q_AInf_smul, pow_two, pow_mul, wParam_pow_m]
  have hI_n : HasSum (fun n : ℕ ↦ ((PowerSeries.coeff n (jqInt ^ k) : ℤ) : ℂ) * q τ ^ (m * n))
      ((f m none τ) ^ k * q τ ^ (m * k)) := by
    convert h0 using 2 with n
    rw [hqAInf, ← pow_mul]
  have hmpos : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  have hz : ∀ p ∉ Set.range (fun n : ℕ ↦ m * n),
      (fun p : ℕ ↦ (CIint m k p : ℂ) * q τ ^ p) p = 0 := by
    intro p hp
    have hnd : ¬ m ∣ p := fun hd ↦ hp (by obtain ⟨n, hn⟩ := hd; exact ⟨n, hn.symm⟩)
    simp only [CIint, ite_eq_right hnd, Int.cast_zero, zero_mul]
  have hcomp : ((fun p : ℕ ↦ (CIint m k p : ℂ) * q τ ^ p) ∘ fun n : ℕ ↦ m * n)
      = fun n : ℕ ↦ ((PowerSeries.coeff n (jqInt ^ k) : ℤ) : ℂ) * q τ ^ (m * n) := by
    funext n
    simp only [Function.comp_apply, CIint, ite_eq_left (dvd_mul_right m n),
      Nat.mul_div_cancel_left n hmpos]
  rw [← Function.Injective.hasSum_iff (fun a b hab ↦ Nat.eq_of_mul_eq_mul_left hmpos hab) hz, hcomp]
  exact hI_n

/-- Cast helper: `((m²-1)·k : ℤ) = m²·k − k`. -/
lemma cast_c [NeZero m] (k : ℕ) :
    (((m ^ 2 - 1) * k : ℕ) : ℤ) = (m : ℤ) ^ 2 * (k : ℤ) - (k : ℤ) := by
  have hkle : k ≤ m ^ 2 * k :=
    Nat.le_mul_of_pos_left k (pow_pos (Nat.pos_of_ne_zero (NeZero.ne m)) 2)
  rw [Nat.sub_one_mul, Nat.cast_sub hkle]; push_cast; ring

/-- **`q`-expansion of the averaged coset contribution `∑_b (f_b)ᵏ·q^{mk}`.** The root-of-unity
average `sum_zetaM_zpow_mul` collapses the `b`-dependence, leaving an honest `q`-series with
integer coefficients `CAint`. -/
lemma hasSum_A [NeZero m] (k : ℕ) (τ : ℍ) :
    HasSum (fun p : ℕ ↦ (CAint m k p : ℂ) * q τ ^ p)
      (∑ b : ZMod m, (f m (some b) τ) ^ k * q τ ^ (m * k)) := by
  have hmpos : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  have hqm : ∀ p : ℕ, wParam m τ ^ (m * p) = q τ ^ p := fun p ↦ by
    rw [pow_mul, wParam_pow_m]
  -- (1) sum the per-coset HasSums
  have hsum := hasSum_sum (s := (Finset.univ : Finset (ZMod m)))
    (fun b _ ↦ hasSum_coset_some k b τ)
  -- (2) collapse the b-average
  have hA_n : HasSum (fun n : ℕ ↦ ((PowerSeries.coeff n (jqInt ^ k) : ℤ) : ℂ)
        * (if (m : ℤ) ∣ ((n : ℤ) - (k : ℤ)) then (m : ℂ) else 0)
        * wParam m τ ^ ((m ^ 2 - 1) * k + n))
      (∑ b : ZMod m, (f m (some b) τ) ^ k * q τ ^ (m * k)) := by
    have hfun : (fun n : ℕ ↦ ((PowerSeries.coeff n (jqInt ^ k) : ℤ) : ℂ)
          * (if (m : ℤ) ∣ ((n : ℤ) - (k : ℤ)) then (m : ℂ) else 0)
          * wParam m τ ^ ((m ^ 2 - 1) * k + n))
        = fun n : ℕ ↦ ∑ b : ZMod m, ((PowerSeries.coeff n (jqInt ^ k) : ℤ) : ℂ)
          * zetaM m ^ ((↑b.val : ℤ) * ((n : ℤ) - (k : ℤ)))
            * wParam m τ ^ ((m ^ 2 - 1) * k + n) := by
      funext n
      rw [Finset.sum_congr rfl (fun b _ ↦
          show ((PowerSeries.coeff n (jqInt ^ k) : ℤ) : ℂ)
              * zetaM m ^ ((↑b.val : ℤ) * ((n : ℤ) - (k : ℤ))) * wParam m τ ^ ((m ^ 2 - 1) * k + n)
            = (((PowerSeries.coeff n (jqInt ^ k) : ℤ) : ℂ) * wParam m τ ^ ((m ^ 2 - 1) * k + n))
              * zetaM m ^ ((↑b.val : ℤ) * ((n : ℤ) - (k : ℤ))) from by ring),
        ← Finset.mul_sum, sum_zetaM_zpow_mul]
      ring
    rw [hfun]; exact hsum
  -- (3) reindex the collapsed series to honest q-powers
  refine (hasSum_iff_hasSum_of_ne_zero_bij
      (f := fun n : ℕ ↦ ((PowerSeries.coeff n (jqInt ^ k) : ℤ) : ℂ)
        * (if (m : ℤ) ∣ ((n : ℤ) - (k : ℤ)) then (m : ℂ) else 0)
        * wParam m τ ^ ((m ^ 2 - 1) * k + n))
      (fun x : Function.support (fun p : ℕ ↦ (CAint m k p : ℂ) * q τ ^ p) ↦
        m * (x : ℕ) - (m ^ 2 - 1) * k) ?_ ?_ ?_).mp hA_n
  · -- injectivity
    intro x y hxy
    have hx : (m ^ 2 - 1) * k ≤ m * (x : ℕ) := by
      by_contra hlt; exact x.2 (by simp only [CAint, ite_eq_right hlt, Int.cast_zero, zero_mul])
    have hy : (m ^ 2 - 1) * k ≤ m * (y : ℕ) := by
      by_contra hlt; exact y.2 (by simp only [CAint, ite_eq_right hlt, Int.cast_zero, zero_mul])
    simp only at hxy
    exact Subtype.ext (Nat.eq_of_mul_eq_mul_left hmpos (by omega))
  · -- support of the collapsed series is covered
    intro n hn
    have hdvd : (m : ℤ) ∣ ((n : ℤ) - (k : ℤ)) := by
      by_contra hnd; exact hn (by simp only [ite_eq_right hnd, mul_zero, zero_mul])
    have hcoeff_ne : PowerSeries.coeff n (jqInt ^ k) ≠ 0 := by
      intro h0; exact hn (by simp only [h0, Int.cast_zero, zero_mul])
    obtain ⟨s, hs⟩ := hdvd
    have hdvdN : m ∣ (n + (m ^ 2 - 1) * k) := by
      rw [← Int.natCast_dvd_natCast, Nat.cast_add, cast_c]
      exact ⟨s + (m : ℤ) * k, by linear_combination hs⟩
    have hmp : m * ((n + (m ^ 2 - 1) * k) / m) = n + (m ^ 2 - 1) * k := Nat.mul_div_cancel' hdvdN
    refine Set.mem_range.mpr ⟨⟨(n + (m ^ 2 - 1) * k) / m, ?_⟩, ?_⟩
    · -- the preimage lies in the support
      change (CAint m k ((n + (m ^ 2 - 1) * k) / m) : ℂ) * q τ ^ _ ≠ 0
      have hle : (m ^ 2 - 1) * k ≤ m * ((n + (m ^ 2 - 1) * k) / m) := by omega
      rw [CAint, ite_eq_left hle, hmp, Nat.add_sub_cancel]
      simp only [ne_eq, mul_eq_zero, not_or]
      refine ⟨?_, pow_ne_zero _ (by rw [q_eq]; exact Complex.exp_ne_zero _)⟩
      exact_mod_cast mul_ne_zero (Nat.cast_ne_zero.mpr (NeZero.ne m)) hcoeff_ne
    · -- the index maps back to `n`
      change m * ((n + (m ^ 2 - 1) * k) / m) - (m ^ 2 - 1) * k = n
      rw [hmp, Nat.add_sub_cancel]
  · -- the coefficient identity on the support
    rintro ⟨p, hp⟩
    have hle : (m ^ 2 - 1) * k ≤ m * p := by
      by_contra hlt; exact hp (by simp only [CAint, ite_eq_right hlt, Int.cast_zero, zero_mul])
    have hdvd : (m : ℤ) ∣ (((m * p - (m ^ 2 - 1) * k : ℕ) : ℤ) - (k : ℤ)) :=
      ⟨(p : ℤ) - (m : ℤ) * k, by rw [Nat.cast_sub hle, cast_c]; push_cast; ring⟩
    have hexp : (m ^ 2 - 1) * k + (m * p - (m ^ 2 - 1) * k) = m * p := Nat.add_sub_cancel' hle
    dsimp only
    rw [hexp, hqm, ite_eq_left hdvd, CAint, ite_eq_left hle]
    push_cast
    ring

/-- Integer `q`-coefficients of `powerSum·q^{mk}`. -/
def Cq (m k p : ℕ) : ℤ := CAint m k p + CIint m k p

/-- **The full `q`-series for `powerSum·q^{mk}`.** -/
lemma hasSum_powerSum_mul_qpow [Fact m.Prime] (k : ℕ) (τ : ℍ) :
    HasSum (fun p : ℕ ↦ (Cq m k p : ℂ) * q τ ^ p) (powerSum m k τ * q τ ^ (m * k)) := by
  have : NeZero m := ⟨(Fact.out : m.Prime).ne_zero⟩
  have hval : powerSum m k τ * q τ ^ (m * k)
      = (f m none τ) ^ k * q τ ^ (m * k)
        + ∑ b : ZMod m, (f m (some b) τ) ^ k * q τ ^ (m * k) := by
    simp only [powerSum, Fintype.sum_option, add_mul, Finset.sum_mul]
  rw [hval, show (fun p : ℕ ↦ (Cq m k p : ℂ) * q τ ^ p)
      = fun p : ℕ ↦ (CIint m k p : ℂ) * q τ ^ p + (CAint m k p : ℂ) * q τ ^ p from by
    funext p; rw [Cq]; push_cast; ring]
  exact (hasSum_I k τ).add (hasSum_A k τ)

/-- **(B3) The power sums are cusp-meromorphic of pole order `≤ m·k` with `ℚ`-coefficients.** -/
lemma powerSum_isCuspMeroR [Fact m.Prime] (k : ℕ) : IsCuspMeroR (powerSum m k) (m * k) RQ := by
  have : NeZero m := ⟨(Fact.out : m.Prime).ne_zero⟩
  have hpvadd : ∀ τ : ℍ, powerSum m k ((1 : ℝ) +ᵥ τ) = powerSum m k τ := fun τ ↦ by
    rw [← modular_T_smul]; exact powerSum_T k τ
  have hFper : Function.Periodic ((fun τ : ℍ ↦ powerSum m k τ * q τ ^ (m * k)) ∘ ofComplex) 1 :=
    periodic_comp_ofComplex_of_vadd (fun τ ↦ by simp only [hpvadd, q_vadd_one])
  have hFholo : MDiff (fun τ : ℍ ↦ powerSum m k τ * q τ ^ (m * k)) :=
    (mdifferentiable_powerSum k).mul (mdifferentiable_q.pow (m * k))
  have hFbdd : IsBoundedAtImInfty (fun τ : ℍ ↦ powerSum m k τ * q τ ^ (m * k)) :=
    isBoundedAtImInfty_powerSum_mul_qpow k
  have hFan : AnalyticAt ℂ (cuspFunction 1 (fun τ : ℍ ↦ powerSum m k τ * q τ ^ (m * k))) 0 :=
    analyticAt_cuspFunction_zero one_pos hFper hFholo hFbdd
  refine ⟨hFper, hFholo, hFbdd, fun n ↦ ?_⟩
  have huniq := qExpansion_coeff_unique_raw hFan hFper hFholo hFbdd
    (fun τ ↦ by simpa only [smul_eq_mul] using hasSum_powerSum_mul_qpow k τ) n
  rw [← huniq]
  exact intCast_mem_RQ (Cq m k n)

/-- **(B3) conclusion:** each power sum of the coset orbit is a `ℚ`-polynomial in `j`. -/
lemma powerSum_eq_aeval_j [Fact m.Prime] (k : ℕ) :
    ∃ Q : Polynomial ℚ, ∀ τ : ℍ, powerSum m k τ = (Polynomial.aeval (j τ)) Q := by
  obtain ⟨P, hPcoeff, _, hPeval⟩ :=
    Sk_eq_poly_j_closed (m * k) RQ (powerSum m k) (fun γ τ ↦ powerSum_smul k γ τ)
      (mdifferentiable_powerSum k) (powerSum_isCuspMeroR k)
  have hlift : P ∈ Polynomial.lifts (Rat.castHom ℂ) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    exact fun n ↦ Set.mem_range.mpr (RingHom.mem_range.mp (hPcoeff n))
  obtain ⟨Q, hQ⟩ := hlift
  refine ⟨Q, fun τ ↦ ?_⟩
  rw [hPeval τ, ← hQ, Polynomial.coe_mapRingHom, Polynomial.eval_map, Polynomial.aeval_def]
  congr 1

/-! ### (B4/B5) Newton's identities: the orbit-polynomial coefficients are `ℚ`-polynomials in `j` -/

/-- The `ℚ`-subalgebra of `ℍ → ℂ` of functions that are `ℚ`-polynomials in `j`. -/
def polyJ : Subalgebra ℚ (ℍ → ℂ) := (Polynomial.aeval (fun τ : ℍ ↦ j τ)).range

/-- Evaluating `aeval (τ ↦ j τ) Q` at a point `τ` gives `aeval (j τ) Q`. -/
lemma aeval_j_apply (Q : Polynomial ℚ) (τ : ℍ) :
    (Polynomial.aeval (fun τ : ℍ ↦ j τ) Q) τ = Polynomial.aeval (j τ) Q := by
  have := Polynomial.aeval_algHom_apply (Pi.evalAlgHom ℚ (fun _ : ℍ ↦ ℂ) τ) (fun τ : ℍ ↦ j τ) Q
  simpa using this.symm

lemma mem_polyJ_iff {g : ℍ → ℂ} :
    g ∈ polyJ ↔ ∃ Q : Polynomial ℚ, ∀ τ, g τ = Polynomial.aeval (j τ) Q := by
  constructor
  · rintro ⟨Q, hQ⟩
    refine ⟨Q, fun τ ↦ ?_⟩
    rw [← aeval_j_apply Q τ]
    exact congrFun hQ.symm τ
  · rintro ⟨Q, hQ⟩
    refine ⟨Q, funext fun τ ↦ ?_⟩
    change (Polynomial.aeval (fun τ : ℍ ↦ j τ) Q) τ = g τ
    rw [aeval_j_apply]; exact (hQ τ).symm

/-- Each power sum lies in `polyJ`. -/
lemma powerSum_mem_polyJ [Fact m.Prime] (l : ℕ) : powerSum m l ∈ polyJ :=
  mem_polyJ_iff.mpr (powerSum_eq_aeval_j l)

/-- The elementary symmetric functions of the orbit values, as functions of `τ`. -/
def esf (m : ℕ) [NeZero m] (l : ℕ) (τ : ℍ) : ℂ :=
  MvPolynomial.aeval (fun i : Option (ZMod m) ↦ f m i τ) (MvPolynomial.esymm (Option (ZMod m)) ℂ l)

/-- `aeval` of a power sum polynomial is the orbit power sum. -/
lemma aeval_psum_eq_powerSum [NeZero m] (l : ℕ) (τ : ℍ) :
    MvPolynomial.aeval (fun i : Option (ZMod m) ↦ f m i τ)
        (MvPolynomial.psum (Option (ZMod m)) ℂ l) = powerSum m l τ := by
  rw [MvPolynomial.psum, map_sum]
  simp only [map_pow, MvPolynomial.aeval_X]
  rfl

/-- **Newton's identity for the orbit** (pointwise), obtained by evaluating
`MvPolynomial.mul_esymm_eq_sum` at the orbit values. -/
lemma newton_esf [NeZero m] (l : ℕ) (τ : ℍ) :
    (l : ℂ) * esf m l τ
      = (-1) ^ (l + 1) * ∑ a ∈ Finset.antidiagonal l with a.1 < l,
          (-1) ^ a.1 * esf m a.1 τ * powerSum m a.2 τ := by
  have h := congrArg (MvPolynomial.aeval (fun i : Option (ZMod m) ↦ f m i τ))
    (MvPolynomial.mul_esymm_eq_sum (Option (ZMod m)) ℂ l)
  simp only [map_mul, map_natCast, map_pow, map_neg, map_one, map_sum,
    aeval_psum_eq_powerSum] at h
  simpa only [esf] using h

/-- `algebraMap ℚ (ℍ → ℂ)` evaluated at `τ` is the rational cast. -/
lemma algebraMap_polyJ_apply (c : ℚ) (τ : ℍ) : (algebraMap ℚ (ℍ → ℂ) c) τ = (c : ℂ) :=
  eq_ratCast (Pi.evalRingHom (fun _ : ℍ ↦ ℂ) τ|>.comp (algebraMap ℚ (ℍ → ℂ))) c

/-- Each elementary symmetric function of the orbit lies in `polyJ` (Newton induction). -/
lemma esf_mem_polyJ [Fact m.Prime] (l : ℕ) : (fun τ ↦ esf m l τ) ∈ polyJ := by
  have : NeZero m := ⟨(Fact.out : m.Prime).ne_zero⟩
  induction l using Nat.strong_induction_on with
  | _ l ih =>
    rcases Nat.eq_zero_or_pos l with hl | hl
    · subst hl
      have h0 : (fun τ ↦ esf m 0 τ) = (1 : ℍ → ℂ) := by
        funext τ; simp [esf, MvPolynomial.esymm_zero]
      rw [h0]; exact one_mem _
    · have hl0 : (l : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hl.ne'
      have hfun : (fun τ ↦ esf m l τ)
          = algebraMap ℚ (ℍ → ℂ) ((l : ℚ)⁻¹ * (-1) ^ (l + 1))
            * ∑ a ∈ Finset.antidiagonal l with a.1 < l,
              algebraMap ℚ (ℍ → ℂ) ((-1) ^ a.1) * (fun τ ↦ esf m a.1 τ) * powerSum m a.2 := by
        funext τ
        have hN := newton_esf (m := m) l τ
        simp only [Pi.mul_apply, Finset.sum_apply, algebraMap_polyJ_apply]
        push_cast
        field_simp
        linear_combination hN
      rw [hfun]
      refine mul_mem (Subalgebra.algebraMap_mem _ _) (sum_mem (fun a ha ↦ ?_))
      exact mul_mem (mul_mem (Subalgebra.algebraMap_mem _ _)
        (ih a.1 (Finset.mem_filter.mp ha).2)) (powerSum_mem_polyJ a.2)

/-- Each coefficient of the orbit polynomial lies in `polyJ`. -/
lemma orbitPoly_coeff_mem_polyJ [Fact m.Prime] (n : ℕ) :
    (fun τ ↦ (orbitPoly m τ).coeff n) ∈ polyJ := by
  have : NeZero m := ⟨(Fact.out : m.Prime).ne_zero⟩
  by_cases hn : n ≤ m + 1
  · have hfun : (fun τ ↦ (orbitPoly m τ).coeff n)
        = algebraMap ℚ (ℍ → ℂ) ((-1) ^ ((m + 1) - n)) * (fun τ ↦ esf m ((m + 1) - n) τ) := by
      funext τ
      have hop : orbitPoly m τ
          = (Multiset.map (fun t ↦ X - C t) (Finset.univ.val.map (fun i ↦ f m i τ))).prod := by
        rw [orbitPoly, Finset.prod_eq_multiset_prod, Multiset.map_map]; rfl
      have hcard : Multiset.card (Finset.univ.val.map (fun i : Option (ZMod m) ↦ f m i τ))
          = m + 1 := by
        rw [Multiset.card_map, Finset.card_val, Finset.card_univ, Fintype.card_option, ZMod.card]
      have hle : n ≤ Multiset.card (Finset.univ.val.map (fun i : Option (ZMod m) ↦ f m i τ)) := by
        rw [hcard]; exact hn
      rw [Pi.mul_apply, algebraMap_polyJ_apply, hop, Multiset.prod_X_sub_C_coeff _ hle, hcard]
      simp only [esf, MvPolynomial.aeval_esymm_eq_multiset_esymm]
      push_cast
      ring
    rw [hfun]
    exact mul_mem (Subalgebra.algebraMap_mem _ _) (esf_mem_polyJ ((m + 1) - n))
  · have h0 : (fun τ ↦ (orbitPoly m τ).coeff n) = (0 : ℍ → ℂ) := by
      funext τ
      exact coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (orbitPoly_natDegree_le τ) (by omega))
    rw [h0]; exact zero_mem _

/-- **The unconditional keystone.** For a prime `m`, the modular polynomial `Φ_m ∈ ℚ[Y][X]`
exists with the defining identity `∏_i (X − f_i τ) = Φ_m(X, j τ)` for every `τ`. All analytic
gates are discharged: the `hrat` input is now proved via the `(B3)` root-of-unity averaging,
`Sk_eq_poly_j_closed`, and Newton's identities. -/
theorem exists_PhiQ_closed [Fact m.Prime] :
    ∃ PhiQ : Polynomial (Polynomial ℚ),
      ∀ τ : ℍ, orbitPoly m τ = specializeY (j τ) PhiQ :=
  exists_PhiQ (fun n ↦ mem_polyJ_iff.mp (orbitPoly_coeff_mem_polyJ n))

end Chudnovsky
