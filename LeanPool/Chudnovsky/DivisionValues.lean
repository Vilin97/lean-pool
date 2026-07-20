/-
Copyright (c) 2026 Xuanji Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuanji Li
-/

import LeanPool.Chudnovsky.Quasiperiods
import Mathlib.Analysis.Meromorphic.TrailingCoefficient
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.RingTheory.Polynomial.IntegralNormalization

/-!
# Division values (Milla, Appendix A)

Division points of a period lattice, the functions `F_m = σ(mz)/σ(z)^{m²}`, and the
two outputs consumed by Appendix B (PLAN B1):

* `theowpsum` : `∑_{u ∈ DIV(m)} ℘(u) = 0`;
* `theomwpu`  : `m·℘(u)` (and `m/2·℘(u)` for even `m`) is integral over `ℤ[¼g₂, ¼g₃]`.

The `m`-division points in the fundamental parallelogram are indexed by pairs
`(k, l) ∈ (ℤ/m)² \ {0}` via `u = (k/m)·ω₁ + (l/m)·ω₂` (paper Lemma `lemmm`:
there are `m² − 1` of them).

TODO (PLAN B1): the division polynomials `P_m ∈ ℤ[x, h₂, h₃]` with their four-case
recursion, Baker's factorization `thmbaker`
(`m²·∏_{u ∈ DIV(m)} (x − ℘(u)) = P_m(x)² · (4(x³ − h₂x − h₃))^{[m even]}`) and the
structure lemmas `propindu`, from which the two theorems below follow.
-/

open scoped Topology

noncomputable section

namespace PeriodPair

variable (L : PeriodPair)

/-- The `m`-division point `(k/m)·ω₁ + (l/m)·ω₂` indexed by `v = (k, l) : Fin m × Fin m`.
For `v ≠ 0` these are exactly the points of the paper's `DIV(m)` (Def. `defidivi`). -/
def divPt (m : ℕ) (v : Fin m × Fin m) : ℂ :=
  ((v.1 : ℕ) : ℂ) / m * L.ω₁ + ((v.2 : ℕ) : ℂ) / m * L.ω₂

/-- A nonnegative rational `k/m` with `k < m` and integral denominator must be `0`. -/
private lemma div_den_eq_one_imp {m : ℕ} (hm : 0 < m) {k : ℕ} (hk : k < m)
    (h : ((k : ℚ) / (m : ℚ)).den = 1) : k = 0 := by
  have hmQ : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  set q : ℚ := (k : ℚ) / (m : ℚ) with hqdef
  have h0 : (0 : ℚ) ≤ q := by rw [hqdef]; positivity
  have h1 : q < 1 := by
    rw [hqdef, div_lt_one (by exact_mod_cast hm)]; exact_mod_cast hk
  have heq : (q.num : ℚ) = q := (Rat.den_eq_one_iff q).mp h
  have hnn : (0 : ℤ) ≤ q.num := by have := h0; rw [← heq] at this; exact_mod_cast this
  have hl1 : q.num < 1 := by have := h1; rw [← heq] at this; exact_mod_cast this
  have hnum0 : q.num = 0 := by omega
  have hq0 : q = 0 := by rw [← heq, hnum0]; simp
  rw [hqdef] at hq0
  rcases div_eq_zero_iff.mp hq0 with hkq | hmq
  · exact_mod_cast hkq
  · exact absurd hmq hmQ

/-- Division points with `v ≠ 0` are not lattice points (so `℘` is finite there). -/
theorem divPt_notMem_lattice {m : ℕ} [NeZero m] {v : Fin m × Fin m} (hv : v ≠ 0) :
    L.divPt m v ∉ L.lattice := by
  have hmpos : 0 < m := NeZero.pos m
  have hdiv : L.divPt m v
      = (((v.1 : ℕ) / (m : ℚ) : ℚ) : ℂ) * L.ω₁ + (((v.2 : ℕ) / (m : ℚ) : ℚ) : ℂ) * L.ω₂ := by
    simp only [divPt]; push_cast; ring
  rw [hdiv]
  intro hmem
  rw [mul_ω₁_add_mul_ω₂_mem_lattice] at hmem
  obtain ⟨hd1, hd2⟩ := hmem
  have e1 := div_den_eq_one_imp hmpos v.1.2 hd1
  have e2 := div_den_eq_one_imp hmpos v.2.2 hd2
  have hv1 : v.1 = 0 := Fin.val_injective (by simpa using e1)
  have hv2 : v.2 = 0 := Fin.val_injective (by simpa using e2)
  exact hv (Prod.ext hv1 hv2)

/-! ## The σ-transformation law (paper Prop. `trafosigma`)

We derive the transformation law of the Weierstrass σ-function in a single period direction
`ω` (with `ω/2 ∉ L`), and its `n`-fold iterate. This is the local copy referred to in the
plan (parallel to the derivation in `Fourier.lean`, which we cannot import here). -/

/-- The lattice is a countable subset of `ℂ` (local copy of the private helper in
`Quasiperiods.lean`). -/
private lemma countable_lattice' : (↑L.lattice : Set ℂ).Countable := by
  have : Countable ↥L.lattice := countable_of_Lindelof_of_discrete
  simpa using Set.countable_range (Subtype.val : ↥L.lattice → ℂ)

/-- `σ` is nonzero away from the lattice. -/
private lemma weierstrassSigma_ne_zero {x : ℂ} (hx : x ∉ L.lattice) :
    L.weierstrassSigma x ≠ 0 := fun h ↦ hx ((L.weierstrassSigma_eq_zero_iff x).mp h)

/-- The σ-transformation law for a single period `ω` with `ω/2 ∉ L`:
`σ(z+ω) = -exp(η·(z+ω/2))·σ(z)`, where `η` is the additive quasi-period `ζ(z+ω)-ζ(z)`.
Instantiated with `ω = ω₁, η = η₁` and `ω = ω₂, η = η₂` (paper Prop. `trafosigma`). -/
private theorem sigma_add_period_aux {ω η : ℂ} (hω : ω ∈ L.lattice) (hω2 : ω / 2 ∉ L.lattice)
    (hquasi : ∀ z ∉ L.lattice, L.weierstrassZeta (z + ω) = L.weierstrassZeta z + η) (w : ℂ) :
    L.weierstrassSigma (w + ω) = -Complex.exp (η * (w + ω / 2)) * L.weierstrassSigma w := by
  by_cases hw : w ∈ L.lattice
  · -- both sides vanish at lattice points
    have h1 : L.weierstrassSigma w = 0 := (L.weierstrassSigma_eq_zero_iff w).mpr hw
    have h2 : L.weierstrassSigma (w + ω) = 0 :=
      (L.weierstrassSigma_eq_zero_iff (w + ω)).mpr (add_mem hw hω)
    rw [h1, h2]; ring
  · -- ratio `F z = σ(z+ω)/(exp(η(z+ω/2))·σ(z))` is locally constant `= -1`
    set den : ℂ → ℂ := fun z ↦ Complex.exp (η * (z + ω / 2)) * L.weierstrassSigma z with hden
    set F : ℂ → ℂ := fun z ↦ L.weierstrassSigma (z + ω) / den z with hF
    have hσdiff : Differentiable ℂ L.weierstrassSigma := L.differentiable_weierstrassSigma
    have hnumdiff : Differentiable ℂ (fun z ↦ L.weierstrassSigma (z + ω)) :=
      hσdiff.comp (differentiable_id.add_const ω)
    have hexpdiff : Differentiable ℂ (fun z ↦ Complex.exp (η * (z + ω / 2))) := by fun_prop
    have hdendiff : Differentiable ℂ den := by rw [hden]; exact hexpdiff.mul hσdiff
    have hmem : ∀ {x : ℂ}, x ∉ L.lattice → x + ω ∉ L.lattice := fun hx hc ↦
      hx (by simpa using sub_mem hc hω)
    have hden_ne : ∀ x ∉ L.lattice, den x ≠ 0 := fun x hx ↦ by
      rw [hden]; exact mul_ne_zero (Complex.exp_ne_zero _) (L.weierstrassSigma_ne_zero hx)
    have hnum_ne : ∀ x ∉ L.lattice, L.weierstrassSigma (x + ω) ≠ 0 := fun x hx ↦
      L.weierstrassSigma_ne_zero (hmem hx)
    have hF_ne : ∀ x ∉ L.lattice, F x ≠ 0 := fun x hx ↦ by
      rw [hF]; exact div_ne_zero (hnum_ne x hx) (hden_ne x hx)
    -- logarithmic derivative of `F` vanishes on `Lᶜ`
    have hlogF : ∀ x ∉ L.lattice, logDeriv F x = 0 := fun x hx ↦ by
      have hxω : x + ω ∉ L.lattice := hmem hx
      have hlognum : logDeriv (fun z ↦ L.weierstrassSigma (z + ω)) x
          = L.weierstrassZeta (x + ω) := by
        rw [logDeriv_apply, deriv_comp_add_const, ← logDeriv_apply,
          L.logDeriv_weierstrassSigma (x + ω) hxω]
      have hlogexp : logDeriv (fun z ↦ Complex.exp (η * (z + ω / 2))) x = η := by
        have hd : HasDerivAt (fun z ↦ Complex.exp (η * (z + ω / 2)))
            (Complex.exp (η * (x + ω / 2)) * η) x := by
          have hlin : HasDerivAt (fun z : ℂ ↦ η * (z + ω / 2)) η x := by
            simpa using ((hasDerivAt_id x).add_const (ω / 2)).const_mul η
          simpa using hlin.cexp
        rw [logDeriv_apply, hd.deriv, mul_comm, mul_div_assoc,
          div_self (Complex.exp_ne_zero _), mul_one]
      have hlogden : logDeriv den x = η + L.weierstrassZeta x := by
        rw [hden, logDeriv_mul (f := fun z ↦ Complex.exp (η * (z + ω / 2)))
          (g := L.weierstrassSigma) x (Complex.exp_ne_zero _) (L.weierstrassSigma_ne_zero hx)
          (hexpdiff x) (hσdiff x), hlogexp, L.logDeriv_weierstrassSigma x hx]
      rw [hF, logDeriv_div x (hnum_ne x hx) (hden_ne x hx) (hnumdiff x) (hdendiff x),
        hlognum, hlogden, hquasi x hx]
      ring
    -- hence `deriv F = 0` on `Lᶜ`
    have hderiv0 : ∀ x ∉ L.lattice, deriv F x = 0 := fun x hx ↦ by
      have h := hlogF x hx
      rw [logDeriv_apply, div_eq_zero_iff] at h
      exact h.resolve_right (hF_ne x hx)
    -- set up the `eqOn_of_deriv_eq` comparison with the constant `-1`
    have hopen : IsOpen ((↑L.lattice : Set ℂ)ᶜ) := L.isClosed_lattice.isOpen_compl
    have hconn : IsPreconnected ((↑L.lattice : Set ℂ)ᶜ) :=
      (L.countable_lattice'.isConnected_compl_of_one_lt_rank (by simp)).isPreconnected
    have hFdiff : DifferentiableOn ℂ F (↑L.lattice)ᶜ := by
      refine DifferentiableOn.div hnumdiff.differentiableOn hdendiff.differentiableOn
        (fun x hx ↦ hden_ne x hx)
    have hderivEq : (↑L.lattice : Set ℂ)ᶜ.EqOn (deriv F) (deriv (fun _ ↦ (-1 : ℂ))) := by
      intro x hx
      rw [hderiv0 x hx, deriv_const']
    have hx₀ : -(ω / 2) ∈ (↑L.lattice : Set ℂ)ᶜ := fun hc ↦ hω2 (by simpa using neg_mem hc)
    have hσ_half_ne : L.weierstrassSigma (ω / 2) ≠ 0 :=
      L.weierstrassSigma_ne_zero hω2
    have hval : F (-(ω / 2)) = -1 := by
      rw [hF]
      simp only [hden]
      rw [show -(ω / 2) + ω = ω / 2 by ring, show η * (-(ω / 2) + ω / 2) = 0 by ring,
        Complex.exp_zero, one_mul, L.weierstrassSigma_neg, div_neg, div_self hσ_half_ne]
    have hEqOn := hopen.eqOn_of_deriv_eq hconn hFdiff (differentiableOn_const _) hderivEq hx₀ hval
    have hFw : F w = -1 := hEqOn hw
    have hdw : den w ≠ 0 := hden_ne w hw
    rw [hF] at hFw
    have := (div_eq_iff hdw).mp hFw
    rw [this, hden]; ring

/-- The `n`-fold iterate of the σ-transformation law (paper Eq. `glgsigmatr`):
`σ(w + n·ω) = (-1)ⁿ·exp(η·(n·w + n²·ω/2))·σ(w)`. -/
private theorem sigma_add_nsmul {ω η : ℂ}
    (hbase : ∀ w, L.weierstrassSigma (w + ω)
      = -Complex.exp (η * (w + ω / 2)) * L.weierstrassSigma w) (n : ℕ) (w : ℂ) :
    L.weierstrassSigma (w + n * ω)
      = (-1) ^ n * Complex.exp (η * (n * w + n ^ 2 * ω / 2)) * L.weierstrassSigma w := by
  induction n with
  | zero => simp
  | succ k ih =>
    have hstep : w + (↑(k + 1) : ℂ) * ω = (w + ↑k * ω) + ω := by push_cast; ring
    rw [hstep, hbase, ih]
    have hexp : Complex.exp (η * (w + ↑k * ω + ω / 2))
          * Complex.exp (η * (↑k * w + ↑k ^ 2 * ω / 2))
        = Complex.exp (η * (↑(k + 1) * w + ↑(k + 1) ^ 2 * ω / 2)) := by
      rw [← Complex.exp_add]; congr 1; push_cast; ring
    rw [pow_succ, ← hexp]
    ring_nf

/-- `(-1)^{m²} = (-1)^m` in `ℂ` (`m²` and `m` have the same parity). -/
private lemma neg_one_pow_sq (m : ℕ) : ((-1 : ℂ)) ^ (m ^ 2) = (-1) ^ m := by
  rcases Nat.even_or_odd m with he | ho
  · rw [he.neg_one_pow, (Nat.even_pow.mpr ⟨he, two_ne_zero⟩).neg_one_pow]
  · rw [ho.neg_one_pow, ho.pow.neg_one_pow]

/-- Milla's `F_m(z) = σ(mz)/σ(z)^{m²}` (Lemma `lemdefifm`): an elliptic function with
a pole of order `m² − 1` on `L` and simple zeros exactly at the `m`-division points. -/
def Fm (m : ℕ) (z : ℂ) : ℂ := L.weierstrassSigma (m * z) / L.weierstrassSigma z ^ (m ^ 2)

/-- `F_m` is periodic in a single "good" period direction `ω` (one for which the
σ-transformation law `hbase` holds), i.e. `ω ∈ {ω₁, ω₂}`. -/
private theorem Fm_add_period_aux {ω η : ℂ}
    (hbase : ∀ w, L.weierstrassSigma (w + ω)
      = -Complex.exp (η * (w + ω / 2)) * L.weierstrassSigma w) (m : ℕ) (z : ℂ) :
    L.Fm m (z + ω) = L.Fm m z := by
  unfold Fm
  have hnum : L.weierstrassSigma (↑m * (z + ω))
      = (-1) ^ m * Complex.exp (η * (↑m * (↑m * z) + ↑m ^ 2 * ω / 2))
        * L.weierstrassSigma (↑m * z) := by
    rw [show (↑m : ℂ) * (z + ω) = (↑m * z) + ↑m * ω by ring]
    exact L.sigma_add_nsmul hbase m (↑m * z)
  have harg : η * (↑m * (↑m * z) + ↑m ^ 2 * ω / 2)
      = ((↑(m ^ 2) : ℂ)) * (η * (z + ω / 2)) := by push_cast; ring
  have hcoeffeq : (-1 : ℂ) ^ m * Complex.exp (η * (↑m * (↑m * z) + ↑m ^ 2 * ω / 2))
      = (-Complex.exp (η * (z + ω / 2))) ^ (m ^ 2) := by
    rw [harg, Complex.exp_nat_mul, ← neg_one_pow_sq, ← neg_pow]
  have hcD_ne : (-Complex.exp (η * (z + ω / 2))) ^ (m ^ 2) ≠ 0 :=
    pow_ne_zero _ (neg_ne_zero.mpr (Complex.exp_ne_zero _))
  rw [hnum, hbase z, mul_pow, mul_div_mul_comm, hcoeffeq, div_self hcD_ne, one_mul]

/-- `F_m` is invariant under translation by any integer multiple of a single period `p`
for which it is `p`-periodic. -/
private theorem Fm_add_intmul {p : ℂ} {m : ℕ} (hp : ∀ w, L.Fm m (w + p) = L.Fm m w)
    (a : ℤ) (w : ℂ) : L.Fm m (w + a * p) = L.Fm m w := by
  have hpneg : ∀ x, L.Fm m (x - p) = L.Fm m x := by
    intro x
    have := hp (x - p)
    rw [show x - p + p = x by ring] at this
    exact this.symm
  induction a using Int.induction_on with
  | zero => simp
  | succ k ih =>
    have heq : w + ((↑k + 1 : ℤ) : ℂ) * p = (w + (↑k : ℤ) * p) + p := by push_cast; ring
    rw [heq, hp, ih]
  | pred k ih =>
    have heq : w + ((-↑k - 1 : ℤ) : ℂ) * p = (w + (-↑k : ℤ) * p) - p := by push_cast; ring
    rw [heq, hpneg, ih]

/-- `F_m` is doubly periodic (paper Lemma `lemdefifm`, via the σ-transformation law
`trafosigma`). -/
theorem Fm_periodic (m : ℕ) {ω : ℂ} (hω : ω ∈ L.lattice) (z : ℂ) :
    L.Fm m (z + ω) = L.Fm m z := by
  -- the σ-transformation laws in the directions ω₁, ω₂
  have hbase1 : ∀ w, L.weierstrassSigma (w + L.ω₁)
      = -Complex.exp (L.eta₁ * (w + L.ω₁ / 2)) * L.weierstrassSigma w :=
    L.sigma_add_period_aux L.ω₁_mem_lattice L.ω₁_div_two_notMem_lattice
      (fun z hz ↦ L.weierstrassZeta_add_ω₁ z hz)
  have hbase2 : ∀ w, L.weierstrassSigma (w + L.ω₂)
      = -Complex.exp (L.eta₂ * (w + L.ω₂ / 2)) * L.weierstrassSigma w :=
    L.sigma_add_period_aux L.ω₂_mem_lattice L.ω₂_div_two_notMem_lattice
      (fun z hz ↦ L.weierstrassZeta_add_ω₂ z hz)
  have hper1 : ∀ w, L.Fm m (w + L.ω₁) = L.Fm m w := fun w ↦ L.Fm_add_period_aux hbase1 m w
  have hper2 : ∀ w, L.Fm m (w + L.ω₂) = L.Fm m w := fun w ↦ L.Fm_add_period_aux hbase2 m w
  -- write ω = a·ω₁ + b·ω₂ and translate
  obtain ⟨a, b, hab⟩ := PeriodPair.mem_lattice.mp hω
  rw [← hab, show z + (↑a * L.ω₁ + ↑b * L.ω₂) = (z + ↑a * L.ω₁) + ↑b * L.ω₂ by ring,
    L.Fm_add_intmul hper2 b, L.Fm_add_intmul hper1 a]

/-! ## The multiplication formula and `theowpsum` (the ζ-trick)

We prove `∑_{v ≠ 0} ℘(u_v) = 0` (`theowpsum`) directly, without the division polynomials.
The argument has three steps:

* the *multiplication formula* `∑_{v} ℘(z + u_v) = m²·℘(mz) + c` (the difference is entire
  and doubly periodic, hence constant by the first Liouville theorem — the removable
  singularities at the `m`-torsion points are handled algebraically via `weierstrassPExcept`);
* the constant `c` vanishes, via the ζ-function `∑_v ζ(z+u_v) − m·ζ(mz)`, whose derivative is
  the multiplication difference and which is doubly *periodic* (quasi-periods cancel);
* evaluation of the multiplication formula at `z = 0`. -/

/-- A signed fraction `k/m` with integral value and `|k| < m` is zero. -/
private lemma frac_den_one_imp_zero {m : ℕ} (hm : 0 < m) {k : ℤ}
    (hlt : k.natAbs < m) (h : ((k : ℚ) / (m : ℚ)).den = 1) : k = 0 := by
  have hmQ : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  set q : ℚ := (k : ℚ) / (m : ℚ) with hqdef
  have heq : ((q.num : ℤ) : ℚ) = q := (Rat.den_eq_one_iff q).mp h
  have hqk : (k : ℚ) = q.num * (m : ℚ) := by
    rw [heq, hqdef, div_mul_cancel₀ _ hmQ]
  have hkeq : k = q.num * (m : ℤ) := by exact_mod_cast hqk
  have hnat : k.natAbs = q.num.natAbs * m := by
    rw [hkeq, Int.natAbs_mul, Int.natAbs_natCast]
  rcases Nat.eq_zero_or_pos q.num.natAbs with h0 | h0
  · rw [hkeq]; simp [Int.natAbs_eq_zero.mp h0]
  · exfalso
    have hle : m ≤ q.num.natAbs * m := Nat.le_mul_of_pos_left m h0
    omega

/-- A fraction `k/m` with `m ∣ k` has denominator one. -/
private lemma frac_den_one_of_dvd {m : ℕ} (hm : 0 < m) {k : ℤ}
    (h : (m : ℤ) ∣ k) : ((k : ℚ) / (m : ℚ)).den = 1 := by
  obtain ⟨j, rfl⟩ := h
  have hmQ : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  have : (((m : ℤ) * j : ℤ) : ℚ) / (m : ℚ) = (j : ℚ) := by
    push_cast
    rw [mul_comm, mul_div_assoc, div_self hmQ, mul_one]
  rw [this]
  exact Rat.den_intCast j

/-- `m · (divPt m v)` is a lattice point (namely `v.1·ω₁ + v.2·ω₂`). -/
private lemma mul_divPt_mem_lattice {m : ℕ} [NeZero m] (v : Fin m × Fin m) :
    (m : ℂ) * L.divPt m v ∈ L.lattice := by
  have hm : (m : ℂ) ≠ 0 := by exact_mod_cast (NeZero.pos m).ne'
  rw [PeriodPair.mem_lattice]
  refine ⟨(v.1 : ℕ), (v.2 : ℕ), ?_⟩
  simp only [divPt]
  push_cast
  field_simp

/-- If `z + divPt m v ∈ L` then `m·z ∈ L`. -/
private lemma mul_mem_lattice_of_add_divPt_mem {m : ℕ} [NeZero m] {z : ℂ} {v : Fin m × Fin m}
    (h : z + L.divPt m v ∈ L.lattice) : (m : ℂ) * z ∈ L.lattice := by
  have h1 : (m : ℂ) * (z + L.divPt m v) ∈ L.lattice := by
    rw [← nsmul_eq_mul]; exact nsmul_mem h m
  have h2 := sub_mem h1 (L.mul_divPt_mem_lattice v)
  simpa [mul_add] using h2

/-- Division points with distinct indices differ by a non-lattice point. -/
private lemma divPt_sub_notMem_lattice {m : ℕ} [NeZero m] {v v' : Fin m × Fin m} (hne : v ≠ v') :
    L.divPt m v - L.divPt m v' ∉ L.lattice := by
  have hm : 0 < m := NeZero.pos m
  intro hmem
  have hdiff : L.divPt m v - L.divPt m v'
      = ((((v.1 : ℤ) - (v'.1 : ℤ) : ℤ) : ℚ) / (m : ℚ) : ℚ) * L.ω₁
        + ((((v.2 : ℤ) - (v'.2 : ℤ) : ℤ) : ℚ) / (m : ℚ) : ℚ) * L.ω₂ := by
    simp only [divPt]; push_cast; ring
  rw [hdiff, mul_ω₁_add_mul_ω₂_mem_lattice] at hmem
  obtain ⟨hd1, hd2⟩ := hmem
  have e1 : (v.1 : ℤ) - (v'.1 : ℤ) = 0 := by
    refine frac_den_one_imp_zero hm ?_ hd1
    have := v.1.isLt; have := v'.1.isLt; omega
  have e2 : (v.2 : ℤ) - (v'.2 : ℤ) = 0 := by
    refine frac_den_one_imp_zero hm ?_ hd2
    have := v.2.isLt; have := v'.2.isLt; omega
  apply hne
  have h1 : v.1 = v'.1 := Fin.ext (by omega)
  have h2 : v.2 = v'.2 := Fin.ext (by omega)
  exact Prod.ext h1 h2

/-- Surjectivity onto `m`-torsion: if `m·z ∈ L` then `z ≡ -divPt m v` for some `v`. -/
private lemma exists_add_divPt_mem_lattice {m : ℕ} [NeZero m] {z : ℂ}
    (hz : (m : ℂ) * z ∈ L.lattice) : ∃ v : Fin m × Fin m, z + L.divPt m v ∈ L.lattice := by
  have hm : 0 < m := NeZero.pos m
  have hmZ : (0 : ℤ) < (m : ℤ) := by exact_mod_cast hm
  have hmC : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  obtain ⟨a, b, hab⟩ := PeriodPair.mem_lattice.mp hz
  -- residues in `[0, m)`
  have hr1 : ((-a) % (m : ℤ)).toNat < m := by
    have h0 : 0 ≤ (-a) % (m : ℤ) := Int.emod_nonneg _ hmZ.ne'
    have h1 : (-a) % (m : ℤ) < (m : ℤ) := Int.emod_lt_of_pos _ hmZ
    omega
  have hr2 : ((-b) % (m : ℤ)).toNat < m := by
    have h0 : 0 ≤ (-b) % (m : ℤ) := Int.emod_nonneg _ hmZ.ne'
    have h1 : (-b) % (m : ℤ) < (m : ℤ) := Int.emod_lt_of_pos _ hmZ
    omega
  set ra : ℤ := (-a) % (m : ℤ) with hra
  set rb : ℤ := (-b) % (m : ℤ) with hrb
  have hra0 : 0 ≤ ra := Int.emod_nonneg _ hmZ.ne'
  have hrb0 : 0 ≤ rb := Int.emod_nonneg _ hmZ.ne'
  refine ⟨(⟨ra.toNat, hr1⟩, ⟨rb.toNat, hr2⟩), ?_⟩
  -- `z = (a/m)ω₁ + (b/m)ω₂`
  have hzeq : z = ((a : ℂ) / m) * L.ω₁ + ((b : ℂ) / m) * L.ω₂ := by
    have h := hab.symm
    field_simp
    linear_combination h
  -- integer witnesses for membership
  rw [PeriodPair.mem_lattice]
  refine ⟨-((-a) / (m : ℤ)), -((-b) / (m : ℤ)), ?_⟩
  have hcra : ((ra.toNat : ℂ)) = (ra : ℂ) := by exact_mod_cast Int.toNat_of_nonneg hra0
  have hcrb : ((rb.toNat : ℂ)) = (rb : ℂ) := by exact_mod_cast Int.toNat_of_nonneg hrb0
  have hjaC : (a : ℂ) + (ra : ℂ) = (m : ℂ) * (-((-a) / (m : ℤ)) : ℤ) := by
    have : a + ra = (m : ℤ) * (-((-a) / (m : ℤ))) := by rw [hra, Int.emod_def]; ring
    exact_mod_cast this
  have hjbC : (b : ℂ) + (rb : ℂ) = (m : ℂ) * (-((-b) / (m : ℤ)) : ℤ) := by
    have : b + rb = (m : ℤ) * (-((-b) / (m : ℤ))) := by rw [hrb, Int.emod_def]; ring
    exact_mod_cast this
  have key1 : (a : ℂ) / m + (ra : ℂ) / m = ((-((-a) / (m : ℤ)) : ℤ) : ℂ) := by
    rw [← add_div, hjaC, mul_comm, mul_div_assoc, div_self hmC, mul_one]
  have key2 : (b : ℂ) / m + (rb : ℂ) / m = ((-((-b) / (m : ℤ)) : ℤ) : ℂ) := by
    rw [← add_div, hjbC, mul_comm, mul_div_assoc, div_self hmC, mul_one]
  rw [hzeq]
  simp only [divPt, hcra, hcrb]
  linear_combination -(key1 * L.ω₁) - key2 * L.ω₂

/-- **Pole cancellation.** At an `m`-torsion point `z` (with `z + u_{v₀} ∈ L` and `m·z ∈ L`),
the diverging term `℘(w + u_{v₀}) − m²·℘(mw)` of the multiplication difference equals a function
analytic at `z` (its two double poles cancel algebraically). -/
private lemma mulPole_identity {m : ℕ} [NeZero m] {z : ℂ} {v₀ : Fin m × Fin m}
    (hv₀ : z + L.divPt m v₀ ∈ L.lattice) (hmp : (m : ℂ) * z ∈ L.lattice) (w : ℂ) :
    L.weierstrassP (w + L.divPt m v₀) - (m : ℂ) ^ 2 * L.weierstrassP (m * w)
      = L.weierstrassPExcept 0 (w - z) - (m : ℂ) ^ 2 * L.weierstrassPExcept 0 (m * (w - z)) := by
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast (NeZero.pos m).ne'
  have hE1 : L.weierstrassPExcept 0 (w - z) = L.weierstrassP (w - z) + -((w - z) ^ 2)⁻¹ := by
    simpa using L.weierstrassPExcept_def (0 : L.lattice) (w - z)
  have hE2 : L.weierstrassPExcept 0 (m * (w - z))
      = L.weierstrassP (m * (w - z)) + -(((m : ℂ) * (w - z)) ^ 2)⁻¹ := by
    simpa using L.weierstrassPExcept_def (0 : L.lattice) (m * (w - z))
  have hP1 : L.weierstrassP (w - z) = L.weierstrassP (w + L.divPt m v₀) := by
    rw [show w + L.divPt m v₀ = (w - z) + (z + L.divPt m v₀) by ring]
    exact (L.weierstrassP_add_coe (w - z) ⟨_, hv₀⟩).symm
  have hP2 : L.weierstrassP (m * (w - z)) = L.weierstrassP (m * w) := by
    rw [show (m : ℂ) * w = (m * (w - z)) + (m * z) by ring]
    exact (L.weierstrassP_add_coe (m * (w - z)) ⟨_, hmp⟩).symm
  have hfrac : (m : ℂ) ^ 2 * (((m : ℂ) * (w - z)) ^ 2)⁻¹ = ((w - z) ^ 2)⁻¹ := by
    rcases eq_or_ne (w - z) 0 with h | h
    · simp [h]
    · field_simp
  rw [hE1, hE2, hP1, hP2]
  linear_combination -hfrac

/-- The multiplication-formula difference `∑_v ℘(z + u_v) − m²·℘(mz)`. -/
private def mulDiff (m : ℕ) (z : ℂ) : ℂ :=
  (∑ v : Fin m × Fin m, L.weierstrassP (z + L.divPt m v)) - (m : ℂ) ^ 2 * L.weierstrassP (m * z)

/-- The multiplication difference is entire: away from the `m`-torsion points every summand is
analytic, and at a torsion point the two double poles cancel (`mulPole_identity`). -/
private lemma analyticAt_mulDiff {m : ℕ} [NeZero m] (z : ℂ) : AnalyticAt ℂ (L.mulDiff m) z := by
  by_cases hmp : (m : ℂ) * z ∈ L.lattice
  · obtain ⟨v₀, hv₀⟩ := L.exists_add_divPt_mem_lattice hmp
    have heq : L.mulDiff m
        = fun w => (∑ v ∈ Finset.univ.erase v₀, L.weierstrassP (w + L.divPt m v))
            + (L.weierstrassPExcept 0 (w - z)
              - (m : ℂ) ^ 2 * L.weierstrassPExcept 0 (m * (w - z))) := by
      funext w
      simp only [mulDiff]
      rw [← Finset.add_sum_erase Finset.univ (fun v => L.weierstrassP (w + L.divPt m v))
          (Finset.mem_univ v₀), ← L.mulPole_identity hv₀ hmp w]
      ring
    rw [heq]
    apply AnalyticAt.add
    · apply Finset.analyticAt_fun_sum
      intro v hv
      have hne : v ≠ v₀ := (Finset.mem_erase.mp hv).1
      have hnl : z + L.divPt m v ∉ L.lattice := by
        intro hc
        exact L.divPt_sub_notMem_lattice hne (by
          have h := sub_mem hc hv₀
          simpa [add_sub_add_left_eq_sub] using h)
      have hf : AnalyticAt ℂ (fun w : ℂ => w + L.divPt m v) z := by fun_prop
      exact (L.analyticOnNhd_weierstrassP _ hnl).comp_of_eq hf rfl
    · apply AnalyticAt.sub
      · have hf : AnalyticAt ℂ (fun w : ℂ => w - z) z := by fun_prop
        exact (L.analyticAt_weierstrassPExcept 0).comp_of_eq hf (sub_self z)
      · refine analyticAt_const.mul ?_
        have hf : AnalyticAt ℂ (fun w : ℂ => (m : ℂ) * (w - z)) z := by fun_prop
        exact (L.analyticAt_weierstrassPExcept 0).comp_of_eq hf (by rw [sub_self, mul_zero])
  · change AnalyticAt ℂ (fun w => (∑ v : Fin m × Fin m, L.weierstrassP (w + L.divPt m v))
        - (m : ℂ) ^ 2 * L.weierstrassP (m * w)) z
    apply AnalyticAt.sub
    · apply Finset.analyticAt_fun_sum
      intro v _
      have hnl : z + L.divPt m v ∉ L.lattice :=
        fun hc => hmp (L.mul_mem_lattice_of_add_divPt_mem hc)
      have hf : AnalyticAt ℂ (fun w : ℂ => w + L.divPt m v) z := by fun_prop
      exact (L.analyticOnNhd_weierstrassP _ hnl).comp_of_eq hf rfl
    · refine analyticAt_const.mul ?_
      have hf : AnalyticAt ℂ (fun w : ℂ => (m : ℂ) * w) z := by fun_prop
      exact (L.analyticOnNhd_weierstrassP _ hmp).comp_of_eq hf rfl

/-- The multiplication difference is doubly periodic and entire, hence *constant* (first Liouville
theorem). This is the multiplication formula `∑_v ℘(z + u_v) = m²·℘(mz) + c`. -/
private lemma exists_mulDiff_const {m : ℕ} [NeZero m] : ∃ c : ℂ, ∀ z, L.mulDiff m z = c := by
  have hdiff : Differentiable ℂ (L.mulDiff m) := fun z => (L.analyticAt_mulDiff z).differentiableAt
  have hell : L.IsEllipticWith (L.mulDiff m) := by
    refine ⟨fun z => (L.analyticAt_mulDiff z).meromorphicAt, ?_⟩
    intro z l
    simp only [mulDiff]
    congr 1
    · refine Finset.sum_congr rfl fun v _ => ?_
      rw [show z + (l : ℂ) + L.divPt m v = (z + L.divPt m v) + l by ring]
      exact L.weierstrassP_add_coe _ l
    · congr 1
      rw [show (m : ℂ) * (z + l) = m * z + m * l by ring]
      have hml : (m : ℂ) * (l : ℂ) ∈ L.lattice := by rw [← nsmul_eq_mul]; exact nsmul_mem l.2 m
      exact L.weierstrassP_add_coe (m * z) ⟨_, hml⟩
  obtain ⟨c, hc⟩ := hell.exists_eq_const_of_differentiable hdiff
  exact ⟨c, fun z => congrFun hc z⟩

/-- Iterated quasi-periodicity: `ζ(w + k·ω₁) = ζ(w) + k·η₁` for `w ∉ L`. -/
private lemma weierstrassZeta_add_nat_ω₁ {w : ℂ} (hw : w ∉ L.lattice) (k : ℕ) :
    L.weierstrassZeta (w + (k : ℂ) * L.ω₁) = L.weierstrassZeta w + (k : ℂ) * L.eta₁ := by
  induction k with
  | zero => simp
  | succ n ih =>
    have hmem : w + (n : ℂ) * L.ω₁ ∉ L.lattice := by
      intro hc
      apply hw
      have hn : (n : ℂ) * L.ω₁ ∈ L.lattice := by
        rw [← nsmul_eq_mul]; exact nsmul_mem L.ω₁_mem_lattice n
      simpa using sub_mem hc hn
    rw [show w + (↑(n + 1) : ℂ) * L.ω₁ = (w + (n : ℂ) * L.ω₁) + L.ω₁ by push_cast; ring,
      L.weierstrassZeta_add_ω₁ _ hmem, ih]
    push_cast; ring

/-- The ζ-combination `∑_v ζ(z + u_v) − m·ζ(mz)`, whose derivative is `−(mulDiff)` and which is
doubly periodic (the quasi-periods cancel). -/
private def zetaComb (m : ℕ) (z : ℂ) : ℂ :=
  (∑ v : Fin m × Fin m, L.weierstrassZeta (z + L.divPt m v)) - (m : ℂ) * L.weierstrassZeta (m * z)

/-- Off the `m`-torsion, `zetaComb` is differentiable with derivative `−(mulDiff)` (since
`ζ' = −℘`). -/
private lemma hasDerivAt_zetaComb {m : ℕ} [NeZero m] {z : ℂ} (hU : (m : ℂ) * z ∉ L.lattice) :
    HasDerivAt (L.zetaComb m) (-(L.mulDiff m z)) z := by
  have hda : ∀ p : ℂ, p ∉ L.lattice → HasDerivAt L.weierstrassZeta (-(L.weierstrassP p)) p := by
    intro p hp
    have hd := (L.differentiableOn_weierstrassZeta.differentiableAt
      (L.isClosed_lattice.isOpen_compl.mem_nhds hp)).hasDerivAt
    rwa [L.deriv_weierstrassZeta p hp] at hd
  have hz1 : ∀ v : Fin m × Fin m, HasDerivAt (fun w => L.weierstrassZeta (w + L.divPt m v))
      (-(L.weierstrassP (z + L.divPt m v))) z := by
    intro v
    have hp : z + L.divPt m v ∉ L.lattice := fun hc => hU (L.mul_mem_lattice_of_add_divPt_mem hc)
    exact (hda _ hp).comp_add_const z (L.divPt m v)
  have hsum : HasDerivAt (fun w => ∑ v : Fin m × Fin m, L.weierstrassZeta (w + L.divPt m v))
      (∑ v : Fin m × Fin m, -(L.weierstrassP (z + L.divPt m v))) z :=
    HasDerivAt.fun_sum (fun v _ => hz1 v)
  have hcomp2 : HasDerivAt (fun w => L.weierstrassZeta ((m : ℂ) * w))
      ((m : ℂ) * -(L.weierstrassP ((m : ℂ) * z))) z := by
    have h := HasDerivAt.scomp (𝕜 := ℂ) z (hda _ hU) ((hasDerivAt_id' z).const_mul (m : ℂ))
    simpa [Function.comp_def, mul_comm] using h
  have hterm2 : HasDerivAt (fun w => (m : ℂ) * L.weierstrassZeta ((m : ℂ) * w))
      ((m : ℂ) * ((m : ℂ) * -(L.weierstrassP ((m : ℂ) * z)))) z :=
    HasDerivAt.const_mul (m : ℂ) hcomp2
  have hcomb : HasDerivAt (L.zetaComb m)
      ((∑ v : Fin m × Fin m, -(L.weierstrassP (z + L.divPt m v)))
        - (m : ℂ) * ((m : ℂ) * -(L.weierstrassP ((m : ℂ) * z)))) z := hsum.sub hterm2
  convert hcomb using 1
  have hsn : (∑ v : Fin m × Fin m, -(L.weierstrassP (z + L.divPt m v)))
      = -(∑ v : Fin m × Fin m, L.weierstrassP (z + L.divPt m v)) :=
    Finset.sum_neg_distrib _
  rw [hsn]
  simp only [mulDiff]
  ring

/-- `zetaComb` is periodic in the direction `ω₁` on its domain: the `η₁`-contributions from the
sum (`m²·η₁`) and from the `m·ζ(mz)`-term (`m²·η₁`) cancel. -/
private lemma zetaComb_add_ω₁ {m : ℕ} [NeZero m] {z : ℂ} (hU : (m : ℂ) * z ∉ L.lattice) :
    L.zetaComb m (z + L.ω₁) = L.zetaComb m z := by
  have hsum1 : (∑ v : Fin m × Fin m, L.weierstrassZeta (z + L.ω₁ + L.divPt m v))
      = (∑ v : Fin m × Fin m, L.weierstrassZeta (z + L.divPt m v)) + (m : ℂ) ^ 2 * L.eta₁ := by
    have hterm : ∀ v : Fin m × Fin m, L.weierstrassZeta (z + L.ω₁ + L.divPt m v)
        = L.weierstrassZeta (z + L.divPt m v) + L.eta₁ := by
      intro v
      rw [show z + L.ω₁ + L.divPt m v = (z + L.divPt m v) + L.ω₁ by ring]
      exact L.weierstrassZeta_add_ω₁ _ (fun hc => hU (L.mul_mem_lattice_of_add_divPt_mem hc))
    rw [Finset.sum_congr rfl (fun v _ => hterm v), Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul]
    push_cast; ring
  have hmz1 : L.weierstrassZeta ((m : ℂ) * (z + L.ω₁))
      = L.weierstrassZeta ((m : ℂ) * z) + (m : ℂ) * L.eta₁ := by
    rw [show (m : ℂ) * (z + L.ω₁) = (m : ℂ) * z + (m : ℂ) * L.ω₁ by ring]
    exact L.weierstrassZeta_add_nat_ω₁ hU m
  simp only [zetaComb]
  rw [hsum1, hmz1]
  ring

/-- **The multiplication constant vanishes.** `zetaComb + c·z` has zero derivative on the connected
domain `{m·z ∉ L}`, hence is constant; comparing at `z` and `z + ω₁` (where `zetaComb` is periodic)
forces `c·ω₁ = 0`, so `c = 0`. -/
private lemma mulDiff_const_eq_zero {m : ℕ} [NeZero m] {c : ℂ}
    (hc : ∀ z, L.mulDiff m z = c) : c = 0 := by
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast (NeZero.pos m).ne'
  set B : Set ℂ := (fun z => (m : ℂ) * z) ⁻¹' (↑L.lattice) with hBdef
  have hmemB : ∀ x, x ∈ B ↔ (m : ℂ) * x ∈ L.lattice := fun x => Iff.rfl
  have hBcount : B.Countable := L.countable_lattice'.preimage (mul_right_injective₀ hm0)
  have hBclosed : IsClosed B := IsClosed.preimage (by fun_prop) L.isClosed_lattice
  have hUopen : IsOpen (Bᶜ : Set ℂ) := hBclosed.isOpen_compl
  have hUconn : IsPreconnected (Bᶜ : Set ℂ) :=
    (hBcount.isConnected_compl_of_one_lt_rank (by simp)).isPreconnected
  have hcount2 : (B ∪ (fun z => z + L.ω₁) ⁻¹' B).Countable :=
    hBcount.union (hBcount.preimage (add_left_injective L.ω₁))
  obtain ⟨z₀, hz₀⟩ := (hcount2.isConnected_compl_of_one_lt_rank (by simp)).nonempty
  rw [Set.mem_compl_iff, Set.mem_union, not_or] at hz₀
  obtain ⟨hz₀B, hz₀B'⟩ := hz₀
  have hUz₀ : (m : ℂ) * z₀ ∉ L.lattice := (hmemB z₀).not.mp hz₀B
  have hUz₀ω : (m : ℂ) * (z₀ + L.ω₁) ∉ L.lattice := (hmemB (z₀ + L.ω₁)).not.mp hz₀B'
  set F : ℂ → ℂ := fun z => L.zetaComb m z + c * z with hFdef
  have hFderiv : ∀ z ∈ (Bᶜ : Set ℂ), HasDerivAt F 0 z := by
    intro z hz
    have hU : (m : ℂ) * z ∉ L.lattice := (hmemB z).not.mp hz
    have hG := L.hasDerivAt_zetaComb hU
    rw [hc z] at hG
    have h2 : HasDerivAt (fun w => L.zetaComb m w + c * w) (-c + c * 1) z :=
      hG.fun_add ((hasDerivAt_id' z).const_mul c)
    have h3 : (-c + c * 1 : ℂ) = 0 := by ring
    rw [hFdef]
    exact h3 ▸ h2
  have hFdiff : DifferentiableOn ℂ F (Bᶜ) :=
    fun z hz => (hFderiv z hz).differentiableAt.differentiableWithinAt
  have hderivEq : (Bᶜ : Set ℂ).EqOn (deriv F) (deriv (fun _ => F z₀)) := by
    intro z hz
    rw [(hFderiv z hz).deriv, deriv_const']
  have hz₀U : z₀ ∈ (Bᶜ : Set ℂ) := hz₀B
  have hEqOn := hUopen.eqOn_of_deriv_eq hUconn hFdiff (differentiableOn_const _) hderivEq hz₀U rfl
  have e1 : F (z₀ + L.ω₁) = F z₀ := hEqOn hz₀B'
  have hper : L.zetaComb m (z₀ + L.ω₁) = L.zetaComb m z₀ := L.zetaComb_add_ω₁ hUz₀
  simp only [hFdef] at e1
  rw [hper] at e1
  have hcω : c * L.ω₁ = 0 := by linear_combination e1
  have hω₁ : L.ω₁ ≠ 0 := by simpa using L.indep.ne_zero 0
  exact (mul_eq_zero.mp hcω).resolve_right hω₁

/-- Milla's `theowpsum`: the sum of `℘` over all `m`-division points vanishes.
(From the vanishing of the second-highest coefficient in `thmbaker`.) -/
theorem theowpsum (m : ℕ) [NeZero m] :
    ∑ v ∈ Finset.univ.erase (0 : Fin m × Fin m), L.weierstrassP (L.divPt m v) = 0 := by
  obtain ⟨c, hc⟩ := L.exists_mulDiff_const (m := m)
  have h0 := hc 0
  rw [L.mulDiff_const_eq_zero hc] at h0
  simp only [mulDiff] at h0
  rw [mul_zero, L.weierstrassP_zero, mul_zero, sub_zero] at h0
  simp only [zero_add] at h0
  rw [← Finset.add_sum_erase Finset.univ (fun v => L.weierstrassP (L.divPt m v))
    (Finset.mem_univ (0 : Fin m × Fin m))] at h0
  have hd0 : L.divPt m (0 : Fin m × Fin m) = 0 := by simp [divPt]
  rw [hd0, L.weierstrassP_zero, zero_add] at h0
  exact h0

/-! ## `lemwpsigma`: the σ-quotient formula for `℘(v) − ℘(u)`

We prove `℘(v) − ℘(u) = σ(u+v)σ(u−v)/(σ(u)²σ(v)²)` (paper Lemma `lemwpsigma`) by the paper's
direct argument: fix `v ∉ L`; the difference `F(u) := σ(u+v)σ(u−v)/(σ(u)²σ(v)²) + ℘(u) − ℘(v)`
is elliptic in `u`, has its two double poles at `u ∈ L` cancel (Laurent computation via the
trailing coefficient `σ'(0) = 1` and the evenness `F(−u) = F(u)`), hence is entire and constant
(first Liouville theorem), and `F(v) = 0` since `σ(0) = 0`. -/

/-- The σ-product `Q(z) = ∏' (1 − z/ω)·exp(z/ω + z²/2ω²)` is entire (local copy of the private
`SigmaZeta` lemma, re-proved from the public locally-uniform product). -/
private lemma differentiable_sigmaProd :
    Differentiable ℂ
      (fun z ↦ ∏' l : {l : L.lattice // l ≠ 0}, weierstrassSigmaTerm z (l.1 : ℂ)) := by
  have hterm : ∀ w : ℂ, Differentiable ℂ (fun z ↦ weierstrassSigmaTerm z w) := by
    intro w; unfold weierstrassSigmaTerm; fun_prop
  rw [← differentiableOn_univ]
  refine (L.hasProdLocallyUniformly_weierstrassSigmaTerm.hasProdLocallyUniformlyOn).differentiableOn
    (.of_forall fun _ ↦ ?_) isOpen_univ
  simpa [Finset.prod_fn] using
    DifferentiableOn.finsetProd fun i _ ↦ (hterm (i.1 : ℂ)).differentiableOn

/-- `Q(0) = 1`. -/
private lemma sigmaProd_zero :
    (∏' l : {l : L.lattice // l ≠ 0}, weierstrassSigmaTerm (0 : ℂ) (l.1 : ℂ)) = 1 := by
  have h : (fun l : {l : L.lattice // l ≠ 0} ↦ weierstrassSigmaTerm (0 : ℂ) (l.1 : ℂ))
      = fun _ ↦ (1 : ℂ) := by funext n; simp [weierstrassSigmaTerm]
  rw [h, tprod_one]

/-- The trailing (leading Laurent) coefficient of `σ` at `0` is `σ'(0) = 1`. -/
private lemma trailingCoeff_sigma_zero :
    meromorphicTrailingCoeffAt L.weierstrassSigma 0 = 1 := by
  set Q := fun z ↦ ∏' l : {l : L.lattice // l ≠ 0}, weierstrassSigmaTerm z (l.1 : ℂ) with hQ
  have hQan : AnalyticAt ℂ Q 0 := (L.differentiable_sigmaProd).analyticAt 0
  have hQ0 : Q 0 = 1 := L.sigmaProd_zero
  have hEq : L.weierstrassSigma =ᶠ[𝓝[≠] (0 : ℂ)] fun z ↦ (z - 0) ^ (1 : ℤ) • Q z := by
    filter_upwards with z
    simp only [sub_zero, zpow_one, smul_eq_mul, hQ, weierstrassSigma]
  rw [hQan.meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE (n := 1)
    (by rw [hQ0]; exact one_ne_zero)
    hEq, hQ0]

open Classical in
/-- The meromorphic order of `σ` is `1` on the lattice and `0` off it. -/
private lemma sigma_meromorphicOrderAt (w : ℂ) :
    meromorphicOrderAt L.weierstrassSigma w = if w ∈ L.lattice then (1 : WithTop ℤ) else 0 := by
  classical
  by_cases hw : w ∈ L.lattice
  · rw [if_pos hw, L.meromorphicOrderAt_weierstrassSigma w hw]
  · rw [if_neg hw]
    have hAn : AnalyticAt ℂ L.weierstrassSigma w := L.differentiable_weierstrassSigma.analyticAt w
    rw [hAn.meromorphicOrderAt_eq,
      analyticOrderAt_eq_zero.mpr (.inr (L.weierstrassSigma_ne_zero hw))]
    simp

/-- Translating the argument of `σ` shifts the base point of the meromorphic order. -/
private lemma sigma_shift_meromorphicOrderAt (a w : ℂ) :
    meromorphicOrderAt (fun t => L.weierstrassSigma (t + a)) w
      = meromorphicOrderAt L.weierstrassSigma (w + a) := by
  have h := meromorphicOrderAt_comp_of_deriv_ne_zero (f := L.weierstrassSigma)
    (g := fun t => t + a) (x := w) (by fun_prop) (by simp)
  simpa only [Function.comp_def] using h

/-- At `a ∉ L` with `℘ a = c`, the zero of `℘ − c` has order `≥ 1`. -/
private lemma one_le_untop₀_meromorphicOrderAt {c a : ℂ} (ha : a ∉ L.lattice)
    (hc : L.weierstrassP a = c) :
    1 ≤ (meromorphicOrderAt (fun z => L.weierstrassP z - c) a).untop₀ := by
  set f : ℂ → ℂ := fun z => L.weierstrassP z - c with hf_def
  have hAn : AnalyticAt ℂ f a := by
    rw [hf_def]; have := L.analyticOnNhd_weierstrassP a ha; fun_prop
  have hfa : f a = 0 := by rw [hf_def]; simp [hc]
  have hz0 : analyticOrderAt f a ≠ 0 := hAn.analyticOrderAt_ne_zero.mpr hfa
  have hne : meromorphicOrderAt f a ≠ ⊤ := by
    have hmero : Meromorphic f := by rw [hf_def]; fun_prop
    have h0 : meromorphicOrderAt f 0 ≠ ⊤ := by
      rw [hf_def, L.meromorphicOrderAt_weierstrassP_sub L.lattice.zero_mem]
      exact WithTop.coe_ne_top
    exact (meromorphicOn_univ.2 hmero).meromorphicOrderAt_ne_top_of_isPreconnected
      isPreconnected_univ (Set.mem_univ 0) (Set.mem_univ a) h0
  rw [hAn.meromorphicOrderAt_eq] at hne ⊢
  rw [Ne, ENat.map_eq_top_iff] at hne
  lift analyticOrderAt f a to ℕ using hne with n hn
  rw [ENat.map_coe, WithTop.untop₀_coe]
  have : n ≠ 0 := by exact_mod_cast hz0
  omega

/-- **`℘` is 2-to-1**: for `z, v ∉ L` with `z − v ∉ L` and `z + v ∉ L`, the values differ,
`℘ z ≠ ℘ v` (contrapositive of `℘ z = ℘ v → z ≡ ±v mod L`). -/
theorem weierstrassP_ne_of_notMem {z v : ℂ} (hz : z ∉ L.lattice) (hv : v ∉ L.lattice)
    (hsub : z - v ∉ L.lattice) (hadd : z + v ∉ L.lattice) :
    L.weierstrassP z ≠ L.weierstrassP v := by
  intro hEq
  set c := L.weierstrassP v with hc
  obtain ⟨p, hpf, hpl⟩ := L.exists_mem_fund z
  obtain ⟨q, hqf, hql⟩ := L.exists_mem_fund v
  obtain ⟨r, hrf, hrl⟩ := L.exists_mem_fund (-v)
  -- the three reps are not `0`, hence not in `L`
  have hp0 : p ≠ 0 := fun h => hz (by simpa [h] using hpl)
  have hq0 : q ≠ 0 := fun h => hv (by simpa [h] using hql)
  have hr0 : r ≠ 0 := fun h => hv (by
    have : (-v) ∈ L.lattice := by simpa [h] using hrl
    simpa using neg_mem this)
  have hpnl : p ∉ L.lattice := L.notMem_lattice_of_mem_fund hpf hp0
  have hqnl : q ∉ L.lattice := L.notMem_lattice_of_mem_fund hqf hq0
  have hrnl : r ∉ L.lattice := L.notMem_lattice_of_mem_fund hrf hr0
  -- the ℘-values at the reps all equal `c`
  have key : ∀ {w s : ℂ}, w - s ∈ L.lattice → L.weierstrassP s = L.weierstrassP w := by
    intro w s h
    have := L.weierstrassP_sub_coe w ⟨w - s, h⟩
    rwa [show w - ((⟨w - s, h⟩ : L.lattice) : ℂ) = s by simp] at this
  have hPp : L.weierstrassP p = c := (key hpl).trans hEq
  have hPq : L.weierstrassP q = c := (key hql).trans hc.symm
  have hPr : L.weierstrassP r = c := by
    rw [key hrl, L.weierstrassP_neg]
  -- p ≠ q and p ≠ r
  have hpq : p ≠ q := by
    intro h; apply hsub
    have : z - v = (z - p) - (v - q) := by rw [h]; ring
    rw [this]; exact sub_mem hpl hql
  have hpr : p ≠ r := by
    intro h; apply hadd
    have : z + v = (z - p) - (-v - r) := by rw [h]; ring
    rw [this]; exact sub_mem hpl hrl
  by_cases hqr : q = r
  · -- `v` is 2-torsion: `q` is a double zero
    have h2v : 2 * v ∈ L.lattice := by
      have h1 : v - q ∈ L.lattice := hql
      have h2 : -v - r ∈ L.lattice := hrl
      rw [hqr] at h1
      have := add_mem h1 h2
      have he : (v - r) + (-v - r) = -(2 * r) := by ring
      rw [he] at this
      have h2r : 2 * r ∈ L.lattice := by simpa using neg_mem this
      -- v ≡ r (from hqr), so 2v ≡ 2r ∈ L
      have hvr : v - r ∈ L.lattice := hqr ▸ hql
      have : 2 * v - 2 * r ∈ L.lattice := by
        have : 2 * v - 2 * r = 2 • (v - r) := by rw [nsmul_eq_mul]; push_cast; ring
        rw [this]; exact nsmul_mem hvr 2
      simpa using add_mem this h2r
    have hderiv_q : L.derivWeierstrassP q = 0 := by
      have : L.derivWeierstrassP q = L.derivWeierstrassP v := by
        have := L.derivWeierstrassP_sub_coe v ⟨v - q, hql⟩
        rwa [show v - ((⟨v - q, hql⟩ : L.lattice) : ℂ) = q by simp] at this
      rw [this]; exact (L.derivWeierstrassP_eq_zero_iff hv).mpr h2v
    have h2q : 2 ≤ (meromorphicOrderAt (fun w => L.weierstrassP w - c) q).untop₀ :=
      L.two_le_untop₀_meromorphicOrderAt hqnl hPq hderiv_q
    have h1p : 1 ≤ (meromorphicOrderAt (fun w => L.weierstrassP w - c) p).untop₀ :=
      L.one_le_untop₀_meromorphicOrderAt hpnl hPp
    have hbound := L.sum_untop₀_meromorphicOrderAt_le_two c {p, q}
      (fun a ha => by rcases Finset.mem_insert.mp ha with h | h
                      · exact h ▸ hpf
                      · exact (Finset.mem_singleton.mp h) ▸ hqf)
      (fun a ha => by rcases Finset.mem_insert.mp ha with h | h
                      · exact h ▸ hpnl
                      · exact (Finset.mem_singleton.mp h) ▸ hqnl)
      (fun a ha => by rcases Finset.mem_insert.mp ha with h | h
                      · exact h ▸ hPp
                      · exact (Finset.mem_singleton.mp h) ▸ hPq)
    rw [Finset.sum_pair hpq] at hbound
    omega
  · -- three distinct simple zeros
    have h1p : 1 ≤ (meromorphicOrderAt (fun w => L.weierstrassP w - c) p).untop₀ :=
      L.one_le_untop₀_meromorphicOrderAt hpnl hPp
    have h1q : 1 ≤ (meromorphicOrderAt (fun w => L.weierstrassP w - c) q).untop₀ :=
      L.one_le_untop₀_meromorphicOrderAt hqnl hPq
    have h1r : 1 ≤ (meromorphicOrderAt (fun w => L.weierstrassP w - c) r).untop₀ :=
      L.one_le_untop₀_meromorphicOrderAt hrnl hPr
    have hbound := L.sum_untop₀_meromorphicOrderAt_le_two c {p, q, r}
      (fun a ha => by rcases Finset.mem_insert.mp ha with h | h
                      · exact h ▸ hpf
                      · rcases Finset.mem_insert.mp h with h | h
                        · exact h ▸ hqf
                        · exact (Finset.mem_singleton.mp h) ▸ hrf)
      (fun a ha => by rcases Finset.mem_insert.mp ha with h | h
                      · exact h ▸ hpnl
                      · rcases Finset.mem_insert.mp h with h | h
                        · exact h ▸ hqnl
                        · exact (Finset.mem_singleton.mp h) ▸ hrnl)
      (fun a ha => by rcases Finset.mem_insert.mp ha with h | h
                      · exact h ▸ hPp
                      · rcases Finset.mem_insert.mp h with h | h
                        · exact h ▸ hPq
                        · exact (Finset.mem_singleton.mp h) ▸ hPr)
    rw [Finset.sum_insert (by simp [hpq, hpr]), Finset.sum_pair hqr] at hbound
    omega

/-- One period step of the σ-quotient `B(w) = σ(w+v)σ(w−v)/σ(w)²`: the quasi-period exponentials
cancel, so `B(w+ω) = B(w)` in a good period direction `ω`. -/
private theorem sigmaQuot_add_period_aux {ω η : ℂ} (v : ℂ)
    (hbase : ∀ w, L.weierstrassSigma (w + ω)
      = -Complex.exp (η * (w + ω / 2)) * L.weierstrassSigma w) (w : ℂ) :
    L.weierstrassSigma (w + ω + v) * L.weierstrassSigma (w + ω - v)
        / L.weierstrassSigma (w + ω) ^ 2
      = L.weierstrassSigma (w + v) * L.weierstrassSigma (w - v) / L.weierstrassSigma w ^ 2 := by
  have hne : Complex.exp (η * (w + ω / 2)) ≠ 0 := Complex.exp_ne_zero _
  have he : Complex.exp (η * (w + v + ω / 2)) * Complex.exp (η * (w - v + ω / 2))
      = Complex.exp (η * (w + ω / 2)) ^ 2 := by
    rw [← Complex.exp_add, sq, ← Complex.exp_add]; congr 1; ring
  rw [show w + ω + v = (w + v) + ω by ring, show w + ω - v = (w - v) + ω by ring,
    hbase (w + v), hbase (w - v), hbase w,
    show (-Complex.exp (η * (w + v + ω / 2)) * L.weierstrassSigma (w + v))
        * (-Complex.exp (η * (w - v + ω / 2)) * L.weierstrassSigma (w - v))
        / (-Complex.exp (η * (w + ω / 2)) * L.weierstrassSigma w) ^ 2
      = (Complex.exp (η * (w + v + ω / 2)) * Complex.exp (η * (w - v + ω / 2)))
        * (L.weierstrassSigma (w + v) * L.weierstrassSigma (w - v))
        / (Complex.exp (η * (w + ω / 2)) ^ 2 * L.weierstrassSigma w ^ 2) by ring,
    he, mul_div_mul_left _ _ (pow_ne_zero 2 hne)]

/-! ### Assembly of `lemwpsigma` (paper Lemma `lemwpsigma`)

`℘(v) − ℘(u) = σ(u+v)·σ(u−v)/(σ(u)²σ(v)²)` for `u, v ∉ L`, via the workhorse lemma:
the σ-quotient `A(u) = σ(u+v)σ(u−v)/σ(u)²` and `g(u) = ℘(u) − ℘(v)` are elliptic in `u`
with identical divisors, so `A = c·g` up to a codiscrete set; the constant is pinned by
the trailing coefficients at `u = 0` (`c = −σ(v)²`), and the identity upgrades to all
`u ∉ L` by the identity theorem on the connected set `Lᶜ`. -/

/-- Translating the argument shifts the base point of the meromorphic order (generic
form of `sigma_shift_meromorphicOrderAt`). -/
private lemma meromorphicOrderAt_shift (f : ℂ → ℂ) (a w : ℂ) :
    meromorphicOrderAt (fun t => f (t + a)) w = meromorphicOrderAt f (w + a) := by
  have h := meromorphicOrderAt_comp_of_deriv_ne_zero (f := f)
    (g := fun t => t + a) (x := w) (by fun_prop) (by simp)
  simpa only [Function.comp_def] using h

/-- `℘` takes equal values at points that differ by a lattice vector. -/
private lemma weierstrassP_eq_of_sub_mem {w s : ℂ} (h : w - s ∈ L.lattice) :
    L.weierstrassP s = L.weierstrassP w := by
  have := L.weierstrassP_sub_coe w ⟨w - s, h⟩
  rwa [show w - ((⟨w - s, h⟩ : L.lattice) : ℂ) = s by simp] at this

/-- The meromorphic order of `℘ − c` is invariant under lattice translation of the base
point. -/
private lemma wpsub_meromorphicOrderAt_add_mem {c l : ℂ} (hl : l ∈ L.lattice) (z : ℂ) :
    meromorphicOrderAt (fun w => L.weierstrassP w - c) (z + l)
      = meromorphicOrderAt (fun w => L.weierstrassP w - c) z := by
  have h := meromorphicOrderAt_shift (fun w => L.weierstrassP w - c) l z
  have heq : (fun t => L.weierstrassP (t + l) - c) = fun t => L.weierstrassP t - c := by
    funext t
    rw [show t + l = t + ((⟨l, hl⟩ : L.lattice) : ℂ) from rfl, L.weierstrassP_add_coe]
  rw [heq] at h
  exact h.symm

/-- Order of `℘ − c` at a *simple* zero (`℘' ≠ 0` there). -/
private lemma wpsub_meromorphicOrderAt_eq_one {c a : ℂ} (ha : a ∉ L.lattice)
    (hc : L.weierstrassP a = c) (hd : L.derivWeierstrassP a ≠ 0) :
    meromorphicOrderAt (fun z => L.weierstrassP z - c) a = 1 := by
  have hAn : AnalyticAt ℂ (fun z => L.weierstrassP z - c) a := by
    have := L.analyticOnNhd_weierstrassP a ha; fun_prop
  have h1 : analyticOrderAt (fun z => L.weierstrassP z - c) a = 1 := by
    apply hAn.analyticOrderAt_eq_one_of_zero_deriv_ne_zero (by simp [hc])
    rw [deriv_sub_const, L.deriv_weierstrassP]
    exact hd
  rw [hAn.meromorphicOrderAt_eq, h1]
  rfl

/-- Order of `℘ − c` at a *double* zero (a two-torsion point, `℘' = 0` there). -/
private lemma wpsub_meromorphicOrderAt_eq_two {c a : ℂ} (ha : a ∉ L.lattice)
    (hc : L.weierstrassP a = c) (hd : L.derivWeierstrassP a = 0) :
    meromorphicOrderAt (fun z => L.weierstrassP z - c) a = 2 := by
  set f : ℂ → ℂ := fun z => L.weierstrassP z - c with hf
  have h2 : 2 ≤ (meromorphicOrderAt f a).untop₀ :=
    L.two_le_untop₀_meromorphicOrderAt ha hc hd
  have hne : meromorphicOrderAt f a ≠ ⊤ := by
    intro htop; rw [htop] at h2; simp at h2
  -- upper bound via translation to the fundamental parallelogram and the counting bound
  obtain ⟨p, hpf, hpl⟩ := L.exists_mem_fund a
  have hordeq : meromorphicOrderAt f a = meromorphicOrderAt f p := by
    have h := L.wpsub_meromorphicOrderAt_add_mem (c := c) hpl p
    rw [show p + (a - p) = a by ring] at h
    exact h
  have hpnl : p ∉ L.lattice := by
    intro hplat
    exact ha (by simpa using add_mem hplat hpl)
  have hpc : L.weierstrassP p = c := by rw [L.weierstrassP_eq_of_sub_mem hpl, hc]
  have hbound := L.sum_untop₀_meromorphicOrderAt_le_two c {p}
    (fun x hx => by rw [Finset.mem_singleton.mp hx]; exact hpf)
    (fun x hx => by rw [Finset.mem_singleton.mp hx]; exact hpnl)
    (fun x hx => by rw [Finset.mem_singleton.mp hx]; exact hpc)
  rw [Finset.sum_singleton, ← hf] at hbound
  rw [hordeq] at h2 hne ⊢
  lift meromorphicOrderAt f p to ℤ using hne with n hn
  rw [WithTop.untop₀_coe] at h2 hbound
  rw [le_antisymm hbound h2]
  rfl

/-- Order of `℘ − c` at a point where `℘ ≠ c`. -/
private lemma wpsub_meromorphicOrderAt_eq_zero {c a : ℂ} (ha : a ∉ L.lattice)
    (hne : L.weierstrassP a ≠ c) :
    meromorphicOrderAt (fun z => L.weierstrassP z - c) a = 0 := by
  have hAn : AnalyticAt ℂ (fun z => L.weierstrassP z - c) a := by
    have := L.analyticOnNhd_weierstrassP a ha; fun_prop
  rw [hAn.meromorphicOrderAt_eq,
    analyticOrderAt_eq_zero.mpr (.inr (by simpa using sub_ne_zero.mpr hne))]
  simp

/-- The meromorphic order of the σ-quotient `A(w) = σ(w+v)σ(w−v)/σ(w)²` decomposes as a
sum of orders of shifted σ's. -/
private lemma sigmaQuot_meromorphicOrderAt (v z : ℂ) :
    meromorphicOrderAt (fun w => L.weierstrassSigma (w + v) * L.weierstrassSigma (w - v)
        / L.weierstrassSigma w ^ 2) z
      = meromorphicOrderAt L.weierstrassSigma (z + v)
        + meromorphicOrderAt L.weierstrassSigma (z - v)
        - 2 * meromorphicOrderAt L.weierstrassSigma z := by
  have hσa : ∀ x : ℂ, AnalyticAt ℂ L.weierstrassSigma x := fun x =>
    L.differentiable_weierstrassSigma.analyticAt x
  have hm1 : MeromorphicAt (fun w => L.weierstrassSigma (w + v)) z := by
    have : AnalyticAt ℂ (fun w : ℂ => L.weierstrassSigma (w + v)) z := by
      have := hσa (z + v); fun_prop
    exact this.meromorphicAt
  have hm2 : MeromorphicAt (fun w => L.weierstrassSigma (w - v)) z := by
    have : AnalyticAt ℂ (fun w : ℂ => L.weierstrassSigma (w - v)) z := by
      have := hσa (z - v); fun_prop
    exact this.meromorphicAt
  have hm3 : MeromorphicAt (fun w => L.weierstrassSigma w ^ 2) z :=
    ((hσa z).fun_pow 2).meromorphicAt
  have hshift1 : meromorphicOrderAt (fun w => L.weierstrassSigma (w + v)) z
      = meromorphicOrderAt L.weierstrassSigma (z + v) :=
    L.sigma_shift_meromorphicOrderAt v z
  have hshift2 : meromorphicOrderAt (fun w => L.weierstrassSigma (w - v)) z
      = meromorphicOrderAt L.weierstrassSigma (z - v) := by
    have h := L.sigma_shift_meromorphicOrderAt (-v) z
    simpa [sub_eq_add_neg] using h
  have hpow : meromorphicOrderAt (fun w => L.weierstrassSigma w ^ 2) z
      = 2 * meromorphicOrderAt L.weierstrassSigma z := by
    rw [show (fun w => L.weierstrassSigma w ^ 2) = L.weierstrassSigma ^ 2 from rfl,
      meromorphicOrderAt_pow (hσa z).meromorphicAt]
    norm_num
  rw [show (fun w => L.weierstrassSigma (w + v) * L.weierstrassSigma (w - v)
        / L.weierstrassSigma w ^ 2)
      = ((fun w => L.weierstrassSigma (w + v)) * (fun w => L.weierstrassSigma (w - v)))
        / (fun w => L.weierstrassSigma w ^ 2) from rfl,
    meromorphicOrderAt_div (hm1.mul hm2) hm3,
    meromorphicOrderAt_mul hm1 hm2, hshift1, hshift2, hpow]

/-- **Divisor match** for `lemwpsigma`: the σ-quotient `A` and `℘ − ℘(v)` have the same
meromorphic order at every point. -/
private lemma sigmaQuot_order_eq {v : ℂ} (hv : v ∉ L.lattice) (z : ℂ) :
    meromorphicOrderAt (fun w => L.weierstrassSigma (w + v) * L.weierstrassSigma (w - v)
        / L.weierstrassSigma w ^ 2) z
      = meromorphicOrderAt (fun w => L.weierstrassP w - L.weierstrassP v) z := by
  rw [L.sigmaQuot_meromorphicOrderAt v z, L.sigma_meromorphicOrderAt (z + v),
    L.sigma_meromorphicOrderAt (z - v), L.sigma_meromorphicOrderAt z]
  by_cases hz : z ∈ L.lattice
  · have hzv : z + v ∉ L.lattice := fun h => hv (by simpa using sub_mem h hz)
    have hzv' : z - v ∉ L.lattice := fun h => hv (by simpa using sub_mem hz h)
    rw [if_neg hzv, if_neg hzv', if_pos hz, L.meromorphicOrderAt_weierstrassP_sub hz]
    norm_num
  · rw [if_neg hz]
    by_cases hsub : z - v ∈ L.lattice
    · have hPz : L.weierstrassP z = L.weierstrassP v :=
        (L.weierstrassP_eq_of_sub_mem hsub).symm
      by_cases hadd : z + v ∈ L.lattice
      · have h2z : 2 * z ∈ L.lattice := by
          have h := add_mem hsub hadd
          rwa [show z - v + (z + v) = 2 * z by ring] at h
        rw [if_pos hadd, if_pos hsub,
          L.wpsub_meromorphicOrderAt_eq_two hz hPz
            ((L.derivWeierstrassP_eq_zero_iff hz).mpr h2z)]
        norm_num
      · have h2z : 2 * z ∉ L.lattice := by
          intro h
          exact hadd (by
            rw [show z + v = 2 * z - (z - v) by ring]; exact sub_mem h hsub)
        have hd : L.derivWeierstrassP z ≠ 0 := fun h0 =>
          h2z ((L.derivWeierstrassP_eq_zero_iff hz).mp h0)
        rw [if_neg hadd, if_pos hsub, L.wpsub_meromorphicOrderAt_eq_one hz hPz hd]
        norm_num
    · by_cases hadd : z + v ∈ L.lattice
      · have hPz : L.weierstrassP z = L.weierstrassP v := by
          have hsm : z - (-v) ∈ L.lattice := by rwa [sub_neg_eq_add]
          rw [← L.weierstrassP_neg v]
          exact (L.weierstrassP_eq_of_sub_mem hsm).symm
        have h2z : 2 * z ∉ L.lattice := by
          intro h
          exact hsub (by
            rw [show z - v = 2 * z - (z + v) by ring]; exact sub_mem h hadd)
        have hd : L.derivWeierstrassP z ≠ 0 := fun h0 =>
          h2z ((L.derivWeierstrassP_eq_zero_iff hz).mp h0)
        rw [if_pos hadd, if_neg hsub, L.wpsub_meromorphicOrderAt_eq_one hz hPz hd]
        norm_num
      · have hPne : L.weierstrassP z ≠ L.weierstrassP v :=
          L.weierstrassP_ne_of_notMem hz hv hsub hadd
        rw [if_neg hadd, if_neg hsub, L.wpsub_meromorphicOrderAt_eq_zero hz hPne]
        norm_num

/-- A function periodic in a single direction `p` is invariant under integer multiples
of `p` (generic form of `Fm_add_intmul`). -/
private lemma periodic_add_intmul {F : ℂ → ℂ} {p : ℂ} (hp : ∀ w, F (w + p) = F w)
    (a : ℤ) (w : ℂ) : F (w + a * p) = F w := by
  have hpneg : ∀ x, F (x - p) = F x := by
    intro x
    have := hp (x - p)
    rw [show x - p + p = x by ring] at this
    exact this.symm
  induction a using Int.induction_on with
  | zero => simp
  | succ k ih =>
    have heq : w + ((↑k + 1 : ℤ) : ℂ) * p = (w + (↑k : ℤ) * p) + p := by push_cast; ring
    rw [heq, hp, ih]
  | pred k ih =>
    have heq : w + ((-↑k - 1 : ℤ) : ℂ) * p = (w + (-↑k : ℤ) * p) - p := by push_cast; ring
    rw [heq, hpneg, ih]

/-- A function periodic in the two directions `ω₁, ω₂` is periodic for the full lattice. -/
private lemma periodic_lattice {F : ℂ → ℂ}
    (h1 : ∀ w, F (w + L.ω₁) = F w) (h2 : ∀ w, F (w + L.ω₂) = F w)
    {ω : ℂ} (hω : ω ∈ L.lattice) (z : ℂ) : F (z + ω) = F z := by
  obtain ⟨a, b, hab⟩ := PeriodPair.mem_lattice.mp hω
  rw [← hab, show z + (↑a * L.ω₁ + ↑b * L.ω₂) = (z + ↑a * L.ω₁) + ↑b * L.ω₂ by ring,
    periodic_add_intmul h2 b, periodic_add_intmul h1 a]

/-- The σ-quotient `A(w) = σ(w+v)σ(w−v)/σ(w)²` is elliptic (in `w`). -/
private lemma sigmaQuot_isElliptic (v : ℂ) :
    L.IsEllipticWith (fun w => L.weierstrassSigma (w + v) * L.weierstrassSigma (w - v)
        / L.weierstrassSigma w ^ 2) := by
  have hσa : ∀ x : ℂ, AnalyticAt ℂ L.weierstrassSigma x := fun x =>
    L.differentiable_weierstrassSigma.analyticAt x
  constructor
  · intro z
    have h1 : AnalyticAt ℂ (fun w : ℂ => L.weierstrassSigma (w + v)) z := by
      have := hσa (z + v); fun_prop
    have h2 : AnalyticAt ℂ (fun w : ℂ => L.weierstrassSigma (w - v)) z := by
      have := hσa (z - v); fun_prop
    exact (h1.meromorphicAt.mul h2.meromorphicAt).div (((hσa z).fun_pow 2).meromorphicAt)
  · intro z l
    have hbase1 : ∀ w, L.weierstrassSigma (w + L.ω₁)
        = -Complex.exp (L.eta₁ * (w + L.ω₁ / 2)) * L.weierstrassSigma w :=
      L.sigma_add_period_aux L.ω₁_mem_lattice L.ω₁_div_two_notMem_lattice
        (fun z hz ↦ L.weierstrassZeta_add_ω₁ z hz)
    have hbase2 : ∀ w, L.weierstrassSigma (w + L.ω₂)
        = -Complex.exp (L.eta₂ * (w + L.ω₂ / 2)) * L.weierstrassSigma w :=
      L.sigma_add_period_aux L.ω₂_mem_lattice L.ω₂_div_two_notMem_lattice
        (fun z hz ↦ L.weierstrassZeta_add_ω₂ z hz)
    exact L.periodic_lattice
      (F := fun w => L.weierstrassSigma (w + v) * L.weierstrassSigma (w - v)
        / L.weierstrassSigma w ^ 2)
      (fun w => L.sigmaQuot_add_period_aux v hbase1 w)
      (fun w => L.sigmaQuot_add_period_aux v hbase2 w) l.2 z

/-- The trailing coefficient of `℘ − c` at `0` is `1` (from `℘(z) ≈ z⁻²`). -/
private lemma trailingCoeff_wpsub_zero (c : ℂ) :
    meromorphicTrailingCoeffAt (fun z => L.weierstrassP z - c) 0 = 1 := by
  set h : ℂ → ℂ := fun z => 1 + z ^ 2 * (L.weierstrassPExcept 0 z - c) with hh
  have hAn : AnalyticAt ℂ h 0 := by
    have := L.analyticAt_weierstrassPExcept 0
    fun_prop
  have h0 : h 0 = 1 := by simp [hh]
  have hEq : (fun z => L.weierstrassP z - c) =ᶠ[𝓝[≠] (0 : ℂ)]
      fun z => (z - 0) ^ (-2 : ℤ) • h z := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    have hz0 : z ≠ 0 := hz
    have hP : L.weierstrassP z = L.weierstrassPExcept 0 z + (z ^ 2)⁻¹ := by
      have hdef := L.weierstrassPExcept_def (0 : L.lattice) z
      simp only [ZeroMemClass.coe_zero, sub_zero] at hdef
      rw [hdef]; ring
    have hz2 : (z : ℂ) ^ 2 ≠ 0 := pow_ne_zero _ hz0
    rw [hP, hh]
    simp only [sub_zero, smul_eq_mul]
    rw [show (z : ℂ) ^ (-2 : ℤ) = (z ^ 2)⁻¹ by
      rw [zpow_neg, ← zpow_natCast z 2]; norm_num]
    field_simp
    ring
  rw [hAn.meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE
    (by rw [h0]; exact one_ne_zero) hEq, h0]

/-- The trailing coefficient of the σ-quotient `A` at `0` is `−σ(v)²`. -/
private lemma trailingCoeff_sigmaQuot_zero {v : ℂ} (hv : v ∉ L.lattice) :
    meromorphicTrailingCoeffAt (fun w => L.weierstrassSigma (w + v)
        * L.weierstrassSigma (w - v) / L.weierstrassSigma w ^ 2) 0
      = -(L.weierstrassSigma v ^ 2) := by
  have hσa : ∀ x : ℂ, AnalyticAt ℂ L.weierstrassSigma x := fun x =>
    L.differentiable_weierstrassSigma.analyticAt x
  have hAn1 : AnalyticAt ℂ (fun w : ℂ => L.weierstrassSigma (w + v)) 0 := by
    have := hσa (0 + v); fun_prop
  have hAn2 : AnalyticAt ℂ (fun w : ℂ => L.weierstrassSigma (w - v)) 0 := by
    have := hσa (0 - v); fun_prop
  have hσv : L.weierstrassSigma v ≠ 0 := L.weierstrassSigma_ne_zero hv
  have h1 : meromorphicTrailingCoeffAt (fun w => L.weierstrassSigma (w + v)) 0
      = L.weierstrassSigma v := by
    rw [hAn1.meromorphicTrailingCoeffAt_of_ne_zero (by simpa using hσv)]
    simp
  have h2 : meromorphicTrailingCoeffAt (fun w => L.weierstrassSigma (w - v)) 0
      = -L.weierstrassSigma v := by
    have hne : L.weierstrassSigma (0 - v) ≠ 0 := by
      rw [zero_sub, L.weierstrassSigma_neg]
      simpa using hσv
    rw [hAn2.meromorphicTrailingCoeffAt_of_ne_zero hne, zero_sub, L.weierstrassSigma_neg]
  have h3 : meromorphicTrailingCoeffAt (fun w => L.weierstrassSigma w ^ 2) 0 = 1 := by
    have h := MeromorphicAt.meromorphicTrailingCoeffAt_fun_pow (n := 2)
      (f := L.weierstrassSigma) (x := 0) ((hσa 0).meromorphicAt)
    rw [h, L.trailingCoeff_sigma_zero, one_pow]
  have hstep : meromorphicTrailingCoeffAt (fun w => L.weierstrassSigma (w + v)
      * L.weierstrassSigma (w - v) / L.weierstrassSigma w ^ 2) 0
      = meromorphicTrailingCoeffAt (fun w => L.weierstrassSigma (w + v)
          * L.weierstrassSigma (w - v)) 0
        * (meromorphicTrailingCoeffAt (fun w => L.weierstrassSigma w ^ 2) 0)⁻¹ := by
    have hM1 : MeromorphicAt
        (fun w => L.weierstrassSigma (w + v) * L.weierstrassSigma (w - v)) 0 :=
      hAn1.meromorphicAt.mul hAn2.meromorphicAt
    have hM2 : MeromorphicAt (fun w => (L.weierstrassSigma w ^ 2)⁻¹) 0 :=
      (((hσa 0).fun_pow 2).meromorphicAt).inv
    rw [show (fun w => L.weierstrassSigma (w + v) * L.weierstrassSigma (w - v)
          / L.weierstrassSigma w ^ 2)
        = fun w => (L.weierstrassSigma (w + v) * L.weierstrassSigma (w - v))
            * (L.weierstrassSigma w ^ 2)⁻¹ from funext fun w => div_eq_mul_inv _ _,
      MeromorphicAt.meromorphicTrailingCoeffAt_fun_mul hM1 hM2,
      meromorphicTrailingCoeffAt_fun_inv]
  rw [hstep, MeromorphicAt.meromorphicTrailingCoeffAt_fun_mul hAn1.meromorphicAt
    hAn2.meromorphicAt, h1, h2, h3]
  ring

/-- Milla's `lemwpsigma`: for `u, v ∉ L`,
`℘(v) − ℘(u) = σ(u+v)·σ(u−v)/(σ(u)²·σ(v)²)`. -/
theorem lemwpsigma {u v : ℂ} (hu : u ∉ L.lattice) (hv : v ∉ L.lattice) :
    L.weierstrassP v - L.weierstrassP u
      = L.weierstrassSigma (u + v) * L.weierstrassSigma (u - v)
        / (L.weierstrassSigma u ^ 2 * L.weierstrassSigma v ^ 2) := by
  set A : ℂ → ℂ := fun w => L.weierstrassSigma (w + v) * L.weierstrassSigma (w - v)
      / L.weierstrassSigma w ^ 2 with hA
  set g : ℂ → ℂ := fun w => L.weierstrassP w - L.weierstrassP v with hg
  have hAell : L.IsEllipticWith A := L.sigmaQuot_isElliptic v
  have hgell : L.IsEllipticWith g := L.isEllipticWith_weierstrassP_sub _
  obtain ⟨c, hc0, hcod⟩ := hAell.exists_const_mul_of_meromorphicOrderAt_eq hgell
    (fun z => L.sigmaQuot_order_eq hv z)
  -- pin the constant via trailing coefficients at `0`
  have hev0 : ∀ᶠ z in 𝓝[≠] (0 : ℂ), A z = c * g z := by
    have hm := mem_codiscrete.mp hcod 0
    rwa [Filter.disjoint_principal_right, compl_compl] at hm
  have htcA : meromorphicTrailingCoeffAt A 0 = -(L.weierstrassSigma v ^ 2) :=
    L.trailingCoeff_sigmaQuot_zero hv
  have htcg : meromorphicTrailingCoeffAt g 0 = 1 := L.trailingCoeff_wpsub_zero _
  have hceq : c = -(L.weierstrassSigma v ^ 2) := by
    have hcongr : meromorphicTrailingCoeffAt A 0
        = meromorphicTrailingCoeffAt (fun z => c * g z) 0 :=
      meromorphicTrailingCoeffAt_congr_nhdsNE hev0
    rw [htcA, MeromorphicAt.meromorphicTrailingCoeffAt_fun_mul
      (MeromorphicAt.const c 0) (hgell.1 0), meromorphicTrailingCoeffAt_const, htcg,
      mul_one] at hcongr
    exact hcongr.symm
  -- pointwise upgrade on the connected set `Lᶜ`
  have hAan : AnalyticOnNhd ℂ A (↑L.lattice)ᶜ := by
    intro x hx
    have hσa : ∀ y : ℂ, AnalyticAt ℂ L.weierstrassSigma y := fun y =>
      L.differentiable_weierstrassSigma.analyticAt y
    have h1 : AnalyticAt ℂ (fun w : ℂ => L.weierstrassSigma (w + v)) x := by
      have := hσa (x + v); fun_prop
    have h2 : AnalyticAt ℂ (fun w : ℂ => L.weierstrassSigma (w - v)) x := by
      have := hσa (x - v); fun_prop
    exact (h1.mul h2).div ((hσa x).pow 2)
      (pow_ne_zero 2 (L.weierstrassSigma_ne_zero hx))
  have hcgan : AnalyticOnNhd ℂ (fun z => c * g z) (↑L.lattice)ᶜ := by
    intro x hx
    have := L.analyticOnNhd_weierstrassP x hx
    fun_prop
  have hconn : IsPreconnected ((↑L.lattice : Set ℂ)ᶜ) :=
    (L.countable_lattice'.isConnected_compl_of_one_lt_rank (by simp)).isPreconnected
  have hx₀ : L.ω₁ / 2 ∈ ((↑L.lattice : Set ℂ)ᶜ) := L.ω₁_div_two_notMem_lattice
  have hfreq : ∃ᶠ z in 𝓝[≠] (L.ω₁ / 2), A z = c * g z := by
    have hm := mem_codiscrete.mp hcod (L.ω₁ / 2)
    rw [Filter.disjoint_principal_right, compl_compl] at hm
    exact Filter.Eventually.frequently hm
  have hEqOn := hAan.eqOn_of_preconnected_of_frequently_eq hcgan hconn hx₀ hfreq
  have hAu : A u = c * g u := hEqOn hu
  -- final algebra
  have hσu : L.weierstrassSigma u ≠ 0 := L.weierstrassSigma_ne_zero hu
  have hσv : L.weierstrassSigma v ≠ 0 := L.weierstrassSigma_ne_zero hv
  rw [hceq] at hAu
  simp only [hA, hg] at hAu
  rw [div_eq_iff (pow_ne_zero 2 hσu)] at hAu
  rw [eq_div_iff (mul_ne_zero (pow_ne_zero 2 hσu) (pow_ne_zero 2 hσv))]
  linear_combination -hAu

/-! ### `propfmprod`: `F_m(z)² = m²·∏_{v ≠ 0} (℘(z) − ℘(u_v))` (paper Thm. `propfmprod`)

Proved by the same workhorse scheme: both sides are elliptic with identical divisors
(`−2(m²−1)` on `L`, total order `2` on each nonzero `m`-torsion class, `0` elsewhere),
and the constant is pinned by the trailing coefficients at `0`
(`F_m ≈ m·z^{−(m²−1)}` and each factor `℘ − ℘(u_v) ≈ z⁻²`). -/

/-- `divPt m 0 = 0`. -/
private lemma divPt_zero (m : ℕ) [NeZero m] : L.divPt m (0 : Fin m × Fin m) = 0 := by
  simp [divPt]

/-- If `z − u_v ∈ L` for a division point `u_v`, then `m·z ∈ L`. -/
private lemma mul_mem_lattice_of_sub_divPt_mem {m : ℕ} [NeZero m] {z : ℂ}
    {v : Fin m × Fin m} (h : z - L.divPt m v ∈ L.lattice) : (m : ℂ) * z ∈ L.lattice := by
  have h1 : (m : ℂ) * (z - L.divPt m v) ∈ L.lattice := by
    rw [← nsmul_eq_mul]; exact nsmul_mem h m
  have h2 := add_mem h1 (L.mul_divPt_mem_lattice v)
  rwa [show (m : ℂ) * (z - L.divPt m v) + (m : ℂ) * L.divPt m v = (m : ℂ) * z by ring] at h2

/-- The order of `t ↦ σ(m·t)` at `z` is the order of `σ` at `m·z`. -/
private lemma sigma_mulArg_meromorphicOrderAt (m : ℕ) [NeZero m] (z : ℂ) :
    meromorphicOrderAt (fun t => L.weierstrassSigma ((m : ℂ) * t)) z
      = meromorphicOrderAt L.weierstrassSigma ((m : ℂ) * z) := by
  have hm : (m : ℂ) ≠ 0 := by exact_mod_cast (NeZero.pos m).ne'
  have hd : deriv (fun t : ℂ => (m : ℂ) * t) z = m := by
    simp
  have h := meromorphicOrderAt_comp_of_deriv_ne_zero (f := L.weierstrassSigma)
    (g := fun t => (m : ℂ) * t) (x := z) (by fun_prop) (by rw [hd]; exact hm)
  simpa only [Function.comp_def] using h

/-- The meromorphic order of `F_m` decomposes into σ-orders. -/
private lemma Fm_meromorphicOrderAt (m : ℕ) [NeZero m] (z : ℂ) :
    meromorphicOrderAt (L.Fm m) z
      = meromorphicOrderAt L.weierstrassSigma ((m : ℂ) * z)
        - (m ^ 2 : ℕ) * meromorphicOrderAt L.weierstrassSigma z := by
  have hσa : ∀ x : ℂ, AnalyticAt ℂ L.weierstrassSigma x := fun x =>
    L.differentiable_weierstrassSigma.analyticAt x
  have hm1 : MeromorphicAt (fun t => L.weierstrassSigma ((m : ℂ) * t)) z := by
    have h : AnalyticAt ℂ (fun t : ℂ => L.weierstrassSigma ((m : ℂ) * t)) z := by
      have := hσa ((m : ℂ) * z); fun_prop
    exact h.meromorphicAt
  have hm2 : MeromorphicAt (fun t => L.weierstrassSigma t ^ m ^ 2) z :=
    ((hσa z).fun_pow (m ^ 2)).meromorphicAt
  have hpow : meromorphicOrderAt (fun t => L.weierstrassSigma t ^ m ^ 2) z
      = (m ^ 2 : ℕ) * meromorphicOrderAt L.weierstrassSigma z := by
    rw [show (fun t => L.weierstrassSigma t ^ m ^ 2) = L.weierstrassSigma ^ m ^ 2 from rfl,
      meromorphicOrderAt_pow (hσa z).meromorphicAt]
  rw [show L.Fm m = (fun t => L.weierstrassSigma ((m : ℂ) * t))
      / (fun t => L.weierstrassSigma t ^ m ^ 2) from rfl,
    meromorphicOrderAt_div hm1 hm2, L.sigma_mulArg_meromorphicOrderAt m z, hpow]

/-- `F_m` is elliptic. -/
private lemma Fm_isElliptic (m : ℕ) [NeZero m] : L.IsEllipticWith (L.Fm m) := by
  have hσa : ∀ x : ℂ, AnalyticAt ℂ L.weierstrassSigma x := fun x =>
    L.differentiable_weierstrassSigma.analyticAt x
  constructor
  · intro z
    have h1 : AnalyticAt ℂ (fun t : ℂ => L.weierstrassSigma ((m : ℂ) * t)) z := by
      have := hσa ((m : ℂ) * z); fun_prop
    exact h1.meromorphicAt.div (((hσa z).fun_pow (m ^ 2)).meromorphicAt)
  · intro z l
    exact L.Fm_periodic m l.2 z

/-- **Divisor match** for `propfmprod`: `F_m²` and `∏_{v ≠ 0}(℘ − ℘(u_v))` have the same
meromorphic order at every point. -/
private lemma Fm_sq_meromorphicOrderAt_eq (m : ℕ) [NeZero m] (z : ℂ) :
    meromorphicOrderAt (fun w => L.Fm m w ^ 2) z
      = meromorphicOrderAt (fun w => ∏ v ∈ Finset.univ.erase (0 : Fin m × Fin m),
          (L.weierstrassP w - L.weierstrassP (L.divPt m v))) z := by
  classical
  have hFmM : MeromorphicAt (L.Fm m) z := (L.Fm_isElliptic m).1 z
  have hLHS : meromorphicOrderAt (fun w => L.Fm m w ^ 2) z
      = 2 * meromorphicOrderAt (L.Fm m) z := by
    rw [show (fun w => L.Fm m w ^ 2) = (L.Fm m) ^ 2 from rfl, meromorphicOrderAt_pow hFmM]
    norm_num
  have hfacM : ∀ v : Fin m × Fin m, MeromorphicAt
      (fun w => L.weierstrassP w - L.weierstrassP (L.divPt m v)) z :=
    fun v => (L.isEllipticWith_weierstrassP_sub _).1 z
  have hRHS : meromorphicOrderAt (fun w => ∏ v ∈ Finset.univ.erase (0 : Fin m × Fin m),
        (L.weierstrassP w - L.weierstrassP (L.divPt m v))) z
      = ∑ v ∈ Finset.univ.erase (0 : Fin m × Fin m),
          meromorphicOrderAt (fun w => L.weierstrassP w
            - L.weierstrassP (L.divPt m v)) z :=
    meromorphicOrderAt_fun_prod (fun v _ => hfacM v)
  rw [hLHS, hRHS, L.Fm_meromorphicOrderAt m z, L.sigma_meromorphicOrderAt ((m : ℂ) * z),
    L.sigma_meromorphicOrderAt z]
  by_cases hz : z ∈ L.lattice
  · -- `z ∈ L`: pole of order `2(m²−1)` on both sides
    have hmz : (m : ℂ) * z ∈ L.lattice := by rw [← nsmul_eq_mul]; exact nsmul_mem hz m
    have hterm : ∀ v ∈ Finset.univ.erase (0 : Fin m × Fin m),
        meromorphicOrderAt (fun w => L.weierstrassP w - L.weierstrassP (L.divPt m v)) z
          = ((-2 : ℤ) : WithTop ℤ) :=
      fun v _ => L.meromorphicOrderAt_weierstrassP_sub hz
    rw [if_pos hz, if_pos hmz, Finset.sum_congr rfl hterm, ← WithTop.coe_sum,
      Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      Fintype.card_prod, Fintype.card_fin]
    have h1 : (1 : ℕ) ≤ m * m := Nat.one_le_iff_ne_zero.mpr
      (Nat.mul_ne_zero (NeZero.ne m) (NeZero.ne m))
    have hcast : ((m * m - 1 : ℕ) • (-2 : ℤ) : ℤ) = 2 - 2 * ((m ^ 2 : ℕ) : ℤ) := by
      rw [nsmul_eq_mul, Nat.cast_sub h1]
      push_cast
      ring
    rw [hcast, show ((m ^ 2 : ℕ) : WithTop ℤ) = (((m ^ 2 : ℕ) : ℤ) : WithTop ℤ) from rfl,
      show (1 : WithTop ℤ) = ((1 : ℤ) : WithTop ℤ) from rfl,
      show (2 : WithTop ℤ) = ((2 : ℤ) : WithTop ℤ) from rfl,
      ← WithTop.coe_mul, ← WithTop.LinearOrderedAddCommGroup.coe_sub, ← WithTop.coe_mul,
      WithTop.coe_eq_coe]
    push_cast
    ring
  · rw [if_neg hz]
    by_cases hmz : (m : ℂ) * z ∈ L.lattice
    · -- `z` is a nonzero `m`-torsion point: total order `2` on both sides
      rw [if_pos hmz]
      obtain ⟨v₀, hv₀⟩ := L.exists_add_divPt_mem_lattice hmz
      have hv₀ne : v₀ ≠ 0 := by
        intro h0
        rw [h0, L.divPt_zero m, add_zero] at hv₀
        exact hz hv₀
      have hv₀A : v₀ ∈ Finset.univ.erase (0 : Fin m × Fin m) :=
        Finset.mem_erase.mpr ⟨hv₀ne, Finset.mem_univ _⟩
      by_cases h2z : 2 * z ∈ L.lattice
      · -- `z ≡ −z`: single factor of order `2`
        have hzsub : z - L.divPt m v₀ ∈ L.lattice := by
          have h := sub_mem h2z hv₀
          rwa [show 2 * z - (z + L.divPt m v₀) = z - L.divPt m v₀ by ring] at h
        have hPz : L.weierstrassP z = L.weierstrassP (L.divPt m v₀) :=
          (L.weierstrassP_eq_of_sub_mem hzsub).symm
        have hordv₀ : meromorphicOrderAt (fun w => L.weierstrassP w
            - L.weierstrassP (L.divPt m v₀)) z = 2 :=
          L.wpsub_meromorphicOrderAt_eq_two hz hPz
            ((L.derivWeierstrassP_eq_zero_iff hz).mpr h2z)
        have hothers : ∀ v ∈ Finset.univ.erase (0 : Fin m × Fin m), v ≠ v₀ →
            meromorphicOrderAt (fun w => L.weierstrassP w
              - L.weierstrassP (L.divPt m v)) z = 0 := by
          intro v hvA hvne
          have hvne0 : v ≠ 0 := (Finset.mem_erase.mp hvA).1
          have hsub : z - L.divPt m v ∉ L.lattice := by
            intro h
            have := sub_mem h hzsub
            rw [show z - L.divPt m v - (z - L.divPt m v₀)
              = -(L.divPt m v - L.divPt m v₀) by ring] at this
            exact L.divPt_sub_notMem_lattice hvne (by simpa using neg_mem this)
          have hadd : z + L.divPt m v ∉ L.lattice := by
            intro h
            have := sub_mem h hv₀
            rw [show z + L.divPt m v - (z + L.divPt m v₀)
              = L.divPt m v - L.divPt m v₀ by ring] at this
            exact L.divPt_sub_notMem_lattice hvne this
          exact L.wpsub_meromorphicOrderAt_eq_zero hz
            (L.weierstrassP_ne_of_notMem hz (L.divPt_notMem_lattice hvne0) hsub hadd)
        rw [Finset.sum_eq_single_of_mem v₀ hv₀A hothers, hordv₀]
        norm_num
      · -- `z ≢ −z`: two simple factors, at `v₀` (`z ≡ −u_{v₀}`) and `v₁` (`z ≡ u_{v₁}`)
        have hd : L.derivWeierstrassP z ≠ 0 := fun h0 =>
          h2z ((L.derivWeierstrassP_eq_zero_iff hz).mp h0)
        obtain ⟨v₁, hv₁⟩ := L.exists_add_divPt_mem_lattice
          (show (m : ℂ) * (-z) ∈ L.lattice by
            have := neg_mem hmz; rwa [show -((m : ℂ) * z) = (m : ℂ) * (-z) by ring] at this)
        have hzv₁ : z - L.divPt m v₁ ∈ L.lattice := by
          have := neg_mem hv₁
          rwa [show -(-z + L.divPt m v₁) = z - L.divPt m v₁ by ring] at this
        have hv₁ne : v₁ ≠ 0 := by
          intro h0
          rw [h0, L.divPt_zero m, sub_zero] at hzv₁
          exact hz hzv₁
        have hv₁nev₀ : v₁ ≠ v₀ := by
          intro heq
          apply h2z
          have h := add_mem hv₀ (heq ▸ hzv₁)
          rwa [show z + L.divPt m v₀ + (z - L.divPt m v₀) = 2 * z by ring] at h
        have hv₁A : v₁ ∈ (Finset.univ.erase (0 : Fin m × Fin m)).erase v₀ :=
          Finset.mem_erase.mpr ⟨hv₁nev₀, Finset.mem_erase.mpr ⟨hv₁ne, Finset.mem_univ _⟩⟩
        have hPzv₀ : L.weierstrassP z = L.weierstrassP (L.divPt m v₀) := by
          have hzsub : z - (-(L.divPt m v₀)) ∈ L.lattice := by
            rwa [sub_neg_eq_add]
          rw [← L.weierstrassP_neg (L.divPt m v₀)]
          exact (L.weierstrassP_eq_of_sub_mem hzsub).symm
        have hPzv₁ : L.weierstrassP z = L.weierstrassP (L.divPt m v₁) :=
          (L.weierstrassP_eq_of_sub_mem hzv₁).symm
        have hordv₀ : meromorphicOrderAt (fun w => L.weierstrassP w
            - L.weierstrassP (L.divPt m v₀)) z = 1 :=
          L.wpsub_meromorphicOrderAt_eq_one hz hPzv₀ hd
        have hordv₁ : meromorphicOrderAt (fun w => L.weierstrassP w
            - L.weierstrassP (L.divPt m v₁)) z = 1 :=
          L.wpsub_meromorphicOrderAt_eq_one hz hPzv₁ hd
        have hrest : ∀ v ∈ ((Finset.univ.erase (0 : Fin m × Fin m)).erase v₀).erase v₁,
            meromorphicOrderAt (fun w => L.weierstrassP w
              - L.weierstrassP (L.divPt m v)) z = 0 := by
          intro v hv
          have hvne₁ : v ≠ v₁ := (Finset.mem_erase.mp hv).1
          have hvne₀ : v ≠ v₀ := (Finset.mem_erase.mp (Finset.mem_erase.mp hv).2).1
          have hvne0 : v ≠ 0 :=
            (Finset.mem_erase.mp (Finset.mem_erase.mp (Finset.mem_erase.mp hv).2).2).1
          have hsub : z - L.divPt m v ∉ L.lattice := by
            intro h
            have := sub_mem h hzv₁
            rw [show z - L.divPt m v - (z - L.divPt m v₁)
              = -(L.divPt m v - L.divPt m v₁) by ring] at this
            exact L.divPt_sub_notMem_lattice hvne₁ (by simpa using neg_mem this)
          have hadd : z + L.divPt m v ∉ L.lattice := by
            intro h
            have := sub_mem h hv₀
            rw [show z + L.divPt m v - (z + L.divPt m v₀)
              = L.divPt m v - L.divPt m v₀ by ring] at this
            exact L.divPt_sub_notMem_lattice hvne₀ this
          exact L.wpsub_meromorphicOrderAt_eq_zero hz
            (L.weierstrassP_ne_of_notMem hz (L.divPt_notMem_lattice hvne0) hsub hadd)
        rw [← Finset.add_sum_erase _ _ hv₀A, ← Finset.add_sum_erase _ _ hv₁A,
          Finset.sum_eq_zero hrest, hordv₀, hordv₁]
        norm_num
    · -- `z` is not `m`-torsion: both sides have order `0`
      rw [if_neg hmz]
      have hall : ∀ v ∈ Finset.univ.erase (0 : Fin m × Fin m),
          meromorphicOrderAt (fun w => L.weierstrassP w
            - L.weierstrassP (L.divPt m v)) z = 0 := by
        intro v hvA
        have hvne0 : v ≠ 0 := (Finset.mem_erase.mp hvA).1
        have hsub : z - L.divPt m v ∉ L.lattice := fun h =>
          hmz (L.mul_mem_lattice_of_sub_divPt_mem h)
        have hadd : z + L.divPt m v ∉ L.lattice := fun h =>
          hmz (L.mul_mem_lattice_of_add_divPt_mem h)
        exact L.wpsub_meromorphicOrderAt_eq_zero hz
          (L.weierstrassP_ne_of_notMem hz (L.divPt_notMem_lattice hvne0) hsub hadd)
      rw [Finset.sum_eq_zero hall]
      norm_num

/-- The trailing coefficient of `F_m` at `0` is `m` (from `σ(z) ≈ z`). -/
private lemma trailingCoeff_Fm_zero (m : ℕ) [NeZero m] :
    meromorphicTrailingCoeffAt (L.Fm m) 0 = m := by
  have hσa : ∀ x : ℂ, AnalyticAt ℂ L.weierstrassSigma x := fun x =>
    L.differentiable_weierstrassSigma.analyticAt x
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast (NeZero.pos m).ne'
  set Q : ℂ → ℂ := fun z => ∏' l : {l : L.lattice // l ≠ 0}, weierstrassSigmaTerm z (l.1 : ℂ)
    with hQ
  have hQan : ∀ x : ℂ, AnalyticAt ℂ Q x := fun x => (L.differentiable_sigmaProd).analyticAt x
  have hQ0 : Q 0 = 1 := L.sigmaProd_zero
  -- numerator
  have hgan : AnalyticAt ℂ (fun t : ℂ => (m : ℂ) * Q ((m : ℂ) * t)) 0 := by
    have := hQan ((m : ℂ) * 0); fun_prop
  have hgne : (m : ℂ) * Q ((m : ℂ) * 0) ≠ 0 := by
    rw [mul_zero, hQ0, mul_one]; exact hm0
  have hnum : meromorphicTrailingCoeffAt (fun t => L.weierstrassSigma ((m : ℂ) * t)) 0
      = (m : ℂ) := by
    have hEq : (fun t => L.weierstrassSigma ((m : ℂ) * t)) =ᶠ[𝓝[≠] (0 : ℂ)]
        fun t => (t - 0) ^ (1 : ℤ) • ((m : ℂ) * Q ((m : ℂ) * t)) := by
      filter_upwards with t
      simp only [sub_zero, zpow_one, smul_eq_mul, hQ, weierstrassSigma]
      ring
    rw [hgan.meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE hgne hEq, mul_zero, hQ0,
      mul_one]
  -- denominator
  have hden : meromorphicTrailingCoeffAt (fun t => L.weierstrassSigma t ^ m ^ 2) 0 = 1 := by
    have h := MeromorphicAt.meromorphicTrailingCoeffAt_fun_pow (n := m ^ 2)
      (f := L.weierstrassSigma) (x := 0) ((hσa 0).meromorphicAt)
    rw [h, L.trailingCoeff_sigma_zero, one_pow]
  -- combine
  have hMnum : MeromorphicAt (fun t => L.weierstrassSigma ((m : ℂ) * t)) 0 := by
    have h : AnalyticAt ℂ (fun t : ℂ => L.weierstrassSigma ((m : ℂ) * t)) 0 := by
      have := hσa ((m : ℂ) * 0); fun_prop
    exact h.meromorphicAt
  have hMden : MeromorphicAt (fun t => (L.weierstrassSigma t ^ m ^ 2)⁻¹) 0 :=
    (((hσa 0).fun_pow (m ^ 2)).meromorphicAt).inv
  rw [show L.Fm m = fun t => L.weierstrassSigma ((m : ℂ) * t)
      * (L.weierstrassSigma t ^ m ^ 2)⁻¹ from funext fun t => div_eq_mul_inv _ _,
    MeromorphicAt.meromorphicTrailingCoeffAt_fun_mul hMnum hMden,
    meromorphicTrailingCoeffAt_fun_inv, hnum, hden]
  norm_num

/-- Milla's `propfmprod`: for `z ∉ L`,
`F_m(z)² = m²·∏_{v ≠ 0} (℘(z) − ℘(u_v))`. -/
theorem propfmprod (m : ℕ) [NeZero m] {z : ℂ} (hz : z ∉ L.lattice) :
    L.Fm m z ^ 2 = (m : ℂ) ^ 2
      * ∏ v ∈ Finset.univ.erase (0 : Fin m × Fin m),
          (L.weierstrassP z - L.weierstrassP (L.divPt m v)) := by
  classical
  set F : ℂ → ℂ := fun w => L.Fm m w ^ 2 with hF
  set G : ℂ → ℂ := fun w => ∏ v ∈ Finset.univ.erase (0 : Fin m × Fin m),
      (L.weierstrassP w - L.weierstrassP (L.divPt m v)) with hG
  have hσa : ∀ x : ℂ, AnalyticAt ℂ L.weierstrassSigma x := fun x =>
    L.differentiable_weierstrassSigma.analyticAt x
  have hFmEll := L.Fm_isElliptic m
  have hFell : L.IsEllipticWith F := by
    constructor
    · intro x
      exact ((hFmEll.1 x).pow 2 : MeromorphicAt _ x)
    · intro x l
      change L.Fm m (x + l) ^ 2 = L.Fm m x ^ 2
      rw [L.Fm_periodic m l.2 x]
  have hGell : L.IsEllipticWith G := by
    constructor
    · intro x
      exact MeromorphicAt.fun_prod
        (fun v _ => (L.isEllipticWith_weierstrassP_sub _).1 x)
    · intro x l
      change (∏ v ∈ _, (L.weierstrassP (x + l) - _)) = _
      exact Finset.prod_congr rfl fun v _ => by rw [L.weierstrassP_add_coe x l]
  obtain ⟨c, hc0, hcod⟩ := hFell.exists_const_mul_of_meromorphicOrderAt_eq hGell
    (fun x => L.Fm_sq_meromorphicOrderAt_eq m x)
  -- pin the constant via trailing coefficients at `0`
  have hev0 : ∀ᶠ x in 𝓝[≠] (0 : ℂ), F x = c * G x := by
    have hm := mem_codiscrete.mp hcod 0
    rwa [Filter.disjoint_principal_right, compl_compl] at hm
  have htcF : meromorphicTrailingCoeffAt F 0 = (m : ℂ) ^ 2 := by
    have h := MeromorphicAt.meromorphicTrailingCoeffAt_fun_pow (n := 2)
      (f := L.Fm m) (x := 0) (hFmEll.1 0)
    rw [hF, h, L.trailingCoeff_Fm_zero m]
  have htcG : meromorphicTrailingCoeffAt G 0 = 1 := by
    have h := meromorphicTrailingCoeffAt_fun_prod
      (s := Finset.univ.erase (0 : Fin m × Fin m))
      (f := fun v => fun w => L.weierstrassP w - L.weierstrassP (L.divPt m v))
      (x := (0 : ℂ)) (fun v _ => (L.isEllipticWith_weierstrassP_sub _).1 0)
    rw [hG, h]
    exact Finset.prod_eq_one fun v _ => L.trailingCoeff_wpsub_zero _
  have hceq : c = (m : ℂ) ^ 2 := by
    have hcongr : meromorphicTrailingCoeffAt F 0
        = meromorphicTrailingCoeffAt (fun x => c * G x) 0 :=
      meromorphicTrailingCoeffAt_congr_nhdsNE hev0
    rw [htcF, MeromorphicAt.meromorphicTrailingCoeffAt_fun_mul
      (MeromorphicAt.const c 0) (hGell.1 0), meromorphicTrailingCoeffAt_const, htcG,
      mul_one] at hcongr
    exact hcongr.symm
  -- pointwise upgrade on the connected set `Lᶜ`
  have hFan : AnalyticOnNhd ℂ F (↑L.lattice)ᶜ := by
    intro x hx
    have h1 : AnalyticAt ℂ (fun t : ℂ => L.weierstrassSigma ((m : ℂ) * t)) x := by
      have := hσa ((m : ℂ) * x); fun_prop
    have hFmAn : AnalyticAt ℂ (L.Fm m) x :=
      h1.div ((hσa x).fun_pow (m ^ 2))
        (pow_ne_zero _ (L.weierstrassSigma_ne_zero hx))
    exact hFmAn.fun_pow 2
  have hGan : AnalyticOnNhd ℂ (fun x => c * G x) (↑L.lattice)ᶜ := by
    intro x hx
    have hw : AnalyticAt ℂ L.weierstrassP x := L.analyticOnNhd_weierstrassP x hx
    have hGx : AnalyticAt ℂ G x := by
      rw [hG]
      exact Finset.analyticAt_fun_prod (Finset.univ.erase (0 : Fin m × Fin m))
        (fun v _ => by fun_prop)
    fun_prop
  have hconn : IsPreconnected ((↑L.lattice : Set ℂ)ᶜ) :=
    (L.countable_lattice'.isConnected_compl_of_one_lt_rank (by simp)).isPreconnected
  have hx₀ : L.ω₁ / 2 ∈ ((↑L.lattice : Set ℂ)ᶜ) := L.ω₁_div_two_notMem_lattice
  have hfreq : ∃ᶠ x in 𝓝[≠] (L.ω₁ / 2), F x = c * G x := by
    have hm := mem_codiscrete.mp hcod (L.ω₁ / 2)
    rw [Filter.disjoint_principal_right, compl_compl] at hm
    exact Filter.Eventually.frequently hm
  have hEqOn := hFan.eqOn_of_preconnected_of_frequently_eq hGan hconn hx₀ hfreq
  have hFz : F z = c * G z := hEqOn hz
  rw [hceq] at hFz
  exact hFz

/-- Milla's `lemwpnz`: `℘(nz) = ℘(z) − F_{n−1}(z)·F_{n+1}(z)/F_n(z)²` for `z, nz ∉ L`
(from `lemwpsigma` with `u = z`, `v = nz`, σ-oddness and the definition of `F_k`). -/
theorem lemwpnz (n : ℕ) {z : ℂ} (hz : z ∉ L.lattice) (hnz : (n : ℂ) * z ∉ L.lattice) :
    L.weierstrassP ((n : ℂ) * z)
      = L.weierstrassP z - L.Fm (n - 1) z * L.Fm (n + 1) z / L.Fm n z ^ 2 := by
  have hn1 : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with rfl | h
    · exact absurd (by simp : ((0 : ℕ) : ℂ) * z ∈ L.lattice) hnz
    · exact h
  obtain ⟨p, rfl⟩ : ∃ p, n = p + 1 := ⟨n - 1, by omega⟩
  set s := L.weierstrassSigma z with hs_def
  set a := L.weierstrassSigma ((↑p : ℂ) * z) with ha_def
  set b := L.weierstrassSigma ((↑(p + 1) : ℂ) * z) with hb_def
  set c := L.weierstrassSigma ((↑(p + 2) : ℂ) * z) with hc_def
  have hs : s ≠ 0 := L.weierstrassSigma_ne_zero hz
  have hb : b ≠ 0 := L.weierstrassSigma_ne_zero hnz
  -- `lemwpsigma` with `u = z`, `v = (p+1)z`
  have hkey := L.lemwpsigma hz hnz
  rw [show z + (↑(p + 1) : ℂ) * z = (↑(p + 2) : ℂ) * z by push_cast; ring,
    show z - (↑(p + 1) : ℂ) * z = -((↑p : ℂ) * z) by push_cast; ring,
    L.weierstrassSigma_neg, ← ha_def, ← hb_def, ← hc_def, ← hs_def] at hkey
  -- unfold the `F_k`
  have hFm : L.Fm p z * L.Fm (p + 2) z / L.Fm (p + 1) z ^ 2 = a * c / (s ^ 2 * b ^ 2) := by
    simp only [Fm, ← ha_def, ← hb_def, ← hc_def, ← hs_def]
    have h3 : s ^ ((p + 1) ^ 2) ≠ 0 := pow_ne_zero _ hs
    field_simp
    ring
  rw [show p + 1 - 1 = p from rfl, show p + 1 + 1 = p + 2 from rfl, hFm]
  linear_combination hkey

end PeriodPair

/-! ## The division polynomials `P_m` (paper Def. `defipm`)

Integer polynomials in `x` (outer variable) and `h₂ = ¼g₂, h₃ = ¼g₃` (inner variables
`X 0, X 1` of the coefficient ring `ℤ[h₂, h₃]`), defined by Milla's four-case recursion.
Verified (sympy, numerically to `m = 15`) against the classical elliptic division
polynomials `ψ_m` for `y² = x³ + ax + b` with `a = −h₂`, `b = −h₃`:
`P_m = ψ_m` for odd `m` and `P_m = ψ_m/(2y)` for even `m`. -/

namespace Milla

open Polynomial

/-- The coefficient ring `ℤ[h₂, h₃]`; `h₂ = X 0`, `h₃ = X 1`. -/
abbrev Coeff : Type := MvPolynomial (Fin 2) ℤ

/-- The coefficient `h₂` (standing for `¼g₂(L)`). -/
noncomputable def h2 : Coeff := MvPolynomial.X 0

/-- The coefficient `h₃` (standing for `¼g₃(L)`). -/
noncomputable def h3 : Coeff := MvPolynomial.X 1

/-- `E = 16(x³ − h₂x − h₃)²`, the polynomial with `E(℘) = (℘′)⁴` (paper `dglP`). -/
noncomputable def E : Coeff[X] := 16 * (X ^ 3 - C h2 * X - C h3) ^ 2

/-- Milla's division polynomials `P_m` (paper Def. `defipm`); `P 0 = 0` by convention.
`P₁ = P₂ = 1`, explicit quartic/sextic `P₃, P₄`, and for `m = 4k + r ≥ 5`:
* `P_{4k+1} = E·P_{2k+2}·P_{2k}³ − P_{2k−1}·P_{2k+1}³`
* `P_{4k+2} = P_{2k+1}·(P_{2k+3}·P_{2k}² − P_{2k−1}·P_{2k+2}²)`
* `P_{4k+3} = P_{2k+3}·P_{2k+1}³ − E·P_{2k}·P_{2k+2}³`
* `P_{4k+4} = P_{2k+2}·(P_{2k+4}·P_{2k+1}² − P_{2k}·P_{2k+3}²)` -/
noncomputable def P : ℕ → Coeff[X]
  | 0 => 0
  | 1 => 1
  | 2 => 1
  | 3 => C 3 * X ^ 4 - C (6 * h2) * X ^ 2 - C (12 * h3) * X - C (h2 ^ 2)
  | 4 => C 2 * X ^ 6 - C (10 * h2) * X ^ 4 - C (40 * h3) * X ^ 3 - C (10 * h2 ^ 2) * X ^ 2
      - C (8 * h2 * h3) * X - C (16 * h3 ^ 2 - 2 * h2 ^ 3)
  | n + 5 =>
    let k := (n + 4) / 4
    if n % 4 = 0 then
      E * P (2 * k + 2) * P (2 * k) ^ 3 - P (2 * k - 1) * P (2 * k + 1) ^ 3
    else if n % 4 = 1 then
      P (2 * k + 1) * (P (2 * k + 3) * P (2 * k) ^ 2 - P (2 * k - 1) * P (2 * k + 2) ^ 2)
    else if n % 4 = 2 then
      P (2 * k + 3) * P (2 * k + 1) ^ 3 - E * P (2 * k) * P (2 * k + 2) ^ 3
    else
      P (2 * k + 2) * (P (2 * k + 4) * P (2 * k + 1) ^ 2 - P (2 * k) * P (2 * k + 3) ^ 2)
  termination_by m => m
  decreasing_by all_goals omega

@[simp] lemma P_zero : P 0 = 0 := by simp [P]

@[simp] lemma P_one : P 1 = 1 := by simp [P]

@[simp] lemma P_two : P 2 = 1 := by simp [P]

lemma P_three :
    P 3 = C 3 * X ^ 4 - C (6 * h2) * X ^ 2 - C (12 * h3) * X - C (h2 ^ 2) := by
  simp [P]

lemma P_four :
    P 4 = C 2 * X ^ 6 - C (10 * h2) * X ^ 4 - C (40 * h3) * X ^ 3 - C (10 * h2 ^ 2) * X ^ 2
      - C (8 * h2 * h3) * X - C (16 * h3 ^ 2 - 2 * h2 ^ 3) := by
  simp [P]

/-- Recursion case `m = 4k + 1`, `k ≥ 1` (paper `defipm`). -/
lemma P_four_mul_add_one {k : ℕ} (hk : 1 ≤ k) :
    P (4 * k + 1)
      = E * P (2 * k + 2) * P (2 * k) ^ 3 - P (2 * k - 1) * P (2 * k + 1) ^ 3 := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [show 4 * (j + 1) + 1 = (4 * j) + 5 by ring, P]
  have hmod : 4 * j % 4 = 0 := by omega
  have hdiv : (4 * j + 4) / 4 = j + 1 := by omega
  simp only [hmod, hdiv, if_pos]

/-- Recursion case `m = 4k + 2`, `k ≥ 1` (paper `defipm`). -/
lemma P_four_mul_add_two {k : ℕ} (hk : 1 ≤ k) :
    P (4 * k + 2)
      = P (2 * k + 1) * (P (2 * k + 3) * P (2 * k) ^ 2 - P (2 * k - 1) * P (2 * k + 2) ^ 2) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [show 4 * (j + 1) + 2 = (4 * j + 1) + 5 by ring, P]
  have hmod : (4 * j + 1) % 4 = 1 := by omega
  have hdiv : (4 * j + 1 + 4) / 4 = j + 1 := by omega
  simp only [hmod, hdiv]
  norm_num

/-- Recursion case `m = 4k + 3`, `k ≥ 1` (paper `defipm`). -/
lemma P_four_mul_add_three {k : ℕ} (hk : 1 ≤ k) :
    P (4 * k + 3)
      = P (2 * k + 3) * P (2 * k + 1) ^ 3 - E * P (2 * k) * P (2 * k + 2) ^ 3 := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [show 4 * (j + 1) + 3 = (4 * j + 2) + 5 by ring, P]
  have hmod : (4 * j + 2) % 4 = 2 := by omega
  have hdiv : (4 * j + 2 + 4) / 4 = j + 1 := by omega
  simp only [hmod, hdiv]
  norm_num

/-- Recursion case `m = 4k + 4`, `k ≥ 1` (paper `defipm`). -/
lemma P_four_mul_add_four {k : ℕ} (hk : 1 ≤ k) :
    P (4 * k + 4)
      = P (2 * k + 2) * (P (2 * k + 4) * P (2 * k + 1) ^ 2 - P (2 * k) * P (2 * k + 3) ^ 2) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [show 4 * (j + 1) + 4 = (4 * j + 3) + 5 by ring, P]
  have hmod : (4 * j + 3) % 4 = 3 := by omega
  have hdiv : (4 * j + 3 + 4) / 4 = j + 1 := by omega
  simp only [hmod, hdiv]
  norm_num

/-! ### Degree and leading coefficient of `P_m` (paper Thm. `propindu` (2), (3))

`natDegree (P m) = (m²−1)/2` and `leadingCoeff = m` for odd `m`;
`natDegree (P m) = (m²−4)/2` and `leadingCoeff = m/2` for even `m ≥ 2`
(with the exact sign `+l_m`, refining the paper's `±l_m`). -/

/-- Degree/leading-coefficient bookkeeping for a product. -/
private lemma mul_natDegree_leadingCoeff {p q : Coeff[X]} {dp dq : ℕ} {cp cq : Coeff}
    (hp : p.natDegree = dp) (hq : q.natDegree = dq)
    (hcp : p.leadingCoeff = cp) (hcq : q.leadingCoeff = cq)
    (hcp0 : cp ≠ 0) (hcq0 : cq ≠ 0) :
    (p * q).natDegree = dp + dq ∧ (p * q).leadingCoeff = cp * cq := by
  have hp0 : p ≠ 0 := fun h => hcp0 (by rw [← hcp, h, Polynomial.leadingCoeff_zero])
  have hq0 : q ≠ 0 := fun h => hcq0 (by rw [← hcq, h, Polynomial.leadingCoeff_zero])
  exact ⟨by rw [Polynomial.natDegree_mul hp0 hq0, hp, hq],
    by rw [Polynomial.leadingCoeff_mul, hcp, hcq]⟩

/-- Degree/leading-coefficient bookkeeping for a power. -/
private lemma pow_natDegree_leadingCoeff {p : Coeff[X]} {d : ℕ} {c : Coeff} (n : ℕ)
    (hp : p.natDegree = d) (hc : p.leadingCoeff = c) :
    (p ^ n).natDegree = n * d ∧ (p ^ n).leadingCoeff = c ^ n :=
  ⟨by rw [Polynomial.natDegree_pow, hp], by rw [Polynomial.leadingCoeff_pow, hc]⟩

/-- Degree/leading-coefficient bookkeeping for a difference of same-degree polynomials
whose leading coefficients do not cancel. -/
private lemma sub_natDegree_leadingCoeff {p q : Coeff[X]} {d : ℕ} {cp cq : Coeff}
    (hpd : p.natDegree = d) (hqd : q.natDegree = d)
    (hcp : p.leadingCoeff = cp) (hcq : q.leadingCoeff = cq)
    (hne : cp - cq ≠ 0) :
    (p - q).natDegree = d ∧ (p - q).leadingCoeff = cp - cq := by
  have hpc : p.coeff d = cp := by rw [← hpd, Polynomial.coeff_natDegree, hcp]
  have hqc : q.coeff d = cq := by rw [← hqd, Polynomial.coeff_natDegree, hcq]
  have hcoeff : (p - q).coeff d = cp - cq := by rw [Polynomial.coeff_sub, hpc, hqc]
  have hle : (p - q).natDegree ≤ d := by
    refine le_trans (Polynomial.natDegree_sub_le p q) ?_
    rw [hpd, hqd, max_self]
  have hge : d ≤ (p - q).natDegree :=
    Polynomial.le_natDegree_of_ne_zero (by rw [hcoeff]; exact hne)
  have hdeg : (p - q).natDegree = d := le_antisymm hle hge
  exact ⟨hdeg, by rw [← Polynomial.coeff_natDegree, hdeg, hcoeff]⟩

private lemma E_natDegree : E.natDegree = 6 := by
  rw [E]
  compute_degree!

private lemma E_leadingCoeff : E.leadingCoeff = 16 := by
  have hq : (X ^ 3 - C h2 * X - C h3 : Coeff[X]).Monic := by
    have h : (X ^ 3 - C h2 * X - C h3 : Coeff[X])
        = X ^ (2 + 1) - (C h2 * X + C h3) := by ring
    rw [h]
    refine Polynomial.monic_X_pow_sub ?_
    compute_degree!
  rw [E, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_pow, hq.leadingCoeff, one_pow,
    mul_one]
  rw [show (16 : Coeff[X]) = Polynomial.C (16 : Coeff) from (map_ofNat Polynomial.C 16).symm,
    Polynomial.leadingCoeff_C]

private lemma P_nlc_case_5 (j : ℕ)
    (hodd : ∀ k : ℕ, 2 * k + 1 < 4 * j + 5 → (P (2 * k + 1)).natDegree = 2 * k ^ 2 + 2 * k
      ∧ (P (2 * k + 1)).leadingCoeff = ((2 * k + 1 : ℕ) : Coeff))
    (heven : ∀ k : ℕ, 2 * k + 2 < 4 * j + 5 → (P (2 * k + 2)).natDegree = 2 * k ^ 2 + 4 * k
      ∧ (P (2 * k + 2)).leadingCoeff = ((k + 1 : ℕ) : Coeff)) :
    (∀ j' : ℕ, 4 * j + 5 = 2 * j' + 1 → (P (4 * j + 5)).natDegree = 2 * j' ^ 2 + 2 * j'
      ∧ (P (4 * j + 5)).leadingCoeff = ((2 * j' + 1 : ℕ) : Coeff))
    ∧ (∀ j' : ℕ, 4 * j + 5 = 2 * j' + 2 → (P (4 * j + 5)).natDegree = 2 * j' ^ 2 + 4 * j'
      ∧ (P (4 * j + 5)).leadingCoeff = ((j' + 1 : ℕ) : Coeff)) := by
  have hcast_ne : ∀ n : ℕ, 0 < n → ((n : ℕ) : Coeff) ≠ 0 := fun n hn =>
    Nat.cast_ne_zero.mpr hn.ne'
  have h16 : (16 : Coeff) ≠ 0 := by norm_num
  rw [show 4 * j + 5 = 4 * (j + 1) + 1 by ring,
    P_four_mul_add_one (by omega : 1 ≤ j + 1),
    show P (2 * (j + 1) - 1) = P (2 * j + 1) by
      rw [show 2 * (j + 1) - 1 = 2 * j + 1 by omega],
    show P (2 * (j + 1)) = P (2 * j + 2) by rw [show 2 * (j + 1) = 2 * j + 2 by ring]]
  obtain ⟨hd1, hc1⟩ := heven (j + 1) (by omega)       -- P (2(j+1)+2)
  obtain ⟨hd2, hc2⟩ := heven j (by omega)             -- P (2j+2)
  obtain ⟨hd3, hc3⟩ := hodd j (by omega)              -- P (2j+1)
  obtain ⟨hd4, hc4⟩ := hodd (j + 1) (by omega)        -- P (2(j+1)+1)
  obtain ⟨hdp3, hcp3⟩ := pow_natDegree_leadingCoeff 3 hd2 hc2
  obtain ⟨hdq3, hcq3⟩ := pow_natDegree_leadingCoeff 3 hd4 hc4
  obtain ⟨hdA', hcA'⟩ := mul_natDegree_leadingCoeff E_natDegree hd1 E_leadingCoeff hc1
    h16 (hcast_ne _ (by omega))
  obtain ⟨hdA, hcA⟩ := mul_natDegree_leadingCoeff hdA' hdp3 hcA' hcp3
    (mul_ne_zero h16 (hcast_ne _ (by omega))) (pow_ne_zero _ (hcast_ne _ (by omega)))
  obtain ⟨hdB, hcB⟩ := mul_natDegree_leadingCoeff hd3 hdq3 hc3 hcq3
    (hcast_ne _ (by omega)) (pow_ne_zero _ (hcast_ne _ (by omega)))
  have hdA2 : (E * P (2 * (j + 1) + 2) * P (2 * j + 2) ^ 3).natDegree
      = 8 * j ^ 2 + 20 * j + 12 := by rw [hdA]; ring
  have hdB2 : (P (2 * j + 1) * P (2 * (j + 1) + 1) ^ 3).natDegree
      = 8 * j ^ 2 + 20 * j + 12 := by rw [hdB]; ring
  have hcA2 : (E * P (2 * (j + 1) + 2) * P (2 * j + 2) ^ 3).leadingCoeff
      = ((16 * (j + 2) * (j + 1) ^ 3 : ℕ) : Coeff) := by rw [hcA]; push_cast; ring
  have hcB2 : (P (2 * j + 1) * P (2 * (j + 1) + 1) ^ 3).leadingCoeff
      = (((2 * j + 1) * (2 * j + 3) ^ 3 : ℕ) : Coeff) := by rw [hcB]; push_cast; ring
  have hclead : ((16 * (j + 2) * (j + 1) ^ 3 : ℕ) : Coeff)
      - (((2 * j + 1) * (2 * j + 3) ^ 3 : ℕ) : Coeff) = ((4 * j + 5 : ℕ) : Coeff) := by
    push_cast; ring
  obtain ⟨hdS, hcS⟩ := sub_natDegree_leadingCoeff hdA2 hdB2 hcA2 hcB2
    (by rw [hclead]; exact hcast_ne _ (by omega))
  refine ⟨fun j' hj' => ?_, fun j' hj' => absurd hj' (by omega)⟩
  obtain rfl : j' = 2 * j + 2 := by omega
  refine ⟨by rw [hdS]; ring, ?_⟩
  rw [hcS, hclead]
  exact_mod_cast congrArg (Nat.cast : ℕ → Coeff)
    (by ring : (4 * j + 5 : ℕ) = 2 * (2 * j + 2) + 1)

private lemma P_nlc_case_6 (j : ℕ)
    (hodd : ∀ k : ℕ, 2 * k + 1 < 4 * j + 6 → (P (2 * k + 1)).natDegree = 2 * k ^ 2 + 2 * k
      ∧ (P (2 * k + 1)).leadingCoeff = ((2 * k + 1 : ℕ) : Coeff))
    (heven : ∀ k : ℕ, 2 * k + 2 < 4 * j + 6 → (P (2 * k + 2)).natDegree = 2 * k ^ 2 + 4 * k
      ∧ (P (2 * k + 2)).leadingCoeff = ((k + 1 : ℕ) : Coeff)) :
    (∀ j' : ℕ, 4 * j + 6 = 2 * j' + 1 → (P (4 * j + 6)).natDegree = 2 * j' ^ 2 + 2 * j'
      ∧ (P (4 * j + 6)).leadingCoeff = ((2 * j' + 1 : ℕ) : Coeff))
    ∧ (∀ j' : ℕ, 4 * j + 6 = 2 * j' + 2 → (P (4 * j + 6)).natDegree = 2 * j' ^ 2 + 4 * j'
      ∧ (P (4 * j + 6)).leadingCoeff = ((j' + 1 : ℕ) : Coeff)) := by
  have hcast_ne : ∀ n : ℕ, 0 < n → ((n : ℕ) : Coeff) ≠ 0 := fun n hn =>
    Nat.cast_ne_zero.mpr hn.ne'
  rw [show 4 * j + 6 = 4 * (j + 1) + 2 by ring,
    P_four_mul_add_two (by omega : 1 ≤ j + 1),
    show P (2 * (j + 1) + 3) = P (2 * (j + 2) + 1) by
      rw [show 2 * (j + 1) + 3 = 2 * (j + 2) + 1 by ring],
    show P (2 * (j + 1) - 1) = P (2 * j + 1) by
      rw [show 2 * (j + 1) - 1 = 2 * j + 1 by omega],
    show P (2 * (j + 1)) = P (2 * j + 2) by rw [show 2 * (j + 1) = 2 * j + 2 by ring]]
  obtain ⟨hd0, hc0⟩ := hodd (j + 1) (by omega)        -- P (2(j+1)+1)
  obtain ⟨hd1, hc1⟩ := hodd (j + 2) (by omega)        -- P (2(j+2)+1)
  obtain ⟨hd2, hc2⟩ := heven j (by omega)             -- P (2j+2)
  obtain ⟨hd3, hc3⟩ := hodd j (by omega)              -- P (2j+1)
  obtain ⟨hd4, hc4⟩ := heven (j + 1) (by omega)       -- P (2(j+1)+2)
  obtain ⟨hdp2, hcp2⟩ := pow_natDegree_leadingCoeff 2 hd2 hc2
  obtain ⟨hdq2, hcq2⟩ := pow_natDegree_leadingCoeff 2 hd4 hc4
  obtain ⟨hdA, hcA⟩ := mul_natDegree_leadingCoeff hd1 hdp2 hc1 hcp2
    (hcast_ne _ (by omega)) (pow_ne_zero _ (hcast_ne _ (by omega)))
  obtain ⟨hdB, hcB⟩ := mul_natDegree_leadingCoeff hd3 hdq2 hc3 hcq2
    (hcast_ne _ (by omega)) (pow_ne_zero _ (hcast_ne _ (by omega)))
  have hdA2 : (P (2 * (j + 2) + 1) * P (2 * j + 2) ^ 2).natDegree
      = 6 * j ^ 2 + 18 * j + 12 := by rw [hdA]; ring
  have hdB2 : (P (2 * j + 1) * P (2 * (j + 1) + 2) ^ 2).natDegree
      = 6 * j ^ 2 + 18 * j + 12 := by rw [hdB]; ring
  have hcA2 : (P (2 * (j + 2) + 1) * P (2 * j + 2) ^ 2).leadingCoeff
      = (((2 * j + 5) * (j + 1) ^ 2 : ℕ) : Coeff) := by rw [hcA]; push_cast; ring
  have hcB2 : (P (2 * j + 1) * P (2 * (j + 1) + 2) ^ 2).leadingCoeff
      = (((2 * j + 1) * (j + 2) ^ 2 : ℕ) : Coeff) := by rw [hcB]; push_cast; ring
  have hclead : (((2 * j + 5) * (j + 1) ^ 2 : ℕ) : Coeff)
      - (((2 * j + 1) * (j + 2) ^ 2 : ℕ) : Coeff) = ((1 : ℕ) : Coeff) := by
    push_cast; ring
  obtain ⟨hdS, hcS⟩ := sub_natDegree_leadingCoeff hdA2 hdB2 hcA2 hcB2
    (by rw [hclead]; exact hcast_ne _ (by omega))
  obtain ⟨hdT, hcT⟩ := mul_natDegree_leadingCoeff hd0 hdS hc0 (hcS.trans hclead)
    (hcast_ne _ (by omega))
    (by rw [show ((1 : ℕ) : Coeff) = 1 from Nat.cast_one]; exact one_ne_zero)
  refine ⟨fun j' hj' => absurd hj' (by omega), fun j' hj' => ?_⟩
  obtain rfl : j' = 2 * j + 2 := by omega
  refine ⟨by rw [hdT]; ring, ?_⟩
  rw [hcT]
  push_cast
  ring

private lemma P_nlc_case_7 (j : ℕ)
    (hodd : ∀ k : ℕ, 2 * k + 1 < 4 * j + 7 → (P (2 * k + 1)).natDegree = 2 * k ^ 2 + 2 * k
      ∧ (P (2 * k + 1)).leadingCoeff = ((2 * k + 1 : ℕ) : Coeff))
    (heven : ∀ k : ℕ, 2 * k + 2 < 4 * j + 7 → (P (2 * k + 2)).natDegree = 2 * k ^ 2 + 4 * k
      ∧ (P (2 * k + 2)).leadingCoeff = ((k + 1 : ℕ) : Coeff)) :
    (∀ j' : ℕ, 4 * j + 7 = 2 * j' + 1 → (P (4 * j + 7)).natDegree = 2 * j' ^ 2 + 2 * j'
      ∧ (P (4 * j + 7)).leadingCoeff = ((2 * j' + 1 : ℕ) : Coeff))
    ∧ (∀ j' : ℕ, 4 * j + 7 = 2 * j' + 2 → (P (4 * j + 7)).natDegree = 2 * j' ^ 2 + 4 * j'
      ∧ (P (4 * j + 7)).leadingCoeff = ((j' + 1 : ℕ) : Coeff)) := by
  have hcast_ne : ∀ n : ℕ, 0 < n → ((n : ℕ) : Coeff) ≠ 0 := fun n hn =>
    Nat.cast_ne_zero.mpr hn.ne'
  have h16 : (16 : Coeff) ≠ 0 := by norm_num
  rw [show 4 * j + 7 = 4 * (j + 1) + 3 by ring,
    P_four_mul_add_three (by omega : 1 ≤ j + 1),
    show P (2 * (j + 1) + 3) = P (2 * (j + 2) + 1) by
      rw [show 2 * (j + 1) + 3 = 2 * (j + 2) + 1 by ring],
    show P (2 * (j + 1)) = P (2 * j + 2) by rw [show 2 * (j + 1) = 2 * j + 2 by ring]]
  obtain ⟨hd1, hc1⟩ := hodd (j + 2) (by omega)        -- P (2(j+2)+1)
  obtain ⟨hd2, hc2⟩ := hodd (j + 1) (by omega)        -- P (2(j+1)+1)
  obtain ⟨hd3, hc3⟩ := heven j (by omega)             -- P (2j+2)
  obtain ⟨hd4, hc4⟩ := heven (j + 1) (by omega)       -- P (2(j+1)+2)
  obtain ⟨hdp3, hcp3⟩ := pow_natDegree_leadingCoeff 3 hd2 hc2
  obtain ⟨hdq3, hcq3⟩ := pow_natDegree_leadingCoeff 3 hd4 hc4
  obtain ⟨hdA, hcA⟩ := mul_natDegree_leadingCoeff hd1 hdp3 hc1 hcp3
    (hcast_ne _ (by omega)) (pow_ne_zero _ (hcast_ne _ (by omega)))
  obtain ⟨hdB', hcB'⟩ := mul_natDegree_leadingCoeff E_natDegree hd3 E_leadingCoeff hc3
    h16 (hcast_ne _ (by omega))
  obtain ⟨hdB, hcB⟩ := mul_natDegree_leadingCoeff hdB' hdq3 hcB' hcq3
    (mul_ne_zero h16 (hcast_ne _ (by omega))) (pow_ne_zero _ (hcast_ne _ (by omega)))
  have hdA2 : (P (2 * (j + 2) + 1) * P (2 * (j + 1) + 1) ^ 3).natDegree
      = 8 * j ^ 2 + 28 * j + 24 := by rw [hdA]; ring
  have hdB2 : (E * P (2 * j + 2) * P (2 * (j + 1) + 2) ^ 3).natDegree
      = 8 * j ^ 2 + 28 * j + 24 := by rw [hdB]; ring
  have hcA2 : (P (2 * (j + 2) + 1) * P (2 * (j + 1) + 1) ^ 3).leadingCoeff
      = (((2 * j + 5) * (2 * j + 3) ^ 3 : ℕ) : Coeff) := by rw [hcA]; push_cast; ring
  have hcB2 : (E * P (2 * j + 2) * P (2 * (j + 1) + 2) ^ 3).leadingCoeff
      = ((16 * (j + 1) * (j + 2) ^ 3 : ℕ) : Coeff) := by rw [hcB]; push_cast; ring
  have hclead : (((2 * j + 5) * (2 * j + 3) ^ 3 : ℕ) : Coeff)
      - ((16 * (j + 1) * (j + 2) ^ 3 : ℕ) : Coeff) = ((4 * j + 7 : ℕ) : Coeff) := by
    push_cast; ring
  obtain ⟨hdS, hcS⟩ := sub_natDegree_leadingCoeff hdA2 hdB2 hcA2 hcB2
    (by rw [hclead]; exact hcast_ne _ (by omega))
  refine ⟨fun j' hj' => ?_, fun j' hj' => absurd hj' (by omega)⟩
  obtain rfl : j' = 2 * j + 3 := by omega
  refine ⟨by rw [hdS]; ring, ?_⟩
  rw [hcS, hclead]
  exact_mod_cast congrArg (Nat.cast : ℕ → Coeff)
    (by ring : (4 * j + 7 : ℕ) = 2 * (2 * j + 3) + 1)

private lemma P_nlc_case_8 (j : ℕ)
    (hodd : ∀ k : ℕ, 2 * k + 1 < 4 * j + 8 → (P (2 * k + 1)).natDegree = 2 * k ^ 2 + 2 * k
      ∧ (P (2 * k + 1)).leadingCoeff = ((2 * k + 1 : ℕ) : Coeff))
    (heven : ∀ k : ℕ, 2 * k + 2 < 4 * j + 8 → (P (2 * k + 2)).natDegree = 2 * k ^ 2 + 4 * k
      ∧ (P (2 * k + 2)).leadingCoeff = ((k + 1 : ℕ) : Coeff)) :
    (∀ j' : ℕ, 4 * j + 8 = 2 * j' + 1 → (P (4 * j + 8)).natDegree = 2 * j' ^ 2 + 2 * j'
      ∧ (P (4 * j + 8)).leadingCoeff = ((2 * j' + 1 : ℕ) : Coeff))
    ∧ (∀ j' : ℕ, 4 * j + 8 = 2 * j' + 2 → (P (4 * j + 8)).natDegree = 2 * j' ^ 2 + 4 * j'
      ∧ (P (4 * j + 8)).leadingCoeff = ((j' + 1 : ℕ) : Coeff)) := by
  have hcast_ne : ∀ n : ℕ, 0 < n → ((n : ℕ) : Coeff) ≠ 0 := fun n hn =>
    Nat.cast_ne_zero.mpr hn.ne'
  rw [show 4 * j + 8 = 4 * (j + 1) + 4 by ring,
    P_four_mul_add_four (by omega : 1 ≤ j + 1),
    show P (2 * (j + 1) + 4) = P (2 * (j + 2) + 2) by
      rw [show 2 * (j + 1) + 4 = 2 * (j + 2) + 2 by ring],
    show P (2 * (j + 1) + 3) = P (2 * (j + 2) + 1) by
      rw [show 2 * (j + 1) + 3 = 2 * (j + 2) + 1 by ring],
    show P (2 * (j + 1)) = P (2 * j + 2) by rw [show 2 * (j + 1) = 2 * j + 2 by ring]]
  obtain ⟨hd0, hc0⟩ := heven (j + 1) (by omega)       -- P (2(j+1)+2)
  obtain ⟨hd1, hc1⟩ := heven (j + 2) (by omega)       -- P (2(j+2)+2)
  obtain ⟨hd2, hc2⟩ := hodd (j + 1) (by omega)        -- P (2(j+1)+1)
  obtain ⟨hd3, hc3⟩ := heven j (by omega)             -- P (2j+2)
  obtain ⟨hd4, hc4⟩ := hodd (j + 2) (by omega)        -- P (2(j+2)+1)
  obtain ⟨hdp2, hcp2⟩ := pow_natDegree_leadingCoeff 2 hd2 hc2
  obtain ⟨hdq2, hcq2⟩ := pow_natDegree_leadingCoeff 2 hd4 hc4
  obtain ⟨hdA, hcA⟩ := mul_natDegree_leadingCoeff hd1 hdp2 hc1 hcp2
    (hcast_ne _ (by omega)) (pow_ne_zero _ (hcast_ne _ (by omega)))
  obtain ⟨hdB, hcB⟩ := mul_natDegree_leadingCoeff hd3 hdq2 hc3 hcq2
    (hcast_ne _ (by omega)) (pow_ne_zero _ (hcast_ne _ (by omega)))
  have hdA2 : (P (2 * (j + 2) + 2) * P (2 * (j + 1) + 1) ^ 2).natDegree
      = 6 * j ^ 2 + 24 * j + 24 := by rw [hdA]; ring
  have hdB2 : (P (2 * j + 2) * P (2 * (j + 2) + 1) ^ 2).natDegree
      = 6 * j ^ 2 + 24 * j + 24 := by rw [hdB]; ring
  have hcA2 : (P (2 * (j + 2) + 2) * P (2 * (j + 1) + 1) ^ 2).leadingCoeff
      = (((j + 3) * (2 * j + 3) ^ 2 : ℕ) : Coeff) := by rw [hcA]; push_cast; ring
  have hcB2 : (P (2 * j + 2) * P (2 * (j + 2) + 1) ^ 2).leadingCoeff
      = (((j + 1) * (2 * j + 5) ^ 2 : ℕ) : Coeff) := by rw [hcB]; push_cast; ring
  have hclead : (((j + 3) * (2 * j + 3) ^ 2 : ℕ) : Coeff)
      - (((j + 1) * (2 * j + 5) ^ 2 : ℕ) : Coeff) = ((2 : ℕ) : Coeff) := by
    push_cast; ring
  obtain ⟨hdS, hcS⟩ := sub_natDegree_leadingCoeff hdA2 hdB2 hcA2 hcB2
    (by rw [hclead]; exact hcast_ne _ (by omega))
  obtain ⟨hdT, hcT⟩ := mul_natDegree_leadingCoeff hd0 hdS hc0 (hcS.trans hclead)
    (hcast_ne _ (by omega)) (hcast_ne 2 (by omega))
  refine ⟨fun j' hj' => absurd hj' (by omega), fun j' hj' => ?_⟩
  obtain rfl : j' = 2 * j + 3 := by omega
  refine ⟨by rw [hdT]; ring, ?_⟩
  rw [hcT]
  push_cast
  ring

/-- The combined strong induction for `propindu` (2)+(3): degree and leading
coefficient of `P m`, split by parity (`m = 2j+1` resp. `m = 2j+2`). -/
private theorem P_natDegree_leadingCoeff_aux (m : ℕ) :
    (∀ j : ℕ, m = 2 * j + 1 → (P m).natDegree = 2 * j ^ 2 + 2 * j
      ∧ (P m).leadingCoeff = ((2 * j + 1 : ℕ) : Coeff))
    ∧ (∀ j : ℕ, m = 2 * j + 2 → (P m).natDegree = 2 * j ^ 2 + 4 * j
      ∧ (P m).leadingCoeff = ((j + 1 : ℕ) : Coeff)) := by
  induction m using Nat.strong_induction_on with
  | _ m IH =>
    -- helpers to extract the inductive data in closed form
    have hodd : ∀ j : ℕ, 2 * j + 1 < m → (P (2 * j + 1)).natDegree = 2 * j ^ 2 + 2 * j
        ∧ (P (2 * j + 1)).leadingCoeff = ((2 * j + 1 : ℕ) : Coeff) :=
      fun j hj => (IH _ hj).1 j rfl
    have heven : ∀ j : ℕ, 2 * j + 2 < m → (P (2 * j + 2)).natDegree = 2 * j ^ 2 + 4 * j
        ∧ (P (2 * j + 2)).leadingCoeff = ((j + 1 : ℕ) : Coeff) :=
      fun j hj => (IH _ hj).2 j rfl
    by_cases h5 : m < 5
    · -- base cases m = 0, 1, 2, 3, 4
      constructor
      · intro j hj
        interval_cases m <;> (try omega)
        · -- m = 1, j = 0
          obtain rfl : j = 0 := by omega
          exact ⟨by simp, by simp⟩
        · -- m = 3, j = 1
          obtain rfl : j = 1 := by omega
          have hdeg : (P 3).natDegree = 4 := by
            rw [P_three]; compute_degree!
          refine ⟨by rw [hdeg]; norm_num, ?_⟩
          rw [← Polynomial.coeff_natDegree, hdeg, P_three]
          simp only [Polynomial.coeff_sub, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
            Polynomial.coeff_C, Polynomial.coeff_X]
          norm_num
      · intro j hj
        interval_cases m <;> (try omega)
        · -- m = 2, j = 0
          obtain rfl : j = 0 := by omega
          exact ⟨by simp, by simp⟩
        · -- m = 4, j = 1
          obtain rfl : j = 1 := by omega
          have hdeg : (P 4).natDegree = 6 := by
            rw [P_four]; compute_degree!
          refine ⟨by rw [hdeg]; norm_num, ?_⟩
          rw [← Polynomial.coeff_natDegree, hdeg, P_four]
          simp only [Polynomial.coeff_sub, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
            Polynomial.coeff_C, Polynomial.coeff_X]
          norm_num
    · -- recursive cases: m = 4(j+1) + r
      obtain ⟨j, hm⟩ : ∃ j, m = 4 * j + 5 ∨ m = 4 * j + 6 ∨ m = 4 * j + 7 ∨ m = 4 * j + 8 := by
        refine ⟨(m - 5) / 4, by omega⟩
      rcases hm with hm | hm | hm | hm
      · subst hm; exact P_nlc_case_5 j hodd heven
      · subst hm; exact P_nlc_case_6 j hodd heven
      · subst hm; exact P_nlc_case_7 j hodd heven
      · subst hm; exact P_nlc_case_8 j hodd heven

/-- `propindu` (2)+(3), odd case: `natDegree (P (2j+1)) = ((2j+1)² − 1)/2`. -/
theorem P_odd_natDegree (j : ℕ) : (P (2 * j + 1)).natDegree = 2 * j ^ 2 + 2 * j :=
  ((P_natDegree_leadingCoeff_aux (2 * j + 1)).1 j rfl).1

/-- `propindu` (3), odd case (with the exact sign): `leadingCoeff (P (2j+1)) = 2j+1`. -/
theorem P_odd_leadingCoeff (j : ℕ) :
    (P (2 * j + 1)).leadingCoeff = ((2 * j + 1 : ℕ) : Coeff) :=
  ((P_natDegree_leadingCoeff_aux (2 * j + 1)).1 j rfl).2

/-- `propindu` (2)+(3), even case: `natDegree (P (2j+2)) = ((2j+2)² − 4)/2`. -/
theorem P_even_natDegree (j : ℕ) : (P (2 * j + 2)).natDegree = 2 * j ^ 2 + 4 * j :=
  ((P_natDegree_leadingCoeff_aux (2 * j + 2)).2 j rfl).1

/-- `propindu` (3), even case (with the exact sign): `leadingCoeff (P (2j+2)) = j+1`. -/
theorem P_even_leadingCoeff (j : ℕ) :
    (P (2 * j + 2)).leadingCoeff = ((j + 1 : ℕ) : Coeff) :=
  ((P_natDegree_leadingCoeff_aux (2 * j + 2)).2 j rfl).2

/-- `P m ≠ 0` for `m ≥ 1`. -/
theorem P_ne_zero {m : ℕ} (hm : 1 ≤ m) : P m ≠ 0 := by
  rcases Nat.even_or_odd m with ⟨j, hj⟩ | ⟨j, hj⟩
  · obtain ⟨j', rfl⟩ : ∃ j', m = 2 * j' + 2 := ⟨j - 1, by omega⟩
    intro h
    have := P_even_leadingCoeff j'
    rw [h, Polynomial.leadingCoeff_zero] at this
    exact_mod_cast Nat.cast_ne_zero.mpr (Nat.succ_ne_zero j') this.symm
  · obtain rfl : m = 2 * j + 1 := by omega
    intro h
    have := P_odd_leadingCoeff j
    rw [h, Polynomial.leadingCoeff_zero] at this
    exact_mod_cast Nat.cast_ne_zero.mpr (by omega : 2 * j + 1 ≠ 0) this.symm

end Milla

/-! ## `lemwp2str`: `℘'' = 6℘² − g₂/2` (paper Lemma `lemwp2str`)

Obtained by differentiating the algebraic differential equation `℘′² = 4℘³ − g₂℘ − g₃`
(Mathlib's `derivWeierstrassP_sq`), cancelling `℘′` where it is nonzero, and removing
the 2-torsion zeros of `℘′` by the identity theorem on the connected set `Lᶜ`. -/

namespace PeriodPair

variable (L : PeriodPair)

/-- `℘` has derivative `℘′` at every `z ∉ L` (as a `HasDerivAt`). -/
private lemma hasDerivAt_weierstrassP {z : ℂ} (hz : z ∉ L.lattice) :
    HasDerivAt L.weierstrassP (L.derivWeierstrassP z) z := by
  have h := ((L.analyticOnNhd_weierstrassP z hz).differentiableAt).hasDerivAt
  rwa [congrFun L.deriv_weierstrassP z] at h

/-- `℘′` has derivative `℘'' = deriv ℘′` at every `z ∉ L`. -/
private lemma hasDerivAt_derivWeierstrassP {z : ℂ} (hz : z ∉ L.lattice) :
    HasDerivAt L.derivWeierstrassP (deriv L.derivWeierstrassP z) z :=
  ((L.analyticOnNhd_derivWeierstrassP z hz).differentiableAt).hasDerivAt

/-- The base point `ω₁/3` and its double are not lattice points. -/
private lemma divPt_three_props :
    L.divPt 3 ((1 : Fin 3), (0 : Fin 3)) ∉ L.lattice
      ∧ 2 * L.divPt 3 ((1 : Fin 3), (0 : Fin 3)) ∉ L.lattice := by
  constructor
  · exact L.divPt_notMem_lattice (by decide)
  · have h : 2 * L.divPt 3 ((1 : Fin 3), (0 : Fin 3))
        = L.divPt 3 ((2 : Fin 3), (0 : Fin 3)) := by
      simp only [divPt]
      norm_num
      ring
    rw [h]
    exact L.divPt_notMem_lattice (by decide)

/-- Milla's `lemwp2str`: `℘''(z) = 6℘(z)² − g₂/2` for `z ∉ L`. -/
theorem lemwp2str {z : ℂ} (hz : z ∉ L.lattice) :
    deriv L.derivWeierstrassP z = 6 * L.weierstrassP z ^ 2 - L.g₂ / 2 := by
  have hopen : IsOpen ((↑L.lattice : Set ℂ)ᶜ) := L.isClosed_lattice.isOpen_compl
  -- differentiating the ODE gives `℘′·2℘'' = ℘′·(12℘² − g₂)` on `Lᶜ`
  have key : ∀ w ∉ L.lattice, L.derivWeierstrassP w * (2 * deriv L.derivWeierstrassP w)
      = L.derivWeierstrassP w * (12 * L.weierstrassP w ^ 2 - L.g₂) := by
    intro w hw
    have hP' := L.hasDerivAt_weierstrassP hw
    have hP'' := L.hasDerivAt_derivWeierstrassP hw
    have hL : HasDerivAt (fun t => L.derivWeierstrassP t ^ 2)
        (2 * L.derivWeierstrassP w * deriv L.derivWeierstrassP w) w := by
      simpa using hP''.fun_pow 2
    have h3 : HasDerivAt (fun t => L.weierstrassP t ^ 3)
        (3 * L.weierstrassP w ^ 2 * L.derivWeierstrassP w) w := by
      simpa using hP'.fun_pow 3
    have hR : HasDerivAt
        (fun t => 4 * L.weierstrassP t ^ 3 - L.g₂ * L.weierstrassP t - L.g₃)
        (4 * (3 * L.weierstrassP w ^ 2 * L.derivWeierstrassP w)
          - L.g₂ * L.derivWeierstrassP w) w :=
      ((h3.const_mul 4).sub (hP'.const_mul L.g₂)).sub_const L.g₃
    have hEq : (fun t => L.derivWeierstrassP t ^ 2)
        =ᶠ[𝓝 w] fun t => 4 * L.weierstrassP t ^ 3 - L.g₂ * L.weierstrassP t - L.g₃ := by
      filter_upwards [hopen.mem_nhds hw] with t ht
      exact L.derivWeierstrassP_sq t ht
    have hL' : HasDerivAt (fun t => L.derivWeierstrassP t ^ 2)
        (4 * (3 * L.weierstrassP w ^ 2 * L.derivWeierstrassP w)
          - L.g₂ * L.derivWeierstrassP w) w :=
      hR.congr_of_eventuallyEq hEq
    have huniq := hL.unique hL'
    linear_combination huniq
  -- identity-theorem upgrade from the set `{℘′ ≠ 0}`
  have hAan : AnalyticOnNhd ℂ (deriv L.derivWeierstrassP) (↑L.lattice)ᶜ :=
    fun w hw => (L.analyticOnNhd_derivWeierstrassP w hw).deriv
  have hBan : AnalyticOnNhd ℂ (fun w => 6 * L.weierstrassP w ^ 2 - L.g₂ / 2)
      (↑L.lattice)ᶜ := by
    intro w hw
    have := L.analyticOnNhd_weierstrassP w hw
    fun_prop
  have hconn : IsPreconnected ((↑L.lattice : Set ℂ)ᶜ) :=
    (L.countable_lattice'.isConnected_compl_of_one_lt_rank (by simp)).isPreconnected
  obtain ⟨hz₀, h2z₀⟩ := L.divPt_three_props
  set z₀ : ℂ := L.divPt 3 ((1 : Fin 3), (0 : Fin 3)) with hz₀def
  have hd0 : L.derivWeierstrassP z₀ ≠ 0 := fun h0 =>
    h2z₀ ((L.derivWeierstrassP_eq_zero_iff hz₀).mp h0)
  have hcont : ContinuousAt L.derivWeierstrassP z₀ :=
    ((L.analyticOnNhd_derivWeierstrassP z₀ hz₀).differentiableAt).continuousAt
  have hev : ∀ᶠ w in 𝓝 z₀, deriv L.derivWeierstrassP w
      = 6 * L.weierstrassP w ^ 2 - L.g₂ / 2 := by
    filter_upwards [hcont.eventually_ne hd0, hopen.mem_nhds hz₀] with w hw hwL
    have h2 := mul_left_cancel₀ hw (key w hwL)
    linear_combination h2 / 2
  have hfreq : ∃ᶠ w in 𝓝[≠] z₀, deriv L.derivWeierstrassP w
      = 6 * L.weierstrassP w ^ 2 - L.g₂ / 2 :=
    (hev.filter_mono nhdsWithin_le_nhds).frequently
  exact hAan.eqOn_of_preconnected_of_frequently_eq hBan hconn hz₀ hfreq hz

/-- `℘''' = 12·℘·℘′` for `z ∉ L` (derivative of `lemwp2str`). -/
private lemma wp_third_deriv {z : ℂ} (hz : z ∉ L.lattice) :
    deriv (deriv L.derivWeierstrassP) z
      = 12 * L.weierstrassP z * L.derivWeierstrassP z := by
  have hopen : IsOpen ((↑L.lattice : Set ℂ)ᶜ) := L.isClosed_lattice.isOpen_compl
  have hev : deriv L.derivWeierstrassP
      =ᶠ[𝓝 z] fun w => 6 * L.weierstrassP w ^ 2 - L.g₂ / 2 := by
    filter_upwards [hopen.mem_nhds hz] with w hw
    exact L.lemwp2str hw
  rw [hev.deriv_eq]
  have hP' := L.hasDerivAt_weierstrassP hz
  have h2 : HasDerivAt (fun w => 6 * L.weierstrassP w ^ 2 - L.g₂ / 2)
      (6 * (2 * L.weierstrassP z * L.derivWeierstrassP z)) z := by
    have h := ((hP'.fun_pow 2).const_mul (6 : ℂ)).sub_const (L.g₂ / 2)
    simpa using h
  rw [h2.deriv]
  ring

/-! ## `F₂ = −℘′` (paper `propfmpm`, case `m = 2`)

Writing `σ(z−v) = (z−v)·Q(z−v)` with the entire σ-product `Q` (`Q(0) = 1`), the formula
`lemwpsigma` becomes `℘(v) − ℘(z) = (z−v)·H(v)` for `v` near `z`; differentiating at
`v = z` gives `℘′(z) = −H(z) = −σ(2z)/σ(z)⁴ = −F₂(z)` — no Laurent series needed. -/

/-- The σ-product `Q` is an even function. -/
private lemma sigmaProd_even (z : ℂ) :
    (∏' l : {l : L.lattice // l ≠ 0}, weierstrassSigmaTerm (-z) (l.1 : ℂ))
      = ∏' l : {l : L.lattice // l ≠ 0}, weierstrassSigmaTerm z (l.1 : ℂ) := by
  rcases eq_or_ne z 0 with rfl | hz
  · rw [neg_zero]
  · have h := L.weierstrassSigma_neg z
    have hL : L.weierstrassSigma (-z)
        = (-z) * ∏' l : {l : L.lattice // l ≠ 0}, weierstrassSigmaTerm (-z) (l.1 : ℂ) := rfl
    have hR : L.weierstrassSigma z
        = z * ∏' l : {l : L.lattice // l ≠ 0}, weierstrassSigmaTerm z (l.1 : ℂ) := rfl
    rw [hL, hR] at h
    have h2 : (-z) * (∏' l : {l : L.lattice // l ≠ 0}, weierstrassSigmaTerm (-z) (l.1 : ℂ))
        = (-z) * ∏' l : {l : L.lattice // l ≠ 0}, weierstrassSigmaTerm z (l.1 : ℂ) := by
      linear_combination h
    exact mul_left_cancel₀ (neg_ne_zero.mpr hz) h2

/-- `Q′(0) = 0` (`Q` is even and differentiable). -/
private lemma deriv_sigmaProd_zero :
    deriv (fun z => ∏' l : {l : L.lattice // l ≠ 0}, weierstrassSigmaTerm z (l.1 : ℂ)) 0
      = 0 := by
  set Q : ℂ → ℂ := fun z => ∏' l : {l : L.lattice // l ≠ 0}, weierstrassSigmaTerm z (l.1 : ℂ)
    with hQ
  have heq : (fun z => Q (-z)) = Q := funext fun z => L.sigmaProd_even z
  have h1 : deriv (fun z => Q (-z)) 0 = -deriv Q (-0) := deriv_comp_neg Q 0
  rw [heq, neg_zero] at h1
  linear_combination h1 / 2

/-- `σ′ = ζ·σ` off the lattice, as a `HasDerivAt`. -/
private lemma hasDerivAt_sigma {w : ℂ} (hw : w ∉ L.lattice) :
    HasDerivAt L.weierstrassSigma (L.weierstrassZeta w * L.weierstrassSigma w) w := by
  have hd := (L.differentiable_weierstrassSigma w).hasDerivAt
  have hlog := L.logDeriv_weierstrassSigma w hw
  rw [logDeriv_apply, div_eq_iff (L.weierstrassSigma_ne_zero hw)] at hlog
  rwa [hlog] at hd

/-- `F₂ = −℘′` for all `z ∉ L` (paper `propfmpm`, `m = 2`). -/
theorem Fm_two {z : ℂ} (hz : z ∉ L.lattice) :
    L.Fm 2 z = -L.derivWeierstrassP z := by
  set Q : ℂ → ℂ := fun w => ∏' l : {l : L.lattice // l ≠ 0}, weierstrassSigmaTerm w (l.1 : ℂ)
    with hQdef
  have hQdiff : Differentiable ℂ Q := L.differentiable_sigmaProd
  have hσz : L.weierstrassSigma z ≠ 0 := L.weierstrassSigma_ne_zero hz
  set H : ℂ → ℂ := fun v => L.weierstrassSigma (z + v) * Q (z - v)
      / (L.weierstrassSigma z ^ 2 * L.weierstrassSigma v ^ 2) with hHdef
  have hAeq : ∀ v, v ∉ L.lattice →
      L.weierstrassP v - L.weierstrassP z = (z - v) * H v := by
    intro v hv
    have h := L.lemwpsigma hz hv
    have hfact : L.weierstrassSigma (z - v) = (z - v) * Q (z - v) := rfl
    rw [h, hfact]
    simp only [hHdef]
    ring
  have hσdiff : Differentiable ℂ L.weierstrassSigma := L.differentiable_weierstrassSigma
  have hHdiff : DifferentiableAt ℂ H z := by
    have h1 : DifferentiableAt ℂ (fun v : ℂ => L.weierstrassSigma (z + v)) z := by fun_prop
    have h2 : DifferentiableAt ℂ (fun v : ℂ => Q (z - v)) z := by fun_prop
    have h3 : DifferentiableAt ℂ
        (fun v : ℂ => L.weierstrassSigma z ^ 2 * L.weierstrassSigma v ^ 2) z := by fun_prop
    exact (h1.mul h2).div h3
      (mul_ne_zero (pow_ne_zero 2 hσz) (pow_ne_zero 2 hσz))
  have hψ : HasDerivAt (fun v => (z - v) * H v) (-H z) z := by
    have h1 : HasDerivAt (fun v : ℂ => z - v) (-1) z := by
      simpa using (hasDerivAt_id z).const_sub z
    have h := h1.fun_mul hHdiff.hasDerivAt
    simpa using h
  have hA : HasDerivAt (fun v => L.weierstrassP v - L.weierstrassP z)
      (L.derivWeierstrassP z) z := (L.hasDerivAt_weierstrassP hz).sub_const _
  have hev : (fun v => L.weierstrassP v - L.weierstrassP z) =ᶠ[𝓝 z]
      fun v => (z - v) * H v := by
    filter_upwards [L.isClosed_lattice.isOpen_compl.mem_nhds hz] with v hv
    exact hAeq v hv
  have hA2 : HasDerivAt (fun v => L.weierstrassP v - L.weierstrassP z) (-H z) z :=
    hψ.congr_of_eventuallyEq hev
  have hval := hA.unique hA2
  have hHz : H z = L.Fm 2 z := by
    have hQ0 : Q (z - z) = 1 := by rw [sub_self]; exact L.sigmaProd_zero
    simp only [hHdef]
    rw [hQ0, mul_one, ← two_mul]
    simp only [Fm]
    norm_num
    ring_nf
  rw [← hHz]
  linear_combination hval

/-! ## Duplication (paper `lemwp2str`, second half)

The derivative of `F₂ = σ(2z)/σ(z)⁴ = −℘′` gives `℘'' = 2(ζ(2z) − 2ζ(z))·℘′`;
differentiating once more (with `ζ′ = −℘` and `℘''' = 12℘℘′`) eliminates `ζ` and
yields the duplication formula, and one further derivative yields `℘′(2z)` and `F₄`. -/

/-- `ζ′ = −℘` as a `HasDerivAt`. -/
private lemma hasDerivAt_zeta {w : ℂ} (hw : w ∉ L.lattice) :
    HasDerivAt L.weierstrassZeta (-L.weierstrassP w) w := by
  have hd := (L.differentiableOn_weierstrassZeta.differentiableAt
    (L.isClosed_lattice.isOpen_compl.mem_nhds hw)).hasDerivAt
  rwa [L.deriv_weierstrassZeta w hw] at hd

/-- `℘'' = 2(ζ(2z) − 2ζ(z))·℘′(z)` for `z, 2z ∉ L`. -/
private theorem wp2_eq_zeta {z : ℂ} (hz : z ∉ L.lattice) (h2z : 2 * z ∉ L.lattice) :
    deriv L.derivWeierstrassP z
      = 2 * (L.weierstrassZeta (2 * z) - 2 * L.weierstrassZeta z)
        * L.derivWeierstrassP z := by
  have hσz : L.weierstrassSigma z ≠ 0 := L.weierstrassSigma_ne_zero hz
  have hev : (fun w => L.weierstrassSigma (2 * w) / L.weierstrassSigma w ^ 4)
      =ᶠ[𝓝 z] fun w => -L.derivWeierstrassP w := by
    filter_upwards [L.isClosed_lattice.isOpen_compl.mem_nhds hz] with w hw
    have h := L.Fm_two hw
    simp only [Fm] at h
    rw [show ((2 : ℕ) : ℂ) = (2 : ℂ) by norm_num, show (2 : ℕ) ^ 2 = 4 from rfl] at h
    exact h
  have hlin : HasDerivAt (fun w : ℂ => 2 * w) 2 z := by
    simpa using (hasDerivAt_id z).const_mul (2 : ℂ)
  have hnum : HasDerivAt (fun w => L.weierstrassSigma (2 * w))
      (L.weierstrassZeta (2 * z) * L.weierstrassSigma (2 * z) * 2) z := by
    have h := (L.hasDerivAt_sigma h2z).comp z hlin
    simpa [Function.comp_def] using h
  have hden : HasDerivAt (fun w => L.weierstrassSigma w ^ 4)
      (4 * L.weierstrassSigma z ^ 3
        * (L.weierstrassZeta z * L.weierstrassSigma z)) z := by
    simpa using (L.hasDerivAt_sigma hz).fun_pow 4
  have hdiv := hnum.fun_div hden (pow_ne_zero 4 hσz)
  have hneg : HasDerivAt (fun w => -L.derivWeierstrassP w)
      (-deriv L.derivWeierstrassP z) z := (L.hasDerivAt_derivWeierstrassP hz).fun_neg
  have hEq := hev.deriv_eq
  rw [hdiv.deriv, hneg.deriv] at hEq
  rw [div_eq_iff (pow_ne_zero 2 (pow_ne_zero 4 hσz))] at hEq
  -- substitute `σ(2z) = −℘′·σ(z)⁴` (that is, `F₂ = −℘′`)
  have hF2 := L.Fm_two hz
  simp only [Fm] at hF2
  rw [show ((2 : ℕ) : ℂ) = (2 : ℂ) by norm_num, show (2 : ℕ) ^ 2 = 4 from rfl,
    div_eq_iff (pow_ne_zero 4 hσz)] at hF2
  rw [hF2] at hEq
  have hgoal : (L.weierstrassSigma z ^ 4) ^ 2 * deriv L.derivWeierstrassP z
      = (L.weierstrassSigma z ^ 4) ^ 2
        * (2 * (L.weierstrassZeta (2 * z) - 2 * L.weierstrassZeta z)
          * L.derivWeierstrassP z) := by
    linear_combination hEq
  exact mul_left_cancel₀ (pow_ne_zero 2 (pow_ne_zero 4 hσz)) hgoal

/-- The set `U₂ = {w | w ∉ L, 2w ∉ L}` is open. -/
private lemma isOpen_U2 : IsOpen {w : ℂ | w ∉ L.lattice ∧ 2 * w ∉ L.lattice} := by
  have h1 : IsOpen ((↑L.lattice : Set ℂ)ᶜ) := L.isClosed_lattice.isOpen_compl
  have h2 : IsOpen ((fun w : ℂ => 2 * w) ⁻¹' (↑L.lattice : Set ℂ)ᶜ) :=
    h1.preimage (by fun_prop)
  exact h1.inter h2

/-- Duplication formula: `4℘(2z)℘′(z)² = ℘''(z)² − 8℘(z)℘′(z)²` for `z, 2z ∉ L`
(paper `lemwp2str`). -/
private theorem wp_dup {z : ℂ} (hz : z ∉ L.lattice) (h2z : 2 * z ∉ L.lattice) :
    4 * L.weierstrassP (2 * z) * L.derivWeierstrassP z ^ 2
      = (deriv L.derivWeierstrassP z) ^ 2
        - 8 * L.weierstrassP z * L.derivWeierstrassP z ^ 2 := by
  have hmem : {w : ℂ | w ∉ L.lattice ∧ 2 * w ∉ L.lattice} ∈ 𝓝 z :=
    L.isOpen_U2.mem_nhds ⟨hz, h2z⟩
  have hev : deriv L.derivWeierstrassP =ᶠ[𝓝 z]
      fun w => 2 * (L.weierstrassZeta (2 * w) - 2 * L.weierstrassZeta w)
        * L.derivWeierstrassP w := by
    filter_upwards [hmem] with w hw
    exact L.wp2_eq_zeta hw.1 hw.2
  have hEq := hev.deriv_eq
  rw [L.wp_third_deriv hz] at hEq
  have hlin : HasDerivAt (fun w : ℂ => 2 * w) 2 z := by
    simpa using (hasDerivAt_id z).const_mul (2 : ℂ)
  have hζ2 : HasDerivAt (fun w => L.weierstrassZeta (2 * w))
      (-L.weierstrassP (2 * z) * 2) z := by
    have h := (L.hasDerivAt_zeta h2z).comp z hlin
    simpa [Function.comp_def] using h
  have hG : HasDerivAt
      (fun w => 2 * (L.weierstrassZeta (2 * w) - 2 * L.weierstrassZeta w))
      (2 * (-L.weierstrassP (2 * z) * 2 - 2 * -L.weierstrassP z)) z :=
    (hζ2.sub ((L.hasDerivAt_zeta hz).const_mul 2)).const_mul 2
  have hP'' := L.hasDerivAt_derivWeierstrassP hz
  have hprod := hG.fun_mul hP''
  rw [hprod.deriv] at hEq
  have hzeta := L.wp2_eq_zeta hz h2z
  linear_combination (L.derivWeierstrassP z) * hEq
    - (deriv L.derivWeierstrassP z) * hzeta

/-- `℘′(2z)·℘′(z)² = ℘℘′℘'' − ℘′³ − ℘(2z)℘′℘''` for `z, 2z ∉ L` (derivative of the
duplication formula). -/
private theorem wpp_dup {z : ℂ} (hz : z ∉ L.lattice) (h2z : 2 * z ∉ L.lattice) :
    L.derivWeierstrassP (2 * z) * L.derivWeierstrassP z ^ 2
      = L.weierstrassP z * L.derivWeierstrassP z * deriv L.derivWeierstrassP z
        - L.derivWeierstrassP z ^ 3
        - L.weierstrassP (2 * z) * L.derivWeierstrassP z
          * deriv L.derivWeierstrassP z := by
  have hmem : {w : ℂ | w ∉ L.lattice ∧ 2 * w ∉ L.lattice} ∈ 𝓝 z :=
    L.isOpen_U2.mem_nhds ⟨hz, h2z⟩
  have hev : (fun w => 4 * L.weierstrassP (2 * w) * L.derivWeierstrassP w ^ 2)
      =ᶠ[𝓝 z] fun w => (deriv L.derivWeierstrassP w) ^ 2
        - 8 * L.weierstrassP w * L.derivWeierstrassP w ^ 2 := by
    filter_upwards [hmem] with w hw
    exact L.wp_dup hw.1 hw.2
  have hEq := hev.deriv_eq
  have hlin : HasDerivAt (fun w : ℂ => 2 * w) 2 z := by
    simpa using (hasDerivAt_id z).const_mul (2 : ℂ)
  have hP2 : HasDerivAt (fun w => L.weierstrassP (2 * w))
      (L.derivWeierstrassP (2 * z) * 2) z := by
    have h := (L.hasDerivAt_weierstrassP h2z).comp z hlin
    simpa [Function.comp_def] using h
  have hP' := L.hasDerivAt_weierstrassP hz
  have hP'' := L.hasDerivAt_derivWeierstrassP hz
  have hP'sq : HasDerivAt (fun w => L.derivWeierstrassP w ^ 2)
      (2 * L.derivWeierstrassP z * deriv L.derivWeierstrassP z) z := by
    simpa using hP''.fun_pow 2
  have hL : HasDerivAt
      (fun w => 4 * L.weierstrassP (2 * w) * L.derivWeierstrassP w ^ 2)
      (4 * (L.derivWeierstrassP (2 * z) * 2) * L.derivWeierstrassP z ^ 2
        + 4 * L.weierstrassP (2 * z)
          * (2 * L.derivWeierstrassP z * deriv L.derivWeierstrassP z)) z :=
    (hP2.const_mul 4).fun_mul hP'sq
  have hdd : HasDerivAt (deriv L.derivWeierstrassP)
      (deriv (deriv L.derivWeierstrassP) z) z :=
    (((L.analyticOnNhd_derivWeierstrassP z hz).deriv).differentiableAt).hasDerivAt
  have hdd2 : HasDerivAt (fun w => (deriv L.derivWeierstrassP w) ^ 2)
      (2 * deriv L.derivWeierstrassP z * deriv (deriv L.derivWeierstrassP) z) z := by
    simpa using hdd.fun_pow 2
  have hR : HasDerivAt
      (fun w => (deriv L.derivWeierstrassP w) ^ 2
        - 8 * L.weierstrassP w * L.derivWeierstrassP w ^ 2)
      (2 * deriv L.derivWeierstrassP z * deriv (deriv L.derivWeierstrassP) z
        - (8 * L.derivWeierstrassP z * L.derivWeierstrassP z ^ 2
          + 8 * L.weierstrassP z
            * (2 * L.derivWeierstrassP z * deriv L.derivWeierstrassP z))) z :=
    hdd2.sub ((hP'.const_mul 8).fun_mul hP'sq)
  rw [hL.deriv, hR.deriv, L.wp_third_deriv hz] at hEq
  linear_combination hEq / 8

/-- `F₄ = −℘′·(3℘℘′²℘'' − ℘′⁴ − ¼℘''³)` for `z, 2z ∉ L`. -/
private theorem Fm_four {z : ℂ} (hz : z ∉ L.lattice) (h2z : 2 * z ∉ L.lattice) :
    L.Fm 4 z = -L.derivWeierstrassP z
      * (3 * L.weierstrassP z * L.derivWeierstrassP z ^ 2 * deriv L.derivWeierstrassP z
        - L.derivWeierstrassP z ^ 4 - (deriv L.derivWeierstrassP z) ^ 3 / 4) := by
  have hσz := L.weierstrassSigma_ne_zero hz
  have hσ2z := L.weierstrassSigma_ne_zero h2z
  have hdecomp : L.Fm 4 z = L.Fm 2 (2 * z) * L.Fm 2 z ^ 4 := by
    have hc1 : ((2 : ℕ) : ℂ) * (2 * z) = ((4 : ℕ) : ℂ) * z := by push_cast; ring
    have hc2 : ((2 : ℕ) : ℂ) * z = 2 * z := by push_cast; ring
    simp only [Fm, hc1, hc2]
    rw [show (2 : ℕ) ^ 2 = 4 from rfl, show (4 : ℕ) ^ 2 = 16 from rfl]
    field_simp [hσ2z]
    have hσ2z'' : L.weierstrassSigma (z * 2) ≠ 0 := by rwa [mul_comm] at hσ2z
    rw [mul_div_cancel_right₀ _ hσ2z'']
  rw [hdecomp, L.Fm_two h2z, L.Fm_two hz]
  have h1 := L.wpp_dup hz h2z
  have h2 := L.wp_dup hz h2z
  linear_combination (-(L.derivWeierstrassP z ^ 2)) * h1
    + (L.derivWeierstrassP z * deriv L.derivWeierstrassP z / 4) * h2

/-! ## The recursions `lemfrekur` (paper Lemma `lemfrekur`)

Both recursions follow from the **master identity**
`F_{2a+d}·F_d = F_{a+d}²·F_a²·(℘(az) − ℘((a+d)z))` — which is `lemwpsigma` at
`u = (a+d)z`, `v = az` plus σ-exponent bookkeeping — combined with `lemwpnz`.
This replaces the paper's three-term σ-identity `lemsigmasigma`. -/

/-- `F₀ = 0`. -/
private lemma Fm_zero (z : ℂ) : L.Fm 0 z = 0 := by
  have h0 : L.weierstrassSigma 0 = 0 :=
    (L.weierstrassSigma_eq_zero_iff 0).mpr L.lattice.zero_mem
  simp [Fm, h0]

/-- `F₁ = 1` off the lattice. -/
private lemma Fm_one {z : ℂ} (hz : z ∉ L.lattice) : L.Fm 1 z = 1 := by
  have hσ := L.weierstrassSigma_ne_zero hz
  simp [Fm, div_self hσ]

/-- `F_k(z) ≠ 0` when `z, kz ∉ L`. -/
private lemma Fm_ne_zero {k : ℕ} {z : ℂ} (hz : z ∉ L.lattice)
    (hk : (k : ℂ) * z ∉ L.lattice) : L.Fm k z ≠ 0 := by
  simp only [Fm]
  exact div_ne_zero (L.weierstrassSigma_ne_zero hk)
    (pow_ne_zero _ (L.weierstrassSigma_ne_zero hz))

/-- `σ(kz) = F_k(z)·σ(z)^{k²}`. -/
private lemma sigma_natMul_eq (k : ℕ) {z : ℂ} (hz : z ∉ L.lattice) :
    L.weierstrassSigma ((k : ℂ) * z) = L.Fm k z * L.weierstrassSigma z ^ (k ^ 2) := by
  simp only [Fm]
  rw [div_mul_cancel₀]
  exact pow_ne_zero _ (L.weierstrassSigma_ne_zero hz)

/-- **Master identity**: `F_{2a+d}·F_d = F_{a+d}²·F_a²·(℘(az) − ℘((a+d)z))` for
`z, az, (a+d)z ∉ L` (from `lemwpsigma` with `u = (a+d)z`, `v = az`). -/
private theorem Fm_master (a d : ℕ) {z : ℂ} (hz : z ∉ L.lattice)
    (ha : ((a : ℕ) : ℂ) * z ∉ L.lattice) (had : ((a + d : ℕ) : ℂ) * z ∉ L.lattice) :
    L.Fm (2 * a + d) z * L.Fm d z
      = L.Fm (a + d) z ^ 2 * L.Fm a z ^ 2
        * (L.weierstrassP ((a : ℂ) * z) - L.weierstrassP (((a + d : ℕ) : ℂ) * z)) := by
  have hs := L.weierstrassSigma_ne_zero hz
  have hFa := L.Fm_ne_zero hz ha
  have hFad := L.Fm_ne_zero hz had
  have hkey := L.lemwpsigma had ha
  rw [show ((a + d : ℕ) : ℂ) * z + (a : ℂ) * z = ((2 * a + d : ℕ) : ℂ) * z by
      push_cast; ring,
    show ((a + d : ℕ) : ℂ) * z - (a : ℂ) * z = ((d : ℕ) : ℂ) * z by push_cast; ring,
    L.sigma_natMul_eq (2 * a + d) hz, L.sigma_natMul_eq d hz,
    L.sigma_natMul_eq (a + d) hz, L.sigma_natMul_eq a hz] at hkey
  rw [hkey]
  have hpow : (L.weierstrassSigma z ^ (a + d) ^ 2) ^ 2 * (L.weierstrassSigma z ^ a ^ 2) ^ 2
      = L.weierstrassSigma z ^ (2 * a + d) ^ 2 * L.weierstrassSigma z ^ d ^ 2 := by
    rw [← pow_mul, ← pow_mul, ← pow_add, ← pow_add]
    congr 1
    ring
  field_simp
  linear_combination (L.Fm (2 * a + d) z * L.Fm d z) * hpow

/-- Paper `lemfrekur`, first recursion:
`F_{2j+3} = F_{j+3}·F_{j+1}³ − F_j·F_{j+2}³` at generic `z`. -/
theorem lemfrekur_odd (j : ℕ) {z : ℂ}
    (hz : ∀ k : ℕ, k ≠ 0 → (k : ℂ) * z ∉ L.lattice) :
    L.Fm (2 * j + 3) z
      = L.Fm (j + 3) z * L.Fm (j + 1) z ^ 3 - L.Fm j z * L.Fm (j + 2) z ^ 3 := by
  have hz1 : z ∉ L.lattice := by
    have := hz 1 one_ne_zero
    rwa [Nat.cast_one, one_mul] at this
  have hj1 : ((j + 1 : ℕ) : ℂ) * z ∉ L.lattice := hz (j + 1) (by omega)
  have hj2 : ((j + 2 : ℕ) : ℂ) * z ∉ L.lattice := hz (j + 2) (by omega)
  have hM := L.Fm_master (j + 1) 1 hz1 hj1
    (by rwa [show j + 1 + 1 = j + 2 from rfl])
  simp only [show 2 * (j + 1) + 1 = 2 * j + 3 from by ring,
    show j + 1 + 1 = j + 2 from rfl] at hM
  rw [L.Fm_one hz1, mul_one] at hM
  have hn1 := L.lemwpnz (j + 1) hz1 hj1
  have hn2 := L.lemwpnz (j + 2) hz1 hj2
  simp only [Nat.add_sub_cancel, show j + 2 - 1 = j + 1 from rfl,
    show j + 1 + 1 = j + 2 from rfl, show j + 2 + 1 = j + 3 from rfl] at hn1 hn2
  have hne1 : L.Fm (j + 1) z ≠ 0 := L.Fm_ne_zero hz1 hj1
  have hne2 : L.Fm (j + 2) z ≠ 0 := L.Fm_ne_zero hz1 hj2
  rw [hM, hn1, hn2]
  field_simp
  ring

/-- Paper `lemfrekur`, second recursion:
`F_{2j+4}·F₂ = F_{j+2}·(F_{j+4}·F_{j+1}² − F_j·F_{j+3}²)` at generic `z`. -/
theorem lemfrekur_even (j : ℕ) {z : ℂ}
    (hz : ∀ k : ℕ, k ≠ 0 → (k : ℂ) * z ∉ L.lattice) :
    L.Fm (2 * j + 4) z * L.Fm 2 z
      = L.Fm (j + 2) z
        * (L.Fm (j + 4) z * L.Fm (j + 1) z ^ 2 - L.Fm j z * L.Fm (j + 3) z ^ 2) := by
  have hz1 : z ∉ L.lattice := by
    have := hz 1 one_ne_zero
    rwa [Nat.cast_one, one_mul] at this
  have hj1 : ((j + 1 : ℕ) : ℂ) * z ∉ L.lattice := hz (j + 1) (by omega)
  have hj3 : ((j + 3 : ℕ) : ℂ) * z ∉ L.lattice := hz (j + 3) (by omega)
  have hM := L.Fm_master (j + 1) 2 hz1 hj1
    (by rwa [show j + 1 + 2 = j + 3 from rfl])
  simp only [show 2 * (j + 1) + 2 = 2 * j + 4 from by ring,
    show j + 1 + 2 = j + 3 from rfl] at hM
  have hn1 := L.lemwpnz (j + 1) hz1 hj1
  have hn3 := L.lemwpnz (j + 3) hz1 hj3
  simp only [Nat.add_sub_cancel, show j + 3 - 1 = j + 2 from rfl,
    show j + 1 + 1 = j + 2 from rfl, show j + 3 + 1 = j + 4 from rfl] at hn1 hn3
  have hne1 : L.Fm (j + 1) z ≠ 0 := L.Fm_ne_zero hz1 hj1
  have hne3 : L.Fm (j + 3) z ≠ 0 := L.Fm_ne_zero hz1 hj3
  rw [hM, hn1, hn3]
  field_simp
  ring

/-- `F₃ = 3℘℘′² − ¼℘''²` for `z, 2z ∉ L`. -/
private theorem Fm_three {z : ℂ} (hz : z ∉ L.lattice) (h2z : 2 * z ∉ L.lattice) :
    L.Fm 3 z = 3 * L.weierstrassP z * L.derivWeierstrassP z ^ 2
      - (deriv L.derivWeierstrassP z) ^ 2 / 4 := by
  have h1z : ((1 : ℕ) : ℂ) * z ∉ L.lattice := by rwa [Nat.cast_one, one_mul]
  have h2z' : ((1 + 1 : ℕ) : ℂ) * z ∉ L.lattice := by
    rwa [show ((1 + 1 : ℕ) : ℂ) = (2 : ℂ) by norm_num]
  have hM := L.Fm_master 1 1 hz h1z h2z'
  simp only [show 2 * 1 + 1 = 3 from rfl, show 1 + 1 = 2 from rfl] at hM
  rw [L.Fm_one hz, mul_one, one_pow, mul_one] at hM
  rw [show ((1 : ℕ) : ℂ) * z = z by rw [Nat.cast_one, one_mul],
    show ((2 : ℕ) : ℂ) * z = 2 * z by norm_num] at hM
  rw [L.Fm_two hz] at hM
  have hdup := L.wp_dup hz h2z
  rw [hM]
  linear_combination -hdup / 4

/-! ## `propfmpm`: `F_m = P̂_m(℘)` (odd `m`) and `F_m = −℘′·P̂_m(℘)` (even `m`)

`P̂_m` is Milla's division polynomial `P_m` with coefficients evaluated at
`h₂ = ¼g₂`, `h₃ = ¼g₃` (paper Thm. `propfmpm`). -/

open Polynomial

/-- The evaluation `ℤ[h₂, h₃] → ℂ`, `h₂ ↦ ¼g₂`, `h₃ ↦ ¼g₃`. -/
noncomputable def coeffToC : Milla.Coeff →+* ℂ :=
  (MvPolynomial.aeval (R := ℤ) ![L.g₂ / 4, L.g₃ / 4]).toRingHom

/-- `P̂_m ∈ ℂ[X]`: Milla's division polynomial with `h₂ = ¼g₂`, `h₃ = ¼g₃`. -/
noncomputable def Pc (m : ℕ) : Polynomial ℂ := (Milla.P m).map L.coeffToC

private lemma coeffToC_h2 : L.coeffToC Milla.h2 = L.g₂ / 4 := by
  simp [coeffToC, Milla.h2]

private lemma coeffToC_h3 : L.coeffToC Milla.h3 = L.g₃ / 4 := by
  simp [coeffToC, Milla.h3]

private lemma Pc_one : L.Pc 1 = 1 := by simp [Pc]

private lemma Pc_two : L.Pc 2 = 1 := by simp [Pc]

private lemma eval_Pc_three (x : ℂ) :
    (L.Pc 3).eval x
      = 3 * x ^ 4 - 6 * (L.g₂ / 4) * x ^ 2 - 12 * (L.g₃ / 4) * x - (L.g₂ / 4) ^ 2 := by
  simp [Pc, Milla.P_three, L.coeffToC_h2, L.coeffToC_h3, map_ofNat]

private lemma eval_Pc_four (x : ℂ) :
    (L.Pc 4).eval x
      = 2 * x ^ 6 - 10 * (L.g₂ / 4) * x ^ 4 - 40 * (L.g₃ / 4) * x ^ 3
        - 10 * (L.g₂ / 4) ^ 2 * x ^ 2 - 8 * (L.g₂ / 4) * (L.g₃ / 4) * x
        - (16 * (L.g₃ / 4) ^ 2 - 2 * (L.g₂ / 4) ^ 3) := by
  simp [Pc, Milla.P_four, L.coeffToC_h2, L.coeffToC_h3, map_ofNat]

private lemma eval_Pc_E (x : ℂ) :
    (Milla.E.map L.coeffToC).eval x = (4 * x ^ 3 - L.g₂ * x - L.g₃) ^ 2 := by
  simp [Milla.E, L.coeffToC_h2, L.coeffToC_h3]
  ring

private lemma Pc_rec_one {k : ℕ} (hk : 1 ≤ k) :
    L.Pc (4 * k + 1)
      = Milla.E.map L.coeffToC * L.Pc (2 * k + 2) * L.Pc (2 * k) ^ 3
        - L.Pc (2 * k - 1) * L.Pc (2 * k + 1) ^ 3 := by
  simp only [Pc, Milla.P_four_mul_add_one hk, Polynomial.map_sub, Polynomial.map_mul,
    Polynomial.map_pow]

private lemma Pc_rec_two {k : ℕ} (hk : 1 ≤ k) :
    L.Pc (4 * k + 2)
      = L.Pc (2 * k + 1)
        * (L.Pc (2 * k + 3) * L.Pc (2 * k) ^ 2 - L.Pc (2 * k - 1) * L.Pc (2 * k + 2) ^ 2) := by
  simp only [Pc, Milla.P_four_mul_add_two hk, Polynomial.map_sub, Polynomial.map_mul,
    Polynomial.map_pow]

private lemma Pc_rec_three {k : ℕ} (hk : 1 ≤ k) :
    L.Pc (4 * k + 3)
      = L.Pc (2 * k + 3) * L.Pc (2 * k + 1) ^ 3
        - Milla.E.map L.coeffToC * L.Pc (2 * k) * L.Pc (2 * k + 2) ^ 3 := by
  simp only [Pc, Milla.P_four_mul_add_three hk, Polynomial.map_sub, Polynomial.map_mul,
    Polynomial.map_pow]

private lemma Pc_rec_four {k : ℕ} (hk : 1 ≤ k) :
    L.Pc (4 * k + 4)
      = L.Pc (2 * k + 2)
        * (L.Pc (2 * k + 4) * L.Pc (2 * k + 1) ^ 2 - L.Pc (2 * k) * L.Pc (2 * k + 3) ^ 2) := by
  simp only [Pc, Milla.P_four_mul_add_four hk, Polynomial.map_sub, Polynomial.map_mul,
    Polynomial.map_pow]

/-- Milla's `propfmpm`: at a generic point `z` (all nonzero integer multiples of `z`
avoid `L`), `F_m(z) = P̂_m(℘(z))` for odd `m` and `F_m(z) = −℘′(z)·P̂_m(℘(z))` for
even `m`. -/
theorem propfmpm (m : ℕ) {z : ℂ} (hz : ∀ k : ℕ, k ≠ 0 → (k : ℂ) * z ∉ L.lattice) :
    (Odd m → L.Fm m z = (L.Pc m).eval (L.weierstrassP z))
      ∧ (Even m → L.Fm m z
          = -L.derivWeierstrassP z * (L.Pc m).eval (L.weierstrassP z)) := by
  induction m using Nat.strong_induction_on with
  | _ m IH =>
    have hz1 : z ∉ L.lattice := by
      have := hz 1 one_ne_zero
      rwa [Nat.cast_one, one_mul] at this
    have h2z : 2 * z ∉ L.lattice := by
      have := hz 2 two_ne_zero
      rwa [Nat.cast_ofNat] at this
    have hode := L.derivWeierstrassP_sq z hz1
    by_cases h5 : m < 5
    · -- base cases `m = 0, 1, 2, 3, 4`
      interval_cases m
      · refine ⟨fun h => absurd (Nat.odd_iff.mp h) (by norm_num), fun _ => ?_⟩
        simp [L.Fm_zero, Pc]
      · refine ⟨fun _ => ?_, fun h => absurd (Nat.even_iff.mp h) (by norm_num)⟩
        rw [L.Fm_one hz1, L.Pc_one]
        simp
      · refine ⟨fun h => absurd (Nat.odd_iff.mp h) (by norm_num), fun _ => ?_⟩
        rw [L.Fm_two hz1, L.Pc_two]
        simp
      · refine ⟨fun _ => ?_, fun h => absurd (Nat.even_iff.mp h) (by norm_num)⟩
        rw [L.Fm_three hz1 h2z, L.eval_Pc_three, L.lemwp2str hz1]
        linear_combination (3 * L.weierstrassP z) * hode
      · refine ⟨fun h => absurd (Nat.odd_iff.mp h) (by norm_num), fun _ => ?_⟩
        rw [L.Fm_four hz1 h2z, L.eval_Pc_four, L.lemwp2str hz1]
        linear_combination (-L.derivWeierstrassP z
          * (3 * L.weierstrassP z * (6 * L.weierstrassP z ^ 2 - L.g₂ / 2)
            - L.derivWeierstrassP z ^ 2
            - (4 * L.weierstrassP z ^ 3 - L.g₂ * L.weierstrassP z - L.g₃))) * hode
    · -- recursive cases `m = 4i + r`, `r ∈ {5, 6, 7, 8}`
      obtain ⟨i, hm⟩ : ∃ i, m = 4 * i + 5 ∨ m = 4 * i + 6 ∨ m = 4 * i + 7 ∨ m = 4 * i + 8 :=
        ⟨(m - 5) / 4, by omega⟩
      have IHodd : ∀ n, n < m → Odd n → L.Fm n z = (L.Pc n).eval (L.weierstrassP z) :=
        fun n hn ho => (IH n hn).1 ho
      have IHeven : ∀ n, n < m → Even n →
          L.Fm n z = -L.derivWeierstrassP z * (L.Pc n).eval (L.weierstrassP z) :=
        fun n hn he => (IH n hn).2 he
      have hP'ne : L.derivWeierstrassP z ≠ 0 := fun h0 =>
        h2z ((L.derivWeierstrassP_eq_zero_iff hz1).mp h0)
      set x := L.weierstrassP z with hxdef
      rcases hm with hm | hm | hm | hm <;> subst hm
      · -- `m = 4i+5`, odd
        refine ⟨fun _ => ?_, fun he => absurd (Nat.even_iff.mp he) (by omega)⟩
        have hrec := L.lemfrekur_odd (2 * i + 1) hz
        rw [show 2 * (2 * i + 1) + 3 = 4 * i + 5 from by ring,
          show 2 * i + 1 + 3 = 2 * i + 4 from rfl, show 2 * i + 1 + 1 = 2 * i + 2 from rfl,
          show 2 * i + 1 + 2 = 2 * i + 3 from rfl] at hrec
        have h1 := IHeven (2 * i + 4) (by omega) ⟨i + 2, by ring⟩
        have h2 := IHeven (2 * i + 2) (by omega) ⟨i + 1, by ring⟩
        have h3 := IHodd (2 * i + 1) (by omega) ⟨i, by ring⟩
        have h4 := IHodd (2 * i + 3) (by omega) ⟨i + 1, by ring⟩
        rw [hrec, h1, h2, h3, h4]
        have hPrec := L.Pc_rec_one (k := i + 1) (by omega)
        rw [show 4 * (i + 1) + 1 = 4 * i + 5 from by ring,
          show 2 * (i + 1) + 2 = 2 * i + 4 from by ring,
          show 2 * (i + 1) - 1 = 2 * i + 1 from by omega,
          show 2 * (i + 1) + 1 = 2 * i + 3 from by ring,
          show 2 * (i + 1) = 2 * i + 2 from by ring] at hPrec
        rw [hPrec]
        simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow,
          L.eval_Pc_E]
        linear_combination ((L.Pc (2 * i + 4)).eval x * (L.Pc (2 * i + 2)).eval x ^ 3
          * (L.derivWeierstrassP z ^ 2 + (4 * x ^ 3 - L.g₂ * x - L.g₃))) * hode
      · -- `m = 4i+6`, even
        refine ⟨fun ho => absurd (Nat.odd_iff.mp ho) (by omega), fun _ => ?_⟩
        have hrec := L.lemfrekur_even (2 * i + 1) hz
        rw [show 2 * (2 * i + 1) + 4 = 4 * i + 6 from by ring,
          show 2 * i + 1 + 2 = 2 * i + 3 from rfl, show 2 * i + 1 + 4 = 2 * i + 5 from rfl,
          show 2 * i + 1 + 1 = 2 * i + 2 from rfl,
          show 2 * i + 1 + 3 = 2 * i + 4 from rfl] at hrec
        rw [L.Fm_two hz1] at hrec
        have h1 := IHodd (2 * i + 3) (by omega) ⟨i + 1, by ring⟩
        have h2 := IHodd (2 * i + 5) (by omega) ⟨i + 2, by ring⟩
        have h3 := IHeven (2 * i + 2) (by omega) ⟨i + 1, by ring⟩
        have h4 := IHodd (2 * i + 1) (by omega) ⟨i, by ring⟩
        have h5' := IHeven (2 * i + 4) (by omega) ⟨i + 2, by ring⟩
        rw [h1, h2, h3, h4, h5'] at hrec
        have hPrec := L.Pc_rec_two (k := i + 1) (by omega)
        rw [show 4 * (i + 1) + 2 = 4 * i + 6 from by ring,
          show 2 * (i + 1) + 1 = 2 * i + 3 from by ring,
          show 2 * (i + 1) + 3 = 2 * i + 5 from by ring,
          show 2 * (i + 1) - 1 = 2 * i + 1 from by omega,
          show 2 * (i + 1) + 2 = 2 * i + 4 from by ring,
          show 2 * (i + 1) = 2 * i + 2 from by ring] at hPrec
        have hgoal : L.Fm (4 * i + 6) z * (-L.derivWeierstrassP z)
            = -L.derivWeierstrassP z * (L.Pc (4 * i + 6)).eval x
              * (-L.derivWeierstrassP z) := by
          rw [hrec, hPrec]
          simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow]
          ring
        exact mul_right_cancel₀ (neg_ne_zero.mpr hP'ne) hgoal
      · -- `m = 4i+7`, odd
        refine ⟨fun _ => ?_, fun he => absurd (Nat.even_iff.mp he) (by omega)⟩
        have hrec := L.lemfrekur_odd (2 * i + 2) hz
        rw [show 2 * (2 * i + 2) + 3 = 4 * i + 7 from by ring,
          show 2 * i + 2 + 3 = 2 * i + 5 from rfl, show 2 * i + 2 + 1 = 2 * i + 3 from rfl,
          show 2 * i + 2 + 2 = 2 * i + 4 from rfl] at hrec
        have h1 := IHodd (2 * i + 5) (by omega) ⟨i + 2, by ring⟩
        have h2 := IHodd (2 * i + 3) (by omega) ⟨i + 1, by ring⟩
        have h3 := IHeven (2 * i + 2) (by omega) ⟨i + 1, by ring⟩
        have h4 := IHeven (2 * i + 4) (by omega) ⟨i + 2, by ring⟩
        rw [hrec, h1, h2, h3, h4]
        have hPrec := L.Pc_rec_three (k := i + 1) (by omega)
        rw [show 4 * (i + 1) + 3 = 4 * i + 7 from by ring,
          show 2 * (i + 1) + 3 = 2 * i + 5 from by ring,
          show 2 * (i + 1) + 1 = 2 * i + 3 from by ring,
          show 2 * (i + 1) + 2 = 2 * i + 4 from by ring,
          show 2 * (i + 1) = 2 * i + 2 from by ring] at hPrec
        rw [hPrec]
        simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow,
          L.eval_Pc_E]
        linear_combination (-((L.Pc (2 * i + 2)).eval x * (L.Pc (2 * i + 4)).eval x ^ 3
          * (L.derivWeierstrassP z ^ 2 + (4 * x ^ 3 - L.g₂ * x - L.g₃)))) * hode
      · -- `m = 4i+8`, even
        refine ⟨fun ho => absurd (Nat.odd_iff.mp ho) (by omega), fun _ => ?_⟩
        have hrec := L.lemfrekur_even (2 * i + 2) hz
        rw [show 2 * (2 * i + 2) + 4 = 4 * i + 8 from by ring,
          show 2 * i + 2 + 2 = 2 * i + 4 from rfl, show 2 * i + 2 + 4 = 2 * i + 6 from rfl,
          show 2 * i + 2 + 1 = 2 * i + 3 from rfl,
          show 2 * i + 2 + 3 = 2 * i + 5 from rfl] at hrec
        rw [L.Fm_two hz1] at hrec
        have h1 := IHeven (2 * i + 4) (by omega) ⟨i + 2, by ring⟩
        have h2 := IHeven (2 * i + 6) (by omega) ⟨i + 3, by ring⟩
        have h3 := IHodd (2 * i + 3) (by omega) ⟨i + 1, by ring⟩
        have h4 := IHeven (2 * i + 2) (by omega) ⟨i + 1, by ring⟩
        have h5' := IHodd (2 * i + 5) (by omega) ⟨i + 2, by ring⟩
        rw [h1, h2, h3, h4, h5'] at hrec
        have hPrec := L.Pc_rec_four (k := i + 1) (by omega)
        rw [show 4 * (i + 1) + 4 = 4 * i + 8 from by ring,
          show 2 * (i + 1) + 4 = 2 * i + 6 from by ring,
          show 2 * (i + 1) + 1 = 2 * i + 3 from by ring,
          show 2 * (i + 1) + 3 = 2 * i + 5 from by ring,
          show 2 * (i + 1) + 2 = 2 * i + 4 from by ring,
          show 2 * (i + 1) = 2 * i + 2 from by ring] at hPrec
        have hgoal : L.Fm (4 * i + 8) z * (-L.derivWeierstrassP z)
            = -L.derivWeierstrassP z * (L.Pc (4 * i + 8)).eval x
              * (-L.derivWeierstrassP z) := by
          rw [hrec, hPrec]
          simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow]
          ring
        exact mul_right_cancel₀ (neg_ne_zero.mpr hP'ne) hgoal

/-! ## `thmbaker` (paper Thm. `thmbaker`)

Both sides are polynomials in `℘(z)`; by `propfmprod` and `propfmpm` they agree at
`℘(z)` for every generic `z`, and `℘` takes infinitely many values at generic points
(irrational real multiples of `ω₁`), so they agree in `ℂ[X]`. -/

/-- An irrational real multiple of `ω₁` is not a lattice point. -/
private lemma irrational_mul_ω₁_notMem {s : ℝ} (hs : Irrational s) :
    (s : ℂ) * L.ω₁ ∉ L.lattice := by
  intro h
  obtain ⟨a, b, hab⟩ := PeriodPair.mem_lattice.mp h
  have hzero : ((a : ℝ) - s) • L.ω₁ + ((b : ℝ)) • L.ω₂ = 0 := by
    simp only [Complex.real_smul]
    push_cast
    linear_combination hab
  have hpair := (LinearIndependent.pair_iff.mp L.indep) _ _ hzero
  have h1 : (a : ℝ) - s = 0 := hpair.1
  exact hs ⟨(a : ℚ), by push_cast; linarith⟩

/-- `℘` takes infinitely many distinct values at generic points. -/
private lemma infinite_wp_generic :
    {x : ℂ | ∃ z : ℂ, (∀ k : ℕ, k ≠ 0 → (k : ℂ) * z ∉ L.lattice)
      ∧ L.weierstrassP z = x}.Infinite := by
  set t : ℕ → ℝ := fun n => ((1 / (n + 2) : ℚ) : ℝ) * Real.sqrt 2 with ht
  set zpt : ℕ → ℂ := fun n => ((t n : ℝ) : ℂ) * L.ω₁ with hzpt
  have hgen : ∀ n, ∀ k : ℕ, k ≠ 0 → (k : ℂ) * zpt n ∉ L.lattice := by
    intro n k hk
    have hirr : Irrational ((k : ℝ) * t n) := by
      have heq : (k : ℝ) * t n = ((k / (n + 2) : ℚ) : ℝ) * Real.sqrt 2 := by
        simp only [ht]
        push_cast
        ring
      rw [heq]
      refine irrational_sqrt_two.ratCast_mul (div_ne_zero ?_ (by positivity))
      exact_mod_cast hk
    have heq2 : (k : ℂ) * zpt n = (((k : ℝ) * t n : ℝ) : ℂ) * L.ω₁ := by
      simp only [hzpt]
      push_cast
      ring
    rw [heq2]
    exact L.irrational_mul_ω₁_notMem hirr
  have hnotMem : ∀ n, zpt n ∉ L.lattice := by
    intro n
    have := hgen n 1 one_ne_zero
    rwa [Nat.cast_one, one_mul] at this
  have hval_ne : ∀ i j : ℕ, i ≠ j →
      L.weierstrassP (zpt i) ≠ L.weierstrassP (zpt j) := by
    intro i j hij
    have hqne : (1 / (i + 2) - 1 / (j + 2) : ℚ) ≠ 0 := by
      intro h0
      apply hij
      have h1 : (1 / (i + 2) : ℚ) = 1 / (j + 2) := by linarith [sub_eq_zero.mp h0]
      have h2 : ((j : ℚ) + 2) = ((i : ℚ) + 2) := by
        field_simp at h1
        linarith
      exact_mod_cast (by linarith : (i : ℚ) = (j : ℚ))
    have hsub : zpt i - zpt j ∉ L.lattice := by
      have heq : zpt i - zpt j = ((t i - t j : ℝ) : ℂ) * L.ω₁ := by
        simp only [hzpt]
        push_cast
        ring
      rw [heq]
      apply L.irrational_mul_ω₁_notMem
      have heq2 : t i - t j = ((1 / (i + 2) - 1 / (j + 2) : ℚ) : ℝ) * Real.sqrt 2 := by
        simp only [ht]
        push_cast
        ring
      rw [heq2]
      exact irrational_sqrt_two.ratCast_mul hqne
    have hadd : zpt i + zpt j ∉ L.lattice := by
      have heq : zpt i + zpt j = ((t i + t j : ℝ) : ℂ) * L.ω₁ := by
        simp only [hzpt]
        push_cast
        ring
      rw [heq]
      apply L.irrational_mul_ω₁_notMem
      have heq2 : t i + t j = ((1 / (i + 2) + 1 / (j + 2) : ℚ) : ℝ) * Real.sqrt 2 := by
        simp only [ht]
        push_cast
        ring
      rw [heq2]
      exact irrational_sqrt_two.ratCast_mul (by positivity)
    exact L.weierstrassP_ne_of_notMem (hnotMem i) (hnotMem j) hsub hadd
  refine Set.infinite_of_injective_forall_mem
    (f := fun n : ℕ => L.weierstrassP (zpt n)) ?_ ?_
  · intro i j hijeq
    by_contra hij
    exact hval_ne i j hij hijeq
  · intro n
    exact ⟨zpt n, hgen n, rfl⟩

/-- Milla's `thmbaker`, odd case: `m²·∏_{v ≠ 0}(X − ℘(u_v)) = P̂_m(X)²` in `ℂ[X]`. -/
theorem thmbaker_odd (m : ℕ) [NeZero m] (hm : Odd m) :
    Polynomial.C ((m : ℂ) ^ 2)
        * ∏ v ∈ Finset.univ.erase (0 : Fin m × Fin m),
            (Polynomial.X - Polynomial.C (L.weierstrassP (L.divPt m v)))
      = L.Pc m ^ 2 := by
  apply Polynomial.eq_of_infinite_eval_eq
  refine L.infinite_wp_generic.mono ?_
  rintro x ⟨z, hgen, rfl⟩
  have hz1 : z ∉ L.lattice := by
    have := hgen 1 one_ne_zero
    rwa [Nat.cast_one, one_mul] at this
  have hprod := L.propfmprod m hz1
  have hfm := (L.propfmpm m hgen).1 hm
  simp only [Set.mem_setOf_eq, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_pow]
  rw [← hfm]
  exact hprod.symm

/-- Milla's `thmbaker`, even case:
`m²·∏_{v ≠ 0}(X − ℘(u_v)) = P̂_m(X)²·4(X³ − ¼g₂X − ¼g₃)` in `ℂ[X]`. -/
theorem thmbaker_even (m : ℕ) [NeZero m] (hm : Even m) :
    Polynomial.C ((m : ℂ) ^ 2)
        * ∏ v ∈ Finset.univ.erase (0 : Fin m × Fin m),
            (Polynomial.X - Polynomial.C (L.weierstrassP (L.divPt m v)))
      = L.Pc m ^ 2
        * (Polynomial.C 4 * (Polynomial.X ^ 3 - Polynomial.C (L.g₂ / 4) * Polynomial.X
            - Polynomial.C (L.g₃ / 4))) := by
  apply Polynomial.eq_of_infinite_eval_eq
  refine L.infinite_wp_generic.mono ?_
  rintro x ⟨z, hgen, rfl⟩
  have hz1 : z ∉ L.lattice := by
    have := hgen 1 one_ne_zero
    rwa [Nat.cast_one, one_mul] at this
  have hprod := L.propfmprod m hz1
  have hfm := (L.propfmpm m hgen).2 hm
  have hode := L.derivWeierstrassP_sq z hz1
  simp only [Set.mem_setOf_eq, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_pow]
  rw [← hprod, hfm]
  linear_combination ((L.Pc m).eval (L.weierstrassP z)) ^ 2 * hode

/-! ## The endgame: integrality of `l_m·℘(u)` (paper Thm. `theomwpu`)

By `thmbaker`, each division value `℘(u)` is a root of `P̂_m(X)²·(4(X³ − h₂X − h₃))^{[m even]}`.
Roots of the monic cubic are integral over `R = ℤ[¼g₂, ¼g₃]`; for roots of `P̂_m` we use
`Polynomial.integralNormalization` together with the leading coefficient `l_m` computed in
`P_odd_leadingCoeff`/`P_even_leadingCoeff`. -/

/-- Evaluation `ℤ[h₂, h₃] → R = ℤ[¼g₂, ¼g₃]`. -/
noncomputable def coeffToR :
    Milla.Coeff →+* (Algebra.adjoin ℤ ({L.g₂ / 4, L.g₃ / 4} : Set ℂ)) :=
  (MvPolynomial.aeval (R := ℤ)
    ![⟨L.g₂ / 4, Algebra.subset_adjoin (by simp)⟩,
      ⟨L.g₃ / 4, Algebra.subset_adjoin (by simp)⟩]).toRingHom

/-- `coeffToC` factors through `R`. -/
private lemma coeffToC_eq_comp :
    L.coeffToC = (algebraMap (Algebra.adjoin ℤ ({L.g₂ / 4, L.g₃ / 4} : Set ℂ)) ℂ).comp
      L.coeffToR := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simp [coeffToC, coeffToR]
  · intro i
    fin_cases i <;> simp [coeffToC, coeffToR]

/-- `P_m` over `R`. -/
noncomputable def PR (m : ℕ) :
    Polynomial (Algebra.adjoin ℤ ({L.g₂ / 4, L.g₃ / 4} : Set ℂ)) :=
  (Milla.P m).map L.coeffToR

private lemma Pc_eq_PR_map (m : ℕ) :
    L.Pc m = (L.PR m).map (algebraMap (Algebra.adjoin ℤ ({L.g₂ / 4, L.g₃ / 4} : Set ℂ)) ℂ) := by
  rw [Pc, PR, Polynomial.map_map, ← L.coeffToC_eq_comp]

private lemma algebraMap_adjoin_injective :
    ∀ x : (Algebra.adjoin ℤ ({L.g₂ / 4, L.g₃ / 4} : Set ℂ)),
      algebraMap (Algebra.adjoin ℤ ({L.g₂ / 4, L.g₃ / 4} : Set ℂ)) ℂ x = 0 → x = 0 :=
  fun _ hx => Subtype.ext hx

/-- The leading coefficient of `P_m` transports to `R`. -/
private lemma PR_leadingCoeff (m l : ℕ) (hl : l ≠ 0)
    (hlead : (Milla.P m).leadingCoeff = ((l : ℕ) : Milla.Coeff)) :
    (L.PR m).leadingCoeff
      = ((l : ℕ) : (Algebra.adjoin ℤ ({L.g₂ / 4, L.g₃ / 4} : Set ℂ))) := by
  have hne : L.coeffToR (Milla.P m).leadingCoeff ≠ 0 := by
    rw [hlead, map_natCast]
    intro h0
    have h1 := congrArg (algebraMap (Algebra.adjoin ℤ ({L.g₂ / 4, L.g₃ / 4} : Set ℂ)) ℂ) h0
    rw [map_natCast, map_zero] at h1
    exact (Nat.cast_ne_zero (R := ℂ)).mpr hl h1
  rw [PR, Polynomial.leadingCoeff_map_of_leadingCoeff_ne_zero _ hne, hlead, map_natCast]

/-- Roots of `P̂_m`, scaled by the leading coefficient `l`, are integral over `R`. -/
private lemma isIntegral_of_Pc_root (m l : ℕ) (hl : l ≠ 0)
    (hlead : (Milla.P m).leadingCoeff = ((l : ℕ) : Milla.Coeff))
    {x : ℂ} (hx : (L.Pc m).eval x = 0) :
    IsIntegral (Algebra.adjoin ℤ ({L.g₂ / 4, L.g₃ / 4} : Set ℂ)) ((l : ℂ) * x) := by
  have hlc := L.PR_leadingCoeff m l hl hlead
  have hPRne : L.PR m ≠ 0 := by
    intro h0
    rw [h0, Polynomial.leadingCoeff_zero] at hlc
    have h1 := congrArg (algebraMap (Algebra.adjoin ℤ ({L.g₂ / 4, L.g₃ / 4} : Set ℂ)) ℂ)
      hlc.symm
    rw [map_natCast, map_zero] at h1
    exact (Nat.cast_ne_zero (R := ℂ)).mpr hl h1
  have haev : Polynomial.aeval x (L.PR m) = 0 := by
    rw [Polynomial.aeval_def, ← Polynomial.eval_map, ← L.Pc_eq_PR_map]
    exact hx
  have hroot := Polynomial.integralNormalization_aeval_eq_zero haev
    L.algebraMap_adjoin_injective
  rw [hlc, map_natCast] at hroot
  exact ⟨(L.PR m).integralNormalization,
    Polynomial.monic_integralNormalization hPRne,
    by rw [← Polynomial.aeval_def]; exact hroot⟩

/-- Roots of the (monic over `R`) cubic `4(X³ − h₂X − h₃)` are integral over `R`. -/
private lemma isIntegral_of_cubic_root {x : ℂ}
    (hx : 4 * (x ^ 3 - L.g₂ / 4 * x - L.g₃ / 4) = 0) :
    IsIntegral (Algebra.adjoin ℤ ({L.g₂ / 4, L.g₃ / 4} : Set ℂ)) x := by
  refine ⟨Polynomial.X ^ 3
      - Polynomial.C (⟨L.g₂ / 4, Algebra.subset_adjoin (by simp)⟩ :
          (Algebra.adjoin ℤ ({L.g₂ / 4, L.g₃ / 4} : Set ℂ))) * Polynomial.X
      - Polynomial.C (⟨L.g₃ / 4, Algebra.subset_adjoin (by simp)⟩ :
          (Algebra.adjoin ℤ ({L.g₂ / 4, L.g₃ / 4} : Set ℂ))), ?_, ?_⟩
  · have h : (Polynomial.X ^ 3
        - Polynomial.C (⟨L.g₂ / 4, Algebra.subset_adjoin (by simp)⟩ :
            (Algebra.adjoin ℤ ({L.g₂ / 4, L.g₃ / 4} : Set ℂ))) * Polynomial.X
        - Polynomial.C (⟨L.g₃ / 4, Algebra.subset_adjoin (by simp)⟩ :
            (Algebra.adjoin ℤ ({L.g₂ / 4, L.g₃ / 4} : Set ℂ))))
        = Polynomial.X ^ (2 + 1)
          - (Polynomial.C (⟨L.g₂ / 4, Algebra.subset_adjoin (by simp)⟩ :
              (Algebra.adjoin ℤ ({L.g₂ / 4, L.g₃ / 4} : Set ℂ))) * Polynomial.X
            + Polynomial.C (⟨L.g₃ / 4, Algebra.subset_adjoin (by simp)⟩ :
              (Algebra.adjoin ℤ ({L.g₂ / 4, L.g₃ / 4} : Set ℂ)))) := by
      ring
    rw [h]
    refine Polynomial.monic_X_pow_sub ?_
    compute_degree!
  · simp only [Polynomial.eval₂_sub, Polynomial.eval₂_mul, Polynomial.eval₂_pow,
      Polynomial.eval₂_X, Polynomial.eval₂_C]
    have hc2 : algebraMap (Algebra.adjoin ℤ ({L.g₂ / 4, L.g₃ / 4} : Set ℂ)) ℂ
        ⟨L.g₂ / 4, Algebra.subset_adjoin (by simp)⟩ = L.g₂ / 4 := rfl
    have hc3 : algebraMap (Algebra.adjoin ℤ ({L.g₂ / 4, L.g₃ / 4} : Set ℂ)) ℂ
        ⟨L.g₃ / 4, Algebra.subset_adjoin (by simp)⟩ = L.g₃ / 4 := rfl
    rw [hc2, hc3]
    linear_combination hx / 4

/-- The evaluation of the Baker product at a division value vanishes. -/
private lemma eval_baker_zero (m : ℕ) [NeZero m] {v : Fin m × Fin m} (hv : v ≠ 0) :
    Polynomial.eval (L.weierstrassP (L.divPt m v))
      (Polynomial.C ((m : ℂ) ^ 2)
        * ∏ v' ∈ Finset.univ.erase (0 : Fin m × Fin m),
            (Polynomial.X - Polynomial.C (L.weierstrassP (L.divPt m v')))) = 0 := by
  rw [Polynomial.eval_mul, Polynomial.eval_prod]
  apply mul_eq_zero_of_right
  apply Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hv, Finset.mem_univ v⟩)
  simp

end PeriodPair

namespace PeriodPair

variable (L : PeriodPair)

/-- Milla's `theomwpu`: for every `m`-division point `u`, `m·℘(u)` is integral over
`ℤ[¼g₂, ¼g₃]`. -/
theorem theomwpu (m : ℕ) [NeZero m] {v : Fin m × Fin m} (hv : v ≠ 0) :
    IsIntegral (Algebra.adjoin ℤ ({L.g₂ / 4, L.g₃ / 4} : Set ℂ))
      ((m : ℂ) * L.weierstrassP (L.divPt m v)) := by
  have h0 := L.eval_baker_zero m hv
  rcases Nat.even_or_odd m with hme | hmo
  · -- even `m`: the two factors of `thmbaker_even`
    rw [L.thmbaker_even m hme] at h0
    simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_sub,
      Polynomial.eval_X, Polynomial.eval_C] at h0
    obtain ⟨j, hj⟩ := hme
    have hj0 : j ≠ 0 := by have := NeZero.ne m; omega
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    have hm2 : m = 2 * j' + 2 := by omega
    rcases mul_eq_zero.mp h0 with h | h
    · have hev : (L.Pc m).eval (L.weierstrassP (L.divPt m v)) = 0 :=
        (pow_eq_zero_iff two_ne_zero).mp h
      have hlead : (Milla.P m).leadingCoeff = ((j' + 1 : ℕ) : Milla.Coeff) := by
        rw [hm2]; exact Milla.P_even_leadingCoeff j'
      have hint := L.isIntegral_of_Pc_root m (j' + 1) (by omega) hlead hev
      have hcast : (m : ℂ) * L.weierstrassP (L.divPt m v)
          = algebraMap (Algebra.adjoin ℤ ({L.g₂ / 4, L.g₃ / 4} : Set ℂ)) ℂ 2
            * (((j' + 1 : ℕ) : ℂ) * L.weierstrassP (L.divPt m v)) := by
        rw [map_ofNat]
        push_cast [hm2]
        ring
      rw [hcast]
      exact isIntegral_algebraMap.mul hint
    · have hint := L.isIntegral_of_cubic_root h
      have hcast : (m : ℂ) * L.weierstrassP (L.divPt m v)
          = algebraMap (Algebra.adjoin ℤ ({L.g₂ / 4, L.g₃ / 4} : Set ℂ)) ℂ ((m : ℕ))
            * L.weierstrassP (L.divPt m v) := by
        rw [map_natCast]
      rw [hcast]
      exact isIntegral_algebraMap.mul hint
  · -- odd `m`: `℘(u)` is a root of `P̂_m` and `l_m = m`
    obtain ⟨j, hj⟩ := hmo
    rw [L.thmbaker_odd m ⟨j, hj⟩, Polynomial.eval_pow] at h0
    have hev : (L.Pc m).eval (L.weierstrassP (L.divPt m v)) = 0 :=
      (pow_eq_zero_iff two_ne_zero).mp h0
    have hlead : (Milla.P m).leadingCoeff = ((m : ℕ) : Milla.Coeff) := by
      rw [hj]; exact Milla.P_odd_leadingCoeff j
    exact L.isIntegral_of_Pc_root m m (NeZero.ne m) hlead hev

/-- Milla's `theomwpu`, second half: for even `m`, already `(m/2)·℘(u)` is integral
over `ℤ[¼g₂, ¼g₃]`. -/
theorem theomwpu_even {m : ℕ} [NeZero m] (hm : Even m) {v : Fin m × Fin m} (hv : v ≠ 0) :
    IsIntegral (Algebra.adjoin ℤ ({L.g₂ / 4, L.g₃ / 4} : Set ℂ))
      ((m : ℂ) / 2 * L.weierstrassP (L.divPt m v)) := by
  have h0 := L.eval_baker_zero m hv
  rw [L.thmbaker_even m hm] at h0
  simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_sub,
    Polynomial.eval_X, Polynomial.eval_C] at h0
  obtain ⟨j, hj⟩ := hm
  have hj0 : j ≠ 0 := by have := NeZero.ne m; omega
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  have hm2 : m = 2 * j' + 2 := by omega
  have hdiv2 : (m : ℂ) / 2 = ((j' + 1 : ℕ) : ℂ) := by
    push_cast [hm2]
    ring
  rcases mul_eq_zero.mp h0 with h | h
  · have hev : (L.Pc m).eval (L.weierstrassP (L.divPt m v)) = 0 :=
      (pow_eq_zero_iff two_ne_zero).mp h
    have hlead : (Milla.P m).leadingCoeff = ((j' + 1 : ℕ) : Milla.Coeff) := by
      rw [hm2]; exact Milla.P_even_leadingCoeff j'
    rw [hdiv2]
    exact L.isIntegral_of_Pc_root m (j' + 1) (by omega) hlead hev
  · have hint := L.isIntegral_of_cubic_root h
    have hcast : (m : ℂ) / 2 * L.weierstrassP (L.divPt m v)
        = algebraMap (Algebra.adjoin ℤ ({L.g₂ / 4, L.g₃ / 4} : Set ℂ)) ℂ ((j' + 1 : ℕ))
          * L.weierstrassP (L.divPt m v) := by
      rw [map_natCast, hdiv2]
    rw [hcast]
    exact isIntegral_algebraMap.mul hint

end PeriodPair
