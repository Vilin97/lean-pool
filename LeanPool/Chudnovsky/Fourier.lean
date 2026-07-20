/-
Copyright (c) 2026 Xuanji Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuanji Li
-/

import LeanPool.Chudnovsky.Lattices
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.QExpansion
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues

/-!
# Fourier expansions: the lattice ↔ modular-forms bridge

Statements from chapter 4 of Milla (arXiv:1809.00533v6, file `090_Fourier.tex`):

* the σ product formula (paper `fouriersigma`)
  `σ(z; L_τ) = (2πi)⁻¹·e^{η₁z²/2}·(q_z^{1/2} - q_z^{-1/2})·∏_{n≥1} (1-q^n q_z)(1-q^n/q_z)/(1-q^n)²`
  with `q_z^{±1/2}` written branch-free as `e^{±πiz}`;
* the bridge to normalized Eisenstein series (paper Thm. `fouriertheorem`):
  `η₁(L_τ) = π²E₂(τ)/3`, `g₂(L_τ) = (4/3)π⁴E₄(τ)`, `g₃(L_τ) = (8/27)π⁶E₆(τ)`,
  `Δ(L_τ) = (2π)¹²/1728·(E₄³-E₆²)`, and `J(L_τ) = E₄³/(E₄³-E₆²) = Chudnovsky.J τ`.

Note the sign trap in the paper's `satzphi` (its displayed transformation
`φ(z+τ) = -e^{2πiz}φ(z)` should read `φ(z+τ) = -e^{-2πiz}φ(z)`, as in its proof); the
final product formula `fouriersigma` stated here is unaffected.

All statements in this file are fully proved.
-/

noncomputable section

namespace Chudnovsky

open Complex ModularForm EisensteinSeries

open UpperHalfPlane hiding I

open scoped Real

/-! ### Helpers for the lattice ↔ Eisenstein-series bridge -/

/-- Reindexing equivalence `ℤ × ℤ ≃ (Fin 2 → ℤ)`, `(m, n) ↦ ![n, m]`, used to match the
lattice sum defining `PeriodPair.G` with Mathlib's `eisSummand` summation over `Fin 2 → ℤ`. -/
private def pairArrowEquiv : ℤ × ℤ ≃ (Fin 2 → ℤ) :=
  (Equiv.prodComm ℤ ℤ).trans (finTwoArrowEquiv ℤ).symm

private lemma pairArrowEquiv_apply (x : ℤ × ℤ) : pairArrowEquiv x = ![x.2, x.1] := rfl

/-- `ζ(k) = 1` bridge: the lattice Eisenstein series `G k` of `L_τ` equals
`ζ(k)·eisensteinSeries` for `k ≥ 3`. -/
private lemma G_Lτ_eq (τ : ℍ) {k : ℕ} (hk : 3 ≤ k) :
    (Lτ τ).G k = riemannZeta k * eisensteinSeries (N := 1) 0 k τ := by
  rw [← tsum_eisSummand_eq_riemannZeta_mul_eisensteinSeries hk τ, PeriodPair.G,
    ← ((Lτ τ).latticeEquivProd.symm.toEquiv).tsum_eq
        (fun l : (Lτ τ).lattice => ((l : ℂ) ^ k)⁻¹),
    ← pairArrowEquiv.tsum_eq (fun v => eisSummand (k : ℤ) v τ)]
  refine tsum_congr fun x => ?_
  have hbase : (((Lτ τ).latticeEquivProd.symm.toEquiv x : (Lτ τ).lattice) : ℂ)
      = (x.1 : ℂ) + (x.2 : ℂ) * (τ : ℂ) := by
    have h := (Lτ τ).latticeEquiv_symm_apply x
    simpa using h
  rw [hbase, eisSummand, pairArrowEquiv_apply]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [zpow_neg, zpow_natCast, add_comm]

/-- `eisensteinSeries 0 k = 2·E k` (the normalisation `E = (1/2)·eisensteinSeries`). -/
private lemma eisensteinSeries_eq_two_E (τ : ℍ) {k : ℕ} (hk : 3 ≤ k) :
    eisensteinSeries (N := 1) 0 k τ = 2 * (E hk) τ := by
  rw [show (E hk) τ = (1 / 2 : ℂ) • eisensteinSeriesSIF (N := 1) 0 k τ from rfl,
    eisensteinSeriesSIF_apply, smul_eq_mul]
  ring

/-- `ζ(6) = π⁶/945`. -/
private lemma riemannZeta_six : riemannZeta 6 = (π : ℂ) ^ 6 / 945 := by
  have h := riemannZeta_two_mul_nat (k := 3) (by norm_num)
  norm_num [show bernoulli 6 = 1 / 42 by decide +kernel] at h
  rw [h]; ring

private lemma pi_C_ne_zero : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero

/-- `η₁(L_τ) = π²·E₂(τ)/3` (paper Thm. `fouriertheorem`). Together with
`eta₁_Lτ_eq_G2` this is Mathlib's `G₂ = 2ζ(2)·E₂` with `ζ(2) = π²/6`. -/
theorem eta₁_Lτ (τ : ℍ) : (Lτ τ).eta₁ = (π : ℂ) ^ 2 / 3 * E2 τ := by
  have hz : (2 * riemannZeta 2 : ℂ) ≠ 0 := by
    rw [riemannZeta_two]
    exact mul_ne_zero two_ne_zero (div_ne_zero (pow_ne_zero 2 pi_C_ne_zero) (by norm_num))
  have hE2 : G2 τ = 2 * riemannZeta 2 * E2 τ := by
    have hdef : E2 τ = (1 / (2 * riemannZeta 2)) • G2 τ := rfl
    rw [hdef, smul_eq_mul, ← mul_assoc, mul_one_div, div_self hz, one_mul]
  rw [eta₁_Lτ_eq_G2, hE2, riemannZeta_two]; ring

/-- `g₂(L_τ) = (4/3)·π⁴·E₄(τ)` (paper Thm. `fouriertheorem`). -/
theorem g₂_Lτ (τ : ℍ) : (Lτ τ).g₂ = 4 / 3 * (π : ℂ) ^ 4 * E₄ τ := by
  rw [PeriodPair.g₂, G_Lτ_eq τ (by norm_num), eisensteinSeries_eq_two_E τ (by norm_num)]
  rw [show ((4 : ℕ) : ℂ) = 4 by norm_num, riemannZeta_four]
  ring

/-- `g₃(L_τ) = (8/27)·π⁶·E₆(τ)` (paper Thm. `fouriertheorem`). -/
theorem g₃_Lτ (τ : ℍ) : (Lτ τ).g₃ = 8 / 27 * (π : ℂ) ^ 6 * E₆ τ := by
  rw [PeriodPair.g₃, G_Lτ_eq τ (by norm_num), eisensteinSeries_eq_two_E τ (by norm_num)]
  rw [show ((6 : ℕ) : ℂ) = 6 by norm_num, riemannZeta_six]
  ring

/-- `Δ(L_τ) = (2π)¹²/1728·(E₄(τ)³ - E₆(τ)²)` (paper Thm. `fouriertheorem`). -/
theorem discr_Lτ (τ : ℍ) :
    (Lτ τ).discr = (2 * (π : ℂ)) ^ 12 / 1728 * (E₄ τ ^ 3 - E₆ τ ^ 2) := by
  rw [PeriodPair.discr, g₂_Lτ, g₃_Lτ]; ring

/-- Klein's absolute invariant of the lattice `L_τ` agrees with the modular `J`-function
`J = E₄³/(E₄³ - E₆²)` of `Basic.lean`, i.e. `J(τ) = g₂³/(g₂³ - 27g₃²)` evaluated at `L_τ`
(paper Thm. `fouriertheorem` and Def. `defijdelta`). -/
theorem J_eq_J_Lτ (τ : ℍ) : J τ = (Lτ τ).J := by
  have hne := E₄_cube_sub_E₆_sq_ne_zero τ
  rw [PeriodPair.J, g₂_Lτ, discr_Lτ, J]
  field_simp
  ring

/-! ### The σ transformation law (paper `trafosigma`)

`σ(z + ω) = -exp(η_ω·(z + ω/2))·σ(z)` for a basic period `ω` of the lattice. This is derived
by the log-derivative constancy argument: `σ(z+ω)/(exp(η(z+ω/2))·σ(z))` has zero derivative
on the connected set `Lᶜ`, hence is constant, and the constant is `-1` by oddness of `σ`. -/

/-- The lattice is a countable subset of `ℂ`. -/
private lemma countable_lattice (L : PeriodPair) : (↑L.lattice : Set ℂ).Countable := by
  have : Countable ↥L.lattice := countable_of_Lindelof_of_discrete
  simpa using Set.countable_range (Subtype.val : ↥L.lattice → ℂ)

/-- The complement of the lattice is dense in `ℂ`. -/
private lemma dense_compl_lattice (L : PeriodPair) : Dense (↑L.lattice : Set ℂ)ᶜ :=
  (countable_lattice L).dense_compl ℂ

/-- The σ-transformation law in a period direction `ω`: given `ω ∈ L`, `ω/2 ∉ L`, and the
quasi-periodicity `ζ(z+ω) = ζ(z) + μ` (for `z ∉ L`), then
`σ(z+ω) = -exp(μ·(z+ω/2))·σ(z)`. -/
private lemma weierstrassSigma_add_period (L : PeriodPair) (ω : ℂ) (hωlat : ω ∈ L.lattice)
    (hω2 : ω / 2 ∉ L.lattice) (μ : ℂ)
    (hμ : ∀ z ∉ L.lattice, L.weierstrassZeta (z + ω) = L.weierstrassZeta z + μ) (z : ℂ) :
    L.weierstrassSigma (z + ω) =
      -Complex.exp (μ * (z + ω / 2)) * L.weierstrassSigma z := by
  classical
  set sig := L.weierstrassSigma with hsig
  set S : Set ℂ := (↑L.lattice)ᶜ with hSdef
  have hSopen : IsOpen S := L.isClosed_lattice.isOpen_compl
  have hSconn : IsPreconnected S :=
    ((countable_lattice L).isConnected_compl_of_one_lt_rank (by simp)).isPreconnected
  have hσdiff : Differentiable ℂ sig := L.differentiable_weierstrassSigma
  have hmem : ∀ {x : ℂ}, x ∉ L.lattice → x + ω ∉ L.lattice := by
    intro x hx hc; exact hx (by simpa using sub_mem hc hωlat)
  have hσne : ∀ {x : ℂ}, x ∉ L.lattice → sig x ≠ 0 := by
    intro x hx; rw [hsig]; exact fun h => hx ((L.weierstrassSigma_eq_zero_iff x).mp h)
  set E : ℂ → ℂ := fun z => Complex.exp (μ * (z + ω / 2)) with hE
  set g : ℂ → ℂ := fun z => E z * sig z with hg
  set m : ℂ → ℂ := fun z => sig (z + ω) * (g z)⁻¹ with hm
  have hEderiv : ∀ z, HasDerivAt E (μ * E z) z := by
    intro z
    have hlin : HasDerivAt (fun z : ℂ => μ * (z + ω / 2)) μ z := by
      simpa using ((hasDerivAt_id z).add_const (ω / 2)).const_mul μ
    simpa [hE, mul_comm] using hlin.cexp
  have hf : ∀ z, HasDerivAt (fun z => sig (z + ω)) (deriv sig (z + ω)) z := by
    intro z
    have h := (hσdiff (z + ω)).hasDerivAt.comp z ((hasDerivAt_id z).add_const ω)
    rw [mul_one] at h
    exact h
  have hEne : ∀ z, E z ≠ 0 := fun z => Complex.exp_ne_zero _
  have hgne : ∀ {z}, z ∉ L.lattice → g z ≠ 0 := fun hz => mul_ne_zero (hEne _) (hσne hz)
  -- The Wronskian-type identity from quasi-periodicity of ζ.
  have hident : ∀ z ∈ S, deriv sig (z + ω) * sig z - sig (z + ω) * deriv sig z
      = μ * (sig (z + ω) * sig z) := by
    intro z hzS
    have hz : z ∉ L.lattice := hzS
    have hzω : z + ω ∉ L.lattice := hmem hz
    have h1 : deriv sig z / sig z = L.weierstrassZeta z := by
      have := L.logDeriv_weierstrassSigma z hz; rwa [logDeriv_apply] at this
    have h2 : deriv sig (z + ω) / sig (z + ω) = L.weierstrassZeta (z + ω) := by
      have := L.logDeriv_weierstrassSigma (z + ω) hzω; rwa [logDeriv_apply] at this
    rw [hμ z hz] at h2
    have hdz := hσne hz
    have hdzω := hσne hzω
    rw [div_eq_iff hdz] at h1
    rw [div_eq_iff hdzω] at h2
    rw [h1, h2]; ring
  -- `m` has zero derivative on `S`.
  have hmderiv : ∀ z ∈ S, HasDerivAt m 0 z := by
    intro z hzS
    have hz : z ∉ L.lattice := hzS
    have hgderiv : HasDerivAt g (μ * E z * sig z + E z * deriv sig z) z :=
      (hEderiv z).mul (hσdiff z).hasDerivAt
    have hginv : HasDerivAt (fun z => (g z)⁻¹)
        (-(μ * E z * sig z + E z * deriv sig z) / g z ^ 2) z :=
      hgderiv.inv (hgne hz)
    have hcomp := (hf z).mul hginv
    have hval : deriv sig (z + ω) * (g z)⁻¹
        + sig (z + ω) * (-(μ * E z * sig z + E z * deriv sig z) / g z ^ 2) = 0 := by
      have hid := hident z hzS
      have hgn := hgne hz
      field_simp [hg]
      linear_combination (E z) * hid
    rw [hval] at hcomp
    exact hcomp
  -- Hence `m = -1` on `S`.
  have hmconst : Set.EqOn m (fun _ => (-1 : ℂ)) S := by
    have hx0mem : -(ω / 2) ∈ S := by
      change -(ω / 2) ∉ L.lattice; intro hc; exact hω2 (by simpa using neg_mem hc)
    have hval0 : m (-(ω / 2)) = -1 := by
      have e1 : -(ω / 2) + ω = ω / 2 := by ring
      have hEval : E (-(ω / 2)) = 1 := by
        simp only [hE]; rw [show μ * (-(ω / 2) + ω / 2) = 0 by ring, Complex.exp_zero]
      have hodd : sig (-(ω / 2)) = -sig (ω / 2) := L.weierstrassSigma_neg (ω / 2)
      have hsne : sig (ω / 2) ≠ 0 := hσne hω2
      simp only [hm, hg, e1, hEval, hodd, one_mul]
      rw [inv_neg, mul_neg, mul_inv_cancel₀ hsne]
    refine hSopen.eqOn_of_deriv_eq hSconn ?_ (differentiableOn_const _) ?_ hx0mem ?_
    · exact fun z hz => (hmderiv z hz).differentiableAt.differentiableWithinAt
    · intro z hz; rw [(hmderiv z hz).deriv]; simp
    · simpa using hval0
  -- Turn the constancy into the pointwise relation on `S`, then extend by density.
  have hkey : Set.EqOn (fun z => sig (z + ω)) (fun z => -E z * sig z) S := by
    intro z hz
    have hmz : sig (z + ω) * (g z)⁻¹ = -1 := hmconst hz
    have hgn := hgne (hz : z ∉ L.lattice)
    rw [← div_eq_mul_inv] at hmz
    have := (div_eq_iff hgn).mp hmz
    change sig (z + ω) = -E z * sig z
    rw [this, hg]; ring
  have hcontf : Continuous (fun z => sig (z + ω)) :=
    hσdiff.continuous.comp (by fun_prop)
  have hcontg : Continuous (fun z => -E z * sig z) := by
    have hcE : Continuous E := by simp only [hE]; fun_prop
    exact (hcE.neg).mul hσdiff.continuous
  have heq := Continuous.ext_on (dense_compl_lattice L) hcontf hcontg hkey
  have := congrFun heq z
  simpa [hsig, hE] using this

/-- σ transformation law for `L_τ` in the `ω₁ = 1` direction:
`σ(z+1) = -exp(η₁·(z+1/2))·σ(z)`. -/
private lemma weierstrassSigma_add_one (τ : ℍ) (z : ℂ) :
    (Lτ τ).weierstrassSigma (z + 1) =
      -Complex.exp ((Lτ τ).eta₁ * (z + 1 / 2)) * (Lτ τ).weierstrassSigma z := by
  have h1 : (1 : ℂ) ∈ (Lτ τ).lattice := by
    have := (Lτ τ).ω₁_mem_lattice; rwa [Lτ_ω₁] at this
  have h2 : (1 : ℂ) / 2 ∉ (Lτ τ).lattice := by
    have := (Lτ τ).ω₁_div_two_notMem_lattice; rwa [Lτ_ω₁] at this
  have h3 : ∀ z ∉ (Lτ τ).lattice, (Lτ τ).weierstrassZeta (z + 1)
      = (Lτ τ).weierstrassZeta z + (Lτ τ).eta₁ := by
    intro z hz; have := (Lτ τ).weierstrassZeta_add_ω₁ z hz; rwa [Lτ_ω₁] at this
  exact weierstrassSigma_add_period (Lτ τ) 1 h1 h2 (Lτ τ).eta₁ h3 z

/-- σ transformation law for `L_τ` in the `ω₂ = τ` direction:
`σ(z+τ) = -exp(η₂·(z+τ/2))·σ(z)`. -/
private lemma weierstrassSigma_add_tau (τ : ℍ) (z : ℂ) :
    (Lτ τ).weierstrassSigma (z + (τ : ℂ)) =
      -Complex.exp ((Lτ τ).eta₂ * (z + (τ : ℂ) / 2)) * (Lτ τ).weierstrassSigma z := by
  have h1 : (τ : ℂ) ∈ (Lτ τ).lattice := by
    have := (Lτ τ).ω₂_mem_lattice; rwa [Lτ_ω₂] at this
  have h2 : (τ : ℂ) / 2 ∉ (Lτ τ).lattice := by
    have := (Lτ τ).ω₂_div_two_notMem_lattice; rwa [Lτ_ω₂] at this
  have h3 : ∀ z ∉ (Lτ τ).lattice, (Lτ τ).weierstrassZeta (z + (τ : ℂ))
      = (Lτ τ).weierstrassZeta z + (Lτ τ).eta₂ := by
    intro z hz; have := (Lτ τ).weierstrassZeta_add_ω₂ z hz; rwa [Lτ_ω₂] at this
  exact weierstrassSigma_add_period (Lτ τ) (τ : ℂ) h1 h2 (Lτ τ).eta₂ h3 z

/-! ### The basic q-product `Q(v) = ∏'_{n≥1} (1 - qⁿ·v)`

All the infinite products in the σ-product formula are values of this single entire function
`Q`, which satisfies the functional equation `Q(v) = (1 - q·v)·Q(q·v)`. -/

/-- The q-product `Q(v) = ∏'_{n≥1} (1 - qⁿ·v)`, written over `ℕ` with exponent `k+1`. -/
private noncomputable def qProd (q v : ℂ) : ℂ := ∏' k : ℕ, (1 - q ^ (k + 1) * v)

private lemma summable_qpow_mul {q : ℂ} (hq : ‖q‖ < 1) (v : ℂ) :
    Summable (fun k : ℕ => q ^ (k + 1) * v) := by
  have h : Summable (fun n : ℕ => q ^ n) := summable_geometric_of_norm_lt_one hq
  have h1 : Summable (fun k : ℕ => q ^ (k + 1)) := (summable_nat_add_iff 1).mpr h
  exact h1.mul_right v

private lemma multipliable_qProd_nat {q : ℂ} (hq : ‖q‖ < 1) (v : ℂ) :
    Multipliable (fun k : ℕ => 1 - q ^ (k + 1) * v) :=
  (Complex.multipliable_one_add_of_summable (summable_qpow_mul hq v).neg).congr
    (fun k => by ring)

/-- `Q(v) = ∏'_{n : ℕ+} (1 - qⁿ·v)` in the `ℕ+`-indexed form used in the statement. -/
private lemma qProd_eq_tprod_pnat (q v : ℂ) :
    qProd q v = ∏' n : ℕ+, (1 - q ^ (n : ℕ) * v) :=
  (tprod_pnat_eq_tprod_succ (f := fun n => 1 - q ^ n * v)).symm

/-- The functional equation `Q(v) = (1 - q·v)·Q(q·v)`. -/
private lemma qProd_functional {q : ℂ} (hq : ‖q‖ < 1) (v : ℂ) :
    qProd q v = (1 - q * v) * qProd q (q * v) := by
  have key : (∏' k : ℕ, (1 - q ^ (k + 1) * v))
      = (1 - q * v) * ∏' k : ℕ, (1 - q ^ (k + 1) * (q * v)) := by
    set f : ℕ → ℂ := fun k => 1 - q ^ (k + 1) * v with hf
    have hshift : Multipliable (fun n => f (n + 1)) :=
      (multipliable_qProd_nat hq (q * v)).congr (fun n => by simp only [hf]; ring)
    rw [tprod_eq_zero_mul' hshift]
    have e0 : f 0 = 1 - q * v := by simp only [hf]; norm_num
    rw [e0]
    congr 1
    exact tprod_congr (fun k => by simp only [hf]; ring)
  simpa only [qProd] using key

/-- `Q(v) ≠ 0` provided no factor vanishes. -/
private lemma qProd_ne_zero {q : ℂ} (hq : ‖q‖ < 1) {v : ℂ}
    (hv : ∀ k : ℕ, q ^ (k + 1) * v ≠ 1) : qProd q v ≠ 0 := by
  have key : (∏' k : ℕ, (1 + -(q ^ (k + 1) * v))) ≠ 0 := by
    refine tprod_one_add_ne_zero_of_summable (fun k => ?_) ?_
    · rw [show (1 : ℂ) + -(q ^ (k + 1) * v) = 1 - q ^ (k + 1) * v by ring, sub_ne_zero]
      exact fun h => hv k h.symm
    · simpa [norm_neg] using summable_norm_iff.mpr (summable_qpow_mul hq v)
  have hcongr : (∏' k : ℕ, (1 + -(q ^ (k + 1) * v))) = qProd q v := by
    simp only [qProd]; exact tprod_congr (fun k => by ring)
  rwa [hcongr] at key

/-- `Q` is entire (in the variable `v`). -/
private lemma differentiable_qProd {q : ℂ} (hq : ‖q‖ < 1) :
    Differentiable ℂ (fun v => qProd q v) := by
  rw [← differentiableOn_univ]
  have hLU : MultipliableLocallyUniformlyOn
      (fun (k : ℕ) (v : ℂ) => 1 - q ^ (k + 1) * v) Set.univ := by
    refine ⟨fun v => ∏' k : ℕ, (1 - q ^ (k + 1) * v), ?_⟩
    simp_rw [sub_eq_add_neg]
    apply hasProdLocallyUniformlyOn_of_forall_compact isOpen_univ
    intro K _ hcK
    rcases K.eq_empty_or_nonempty with hN | hN
    · simpa [hasProdUniformlyOn_iff_tendstoUniformlyOn, hN] using tendstoUniformlyOn_empty
    · obtain ⟨v₀, _, _, HB⟩ := hcK.exists_sSup_image_eq_and_ge hN
        (show ContinuousOn (fun v : ℂ => ‖v‖) K by fun_prop)
      refine (((summable_nat_add_iff 1).mpr
        (summable_geometric_of_lt_one (norm_nonneg q) hq)).mul_right ‖v₀‖)
        |>.hasProdUniformlyOn_nat_one_add
        hcK (.of_forall fun k x hx => ?_) (fun _ => by fun_prop)
      rw [norm_neg, norm_mul, norm_pow]
      exact mul_le_mul_of_nonneg_left (HB x hx) (by positivity)
  have := hLU.hasProdLocallyUniformlyOn.differentiableOn
    (.of_forall fun _ => by simpa [Finset.prod_fn] using
      DifferentiableOn.finsetProd (fun i _ => by fun_prop)) isOpen_univ
  exact this

private lemma norm_one_sub_qpow_ge {q : ℂ} (hq : ‖q‖ < 1) (k : ℕ) :
    1 - ‖q‖ ≤ ‖1 - q ^ (k + 1)‖ := by
  have h1 : ‖q ^ (k + 1)‖ ≤ ‖q‖ := by
    rw [norm_pow]
    calc ‖q‖ ^ (k + 1) ≤ ‖q‖ ^ 1 :=
          pow_le_pow_of_le_one (norm_nonneg q) hq.le (by omega)
      _ = ‖q‖ := pow_one _
  calc 1 - ‖q‖ ≤ ‖(1 : ℂ)‖ - ‖q ^ (k + 1)‖ := by rw [norm_one]; linarith
    _ ≤ ‖1 - q ^ (k + 1)‖ := norm_sub_norm_le _ _

private lemma one_sub_qpow_ne_zero {q : ℂ} (hq : ‖q‖ < 1) (k : ℕ) :
    (1 : ℂ) - q ^ (k + 1) ≠ 0 := by
  intro h
  have := norm_one_sub_qpow_ge hq k
  rw [h, norm_zero] at this; linarith

private lemma multipliable_qProd_inv_nat {q : ℂ} (hq : ‖q‖ < 1) :
    Multipliable (fun k : ℕ => (1 - q ^ (k + 1))⁻¹) := by
  have hpos : 0 < 1 - ‖q‖ := by linarith
  have hsum : Summable (fun k : ℕ => q ^ (k + 1) * (1 - q ^ (k + 1))⁻¹) := by
    refine Summable.of_norm_bounded
      (g := fun k : ℕ => ‖q‖ ^ (k + 1) * (1 - ‖q‖)⁻¹)
      (((summable_nat_add_iff 1).mpr
        (summable_geometric_of_lt_one (norm_nonneg q) hq)).mul_right (1 - ‖q‖)⁻¹) (fun k => ?_)
    rw [norm_mul, norm_pow, norm_inv]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have hden : 0 < ‖1 - q ^ (k + 1)‖ := lt_of_lt_of_le hpos (norm_one_sub_qpow_ge hq k)
    rw [inv_le_inv₀ hden hpos]
    exact norm_one_sub_qpow_ge hq k
  refine (Complex.multipliable_one_add_of_summable hsum).congr (fun k => ?_)
  have h := one_sub_qpow_ne_zero hq k
  field_simp; ring

/-- The combining identity: the combined product equals `Q(w)·Q(w⁻¹)/Q(1)²`. -/
private lemma combined_eq_Gfun {q : ℂ} (hq : ‖q‖ < 1) (w : ℂ) :
    (∏' k : ℕ, (1 - q ^ (k + 1) * w) * (1 - q ^ (k + 1) * w⁻¹) / (1 - q ^ (k + 1)) ^ 2)
      = qProd q w * qProd q w⁻¹ / qProd q 1 ^ 2 := by
  have hA := multipliable_qProd_nat hq w
  have hB := multipliable_qProd_nat hq w⁻¹
  have hD : Multipliable (fun k : ℕ => 1 - q ^ (k + 1)) :=
    (multipliable_qProd_nat hq 1).congr (fun k => by ring)
  have hDsq : Multipliable (fun k : ℕ => (1 - q ^ (k + 1)) ^ 2) :=
    (hD.mul hD).congr (fun k => (sq _).symm)
  have hDinv := multipliable_qProd_inv_nat hq
  have hEsq : Multipliable (fun k : ℕ => ((1 - q ^ (k + 1)) ^ 2)⁻¹) :=
    (hDinv.mul hDinv).congr (fun k => by rw [← mul_inv, ← sq])
  have hP : Multipliable (fun k : ℕ =>
      (1 - q ^ (k + 1) * w) * (1 - q ^ (k + 1) * w⁻¹) / (1 - q ^ (k + 1)) ^ 2) :=
    ((hA.mul hB).mul hEsq).congr (fun k => by rw [div_eq_mul_inv])
  have hqP1 : qProd q 1 = ∏' k : ℕ, (1 - q ^ (k + 1)) := by
    simp only [qProd]; exact tprod_congr (fun k => by ring)
  -- `P · ∏'D² = Q(w)·Q(w⁻¹)`
  have hcomb : (fun k : ℕ =>
        (1 - q ^ (k + 1) * w) * (1 - q ^ (k + 1) * w⁻¹) / (1 - q ^ (k + 1)) ^ 2
          * (1 - q ^ (k + 1)) ^ 2)
      = (fun k : ℕ => (1 - q ^ (k + 1) * w) * (1 - q ^ (k + 1) * w⁻¹)) :=
    funext (fun k => div_mul_cancel₀ _ (pow_ne_zero 2 (one_sub_qpow_ne_zero hq k)))
  have step : (∏' k : ℕ, (1 - q ^ (k + 1) * w) * (1 - q ^ (k + 1) * w⁻¹) / (1 - q ^ (k + 1)) ^ 2)
      * (∏' k : ℕ, (1 - q ^ (k + 1)) ^ 2) = qProd q w * qProd q w⁻¹ :=
    calc (∏' k : ℕ, (1 - q ^ (k + 1) * w) * (1 - q ^ (k + 1) * w⁻¹) / (1 - q ^ (k + 1)) ^ 2)
          * (∏' k : ℕ, (1 - q ^ (k + 1)) ^ 2)
        = ∏' k : ℕ, ((1 - q ^ (k + 1) * w) * (1 - q ^ (k + 1) * w⁻¹) / (1 - q ^ (k + 1)) ^ 2
            * (1 - q ^ (k + 1)) ^ 2) := (hP.tprod_mul hDsq).symm
      _ = ∏' k : ℕ, ((1 - q ^ (k + 1) * w) * (1 - q ^ (k + 1) * w⁻¹)) := by rw [hcomb]
      _ = qProd q w * qProd q w⁻¹ := by rw [hA.tprod_mul hB]; simp only [qProd]
  have hD2val : (∏' k : ℕ, (1 - q ^ (k + 1)) ^ 2) = qProd q 1 ^ 2 := by
    rw [hqP1, ← hD.tprod_pow 2]
  have hv1 : ∀ k : ℕ, q ^ (k + 1) * 1 ≠ 1 := by
    intro k; rw [mul_one]; intro h
    exact one_sub_qpow_ne_zero hq k (by rw [h]; ring)
  rw [hD2val] at step
  rw [eq_div_iff (pow_ne_zero 2 (qProd_ne_zero hq hv1))]
  exact step

/-! ### Milla's `φ` and `g` functions and their transformation laws (paper `satzphi`)

`φ(z) = exp(-η₁/2·z² + πiz)·σ(z)` and `g(z) = (q_z - 1)/(2πi)·Q(q_z)·Q(q_z⁻¹)/Q(1)²`
transform identically under `z ↦ z+1` (invariant) and `z ↦ z+τ` (factor `-e^{-2πiz}`, the
corrected sign of the paper's `satzphi`). -/

/-- The `Q(q_z)·Q(q_z⁻¹)/Q(1)²` factor of the product formula. -/
private noncomputable def Gfun (τ : ℍ) (z : ℂ) : ℂ :=
  qProd (q τ) (exp (2 * (π : ℂ) * I * z)) * qProd (q τ) (exp (2 * (π : ℂ) * I * z))⁻¹
    / qProd (q τ) 1 ^ 2

/-- Milla's `φ(z) = exp(-η₁/2·z² + πiz)·σ(z)`. -/
private noncomputable def φfun (τ : ℍ) (z : ℂ) : ℂ :=
  exp (-(Lτ τ).eta₁ / 2 * z ^ 2 + (π : ℂ) * I * z) * (Lτ τ).weierstrassSigma z

/-- Milla's `g(z) = (q_z - 1)/(2πi)·Gfun(z)`. -/
private noncomputable def gfun (τ : ℍ) (z : ℂ) : ℂ :=
  (exp (2 * (π : ℂ) * I * z) - 1) / (2 * (π : ℂ) * I) * Gfun τ z

private lemma exp_two_pi_I_add_one (z : ℂ) :
    exp (2 * (π : ℂ) * I * (z + 1)) = exp (2 * (π : ℂ) * I * z) := by
  rw [show 2 * (π : ℂ) * I * (z + 1) = 2 * (π : ℂ) * I * z + 2 * (π : ℂ) * I by ring,
    Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]

private lemma exp_two_pi_I_add_tau (τ : ℍ) (z : ℂ) :
    exp (2 * (π : ℂ) * I * (z + (τ : ℂ))) = q τ * exp (2 * (π : ℂ) * I * z) := by
  rw [show 2 * (π : ℂ) * I * (z + (τ : ℂ))
      = 2 * (π : ℂ) * I * z + 2 * (π : ℂ) * I * (τ : ℂ) by ring,
    Complex.exp_add, q_eq]
  ring

private lemma φfun_add_one (τ : ℍ) (z : ℂ) : φfun τ (z + 1) = φfun τ z := by
  have hexp : exp (-(Lτ τ).eta₁ / 2 * (z + 1) ^ 2 + (π : ℂ) * I * (z + 1))
      * -exp ((Lτ τ).eta₁ * (z + 1 / 2))
      = exp (-(Lτ τ).eta₁ / 2 * z ^ 2 + (π : ℂ) * I * z) := by
    rw [mul_neg, ← Complex.exp_add,
      show -(Lτ τ).eta₁ / 2 * (z + 1) ^ 2 + (π : ℂ) * I * (z + 1) + (Lτ τ).eta₁ * (z + 1 / 2)
        = (-(Lτ τ).eta₁ / 2 * z ^ 2 + (π : ℂ) * I * z) + (π : ℂ) * I by ring,
      Complex.exp_add, Complex.exp_pi_mul_I]
    ring
  simp only [φfun, weierstrassSigma_add_one]
  linear_combination (Lτ τ).weierstrassSigma z * hexp

private lemma φfun_add_tau (τ : ℍ) (z : ℂ) :
    φfun τ (z + (τ : ℂ)) = -exp (-(2 * (π : ℂ) * I * z)) * φfun τ z := by
  have hleg : (Lτ τ).eta₂ = (Lτ τ).eta₁ * (τ : ℂ) - 2 * (π : ℂ) * I := by
    linear_combination -(legendre_Lτ τ)
  have hexpeq : -(Lτ τ).eta₁ / 2 * (z + (τ : ℂ)) ^ 2 + (π : ℂ) * I * (z + (τ : ℂ))
      + (Lτ τ).eta₂ * (z + (τ : ℂ) / 2)
      = -(2 * (π : ℂ) * I * z) + (-(Lτ τ).eta₁ / 2 * z ^ 2 + (π : ℂ) * I * z) := by
    rw [hleg]; ring
  have hexp : exp (-(Lτ τ).eta₁ / 2 * (z + (τ : ℂ)) ^ 2 + (π : ℂ) * I * (z + (τ : ℂ)))
      * -exp ((Lτ τ).eta₂ * (z + (τ : ℂ) / 2))
      = -exp (-(2 * (π : ℂ) * I * z)) * exp (-(Lτ τ).eta₁ / 2 * z ^ 2 + (π : ℂ) * I * z) := by
    rw [mul_neg, ← Complex.exp_add, hexpeq, Complex.exp_add]; ring
  simp only [φfun, weierstrassSigma_add_tau]
  linear_combination (Lτ τ).weierstrassSigma z * hexp

private lemma gfun_add_one (τ : ℍ) (z : ℂ) : gfun τ (z + 1) = gfun τ z := by
  simp only [gfun, Gfun, exp_two_pi_I_add_one]

private lemma gfun_add_tau (τ : ℍ) (z : ℂ) :
    gfun τ (z + (τ : ℂ)) = -exp (-(2 * (π : ℂ) * I * z)) * gfun τ z := by
  have hqlt := norm_q_lt_one τ
  set w := exp (2 * (π : ℂ) * I * z) with hw
  have hwne : w ≠ 0 := Complex.exp_ne_zero _
  have hqne : q τ ≠ 0 := by rw [q_eq]; exact Complex.exp_ne_zero _
  have hP0 : qProd (q τ) 1 ≠ 0 := qProd_ne_zero hqlt (fun k => by
    rw [mul_one]; intro h; exact one_sub_qpow_ne_zero hqlt k (by rw [h]; ring))
  have h2pi : (2 * (π : ℂ) * I) ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero
  have hqz : exp (2 * (π : ℂ) * I * (z + (τ : ℂ))) = q τ * w := exp_two_pi_I_add_tau τ z
  have hnegexp : exp (-(2 * (π : ℂ) * I * z)) = w⁻¹ := by rw [Complex.exp_neg]
  have F1 : qProd (q τ) w = (1 - q τ * w) * qProd (q τ) (q τ * w) := qProd_functional hqlt w
  have F3 : qProd (q τ) (q τ * w)⁻¹ = (1 - w⁻¹) * qProd (q τ) w⁻¹ := by
    have h := qProd_functional hqlt ((q τ)⁻¹ * w⁻¹)
    rw [show q τ * ((q τ)⁻¹ * w⁻¹) = w⁻¹ from by
      rw [← mul_assoc, mul_inv_cancel₀ hqne, one_mul]] at h
    rw [mul_inv]; exact h
  simp only [gfun, Gfun, hqz, hnegexp]
  rw [F3, F1]
  field_simp
  ring

/-! ### Entireness and non-vanishing of `φ` and `g` -/

private lemma differentiable_Gfun (τ : ℍ) : Differentiable ℂ (Gfun τ) := by
  unfold Gfun
  apply Differentiable.div_const
  refine Differentiable.mul ((differentiable_qProd (norm_q_lt_one τ)).comp (by fun_prop)) ?_
  exact (differentiable_qProd (norm_q_lt_one τ)).comp
    ((by fun_prop : Differentiable ℂ (fun z : ℂ => exp (2 * (π : ℂ) * I * z))).inv
      (fun z => Complex.exp_ne_zero _))

private lemma differentiable_φfun (τ : ℍ) : Differentiable ℂ (φfun τ) := by
  unfold φfun
  exact ((by fun_prop : Differentiable ℂ
    (fun z : ℂ => -(Lτ τ).eta₁ / 2 * z ^ 2 + (π : ℂ) * I * z)).cexp).mul
    (Lτ τ).differentiable_weierstrassSigma

private lemma differentiable_gfun (τ : ℍ) : Differentiable ℂ (gfun τ) := by
  unfold gfun
  exact (by fun_prop : Differentiable ℂ
    (fun z : ℂ => (exp (2 * (π : ℂ) * I * z) - 1) / (2 * (π : ℂ) * I))).mul (differentiable_Gfun τ)

/-- If `z ∉ L_τ`, then `exp(2πi·(a·τ + z)) ≠ 1` for every integer `a`. -/
private lemma exp_add_lattice_ne_one (τ : ℍ) {z : ℂ} (hz : z ∉ (Lτ τ).lattice) (a : ℤ) :
    exp (2 * (π : ℂ) * I * ((a : ℂ) * (τ : ℂ) + z)) ≠ 1 := by
  intro h
  rw [Complex.exp_eq_one_iff] at h
  obtain ⟨n, hn⟩ := h
  have h2pi : (2 * (π : ℂ) * I) ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero
  have key : (a : ℂ) * (τ : ℂ) + z = (n : ℂ) := mul_left_cancel₀ h2pi (by linear_combination hn)
  apply hz
  rw [PeriodPair.mem_lattice]
  refine ⟨n, -a, ?_⟩
  simp only [Lτ_ω₁, Lτ_ω₂]
  push_cast
  linear_combination -key

private lemma qpow_qz_eq (τ : ℍ) (z : ℂ) (k : ℕ) :
    q τ ^ (k + 1) * exp (2 * (π : ℂ) * I * z)
      = exp (2 * (π : ℂ) * I * ((((k : ℤ) + 1 : ℤ) : ℂ) * (τ : ℂ) + z)) := by
  rw [q_eq, ← Complex.exp_nat_mul, ← Complex.exp_add]
  congr 1; push_cast; ring

private lemma qpow_qzinv_eq (τ : ℍ) (z : ℂ) (k : ℕ) :
    q τ ^ (k + 1) * (exp (2 * (π : ℂ) * I * z))⁻¹
      = exp (2 * (π : ℂ) * I * ((((k : ℤ) + 1 : ℤ) : ℂ) * (τ : ℂ) + (-z))) := by
  rw [q_eq, ← Complex.exp_nat_mul, ← Complex.exp_neg, ← Complex.exp_add]
  congr 1; push_cast; ring

private lemma qProd_qz_ne_zero (τ : ℍ) {z : ℂ} (hz : z ∉ (Lτ τ).lattice) :
    qProd (q τ) (exp (2 * (π : ℂ) * I * z)) ≠ 0 :=
  qProd_ne_zero (norm_q_lt_one τ) (fun k => by
    rw [qpow_qz_eq]; exact exp_add_lattice_ne_one τ hz ((k : ℤ) + 1))

private lemma qProd_qzinv_ne_zero (τ : ℍ) {z : ℂ} (hz : z ∉ (Lτ τ).lattice) :
    qProd (q τ) (exp (2 * (π : ℂ) * I * z))⁻¹ ≠ 0 := by
  have hnegz : -z ∉ (Lτ τ).lattice := fun hc => hz (by simpa using neg_mem hc)
  exact qProd_ne_zero (norm_q_lt_one τ) (fun k => by
    rw [qpow_qzinv_eq]; exact exp_add_lattice_ne_one τ hnegz ((k : ℤ) + 1))

private lemma qProd_one_ne_zero' (τ : ℍ) : qProd (q τ) 1 ≠ 0 :=
  qProd_ne_zero (norm_q_lt_one τ) (fun k => by
    rw [mul_one]; intro h
    exact one_sub_qpow_ne_zero (norm_q_lt_one τ) k (by rw [h]; ring))

private lemma Gfun_ne_zero (τ : ℍ) {z : ℂ} (hz : z ∉ (Lτ τ).lattice) : Gfun τ z ≠ 0 := by
  simp only [Gfun]
  exact div_ne_zero (mul_ne_zero (qProd_qz_ne_zero τ hz) (qProd_qzinv_ne_zero τ hz))
    (pow_ne_zero 2 (qProd_one_ne_zero' τ))

private lemma gfun_ne_zero (τ : ℍ) {z : ℂ} (hz : z ∉ (Lτ τ).lattice) : gfun τ z ≠ 0 := by
  have h2pi : (2 * (π : ℂ) * I) ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero
  have hqz1 : exp (2 * (π : ℂ) * I * z) - 1 ≠ 0 := by
    rw [sub_ne_zero]
    have := exp_add_lattice_ne_one τ hz 0
    simpa using this
  simp only [gfun]
  exact mul_ne_zero (div_ne_zero hqz1 h2pi) (Gfun_ne_zero τ hz)

private lemma φfun_ne_zero (τ : ℍ) {z : ℂ} (hz : z ∉ (Lτ τ).lattice) : φfun τ z ≠ 0 := by
  simp only [φfun]
  refine mul_ne_zero (Complex.exp_ne_zero _) ?_
  exact fun h => hz ((( Lτ τ).weierstrassSigma_eq_zero_iff z).mp h)

/-! ### `φ = g` via the first Liouville theorem, and the product formula -/

/-- `σ'(0) = 1` from the normalisation `σ(z) = z·∏(…)` with the product `→ 1` at `0`. -/
private lemma deriv_weierstrassSigma_zero (L : PeriodPair) : deriv L.weierstrassSigma 0 = 1 := by
  have hPdiff : Differentiable ℂ
      (fun z => ∏' l : {l : L.lattice // l ≠ 0}, PeriodPair.weierstrassSigmaTerm z (l.1 : ℂ)) := by
    rw [← differentiableOn_univ]
    refine (L.hasProdLocallyUniformly_weierstrassSigmaTerm.hasProdLocallyUniformlyOn
      |>.differentiableOn) (.of_forall fun _ => ?_) isOpen_univ
    simpa [Finset.prod_fn] using DifferentiableOn.finsetProd (fun i _ =>
      (by unfold PeriodPair.weierstrassSigmaTerm; fun_prop :
        DifferentiableOn ℂ (fun z => PeriodPair.weierstrassSigmaTerm z (i.1 : ℂ)) _))
  have hP0 : (∏' l : {l : L.lattice // l ≠ 0},
      PeriodPair.weierstrassSigmaTerm (0 : ℂ) (l.1 : ℂ)) = 1 := by
    rw [show (fun l : {l : L.lattice // l ≠ 0} =>
        PeriodPair.weierstrassSigmaTerm (0 : ℂ) (l.1 : ℂ)) = fun _ => (1 : ℂ) from
      funext (fun l => by simp [PeriodPair.weierstrassSigmaTerm]), tprod_one]
  have hd : HasDerivAt L.weierstrassSigma
      (1 * (∏' l : {l : L.lattice // l ≠ 0}, PeriodPair.weierstrassSigmaTerm (0 : ℂ) (l.1 : ℂ))
        + 0 * deriv (fun z => ∏' l : {l : L.lattice // l ≠ 0},
            PeriodPair.weierstrassSigmaTerm z (l.1 : ℂ)) 0) 0 :=
    (hasDerivAt_id (0 : ℂ)).mul (hPdiff 0).hasDerivAt
  rw [hd.deriv, hP0]; ring

private lemma Gfun_zero (τ : ℍ) : Gfun τ 0 = 1 := by
  simp only [Gfun, mul_zero, Complex.exp_zero, inv_one]
  rw [← sq, div_self (pow_ne_zero 2 (qProd_one_ne_zero' τ))]

private lemma gfun_hasDerivAt_zero (τ : ℍ) : HasDerivAt (gfun τ) 1 0 := by
  have h2pi : (2 * (π : ℂ) * I) ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero
  have h1 : HasDerivAt (fun z : ℂ => exp (2 * (π : ℂ) * I * z))
      (exp (2 * (π : ℂ) * I * 0) * (2 * (π : ℂ) * I)) 0 := by
    have hlin : HasDerivAt (fun z : ℂ => 2 * (π : ℂ) * I * z) (2 * (π : ℂ) * I) 0 := by
      simpa using (hasDerivAt_id (0 : ℂ)).const_mul (2 * (π : ℂ) * I)
    simpa [mul_comm] using hlin.cexp
  have hA : HasDerivAt (fun z : ℂ => (exp (2 * (π : ℂ) * I * z) - 1) / (2 * (π : ℂ) * I)) 1 0 := by
    have := (h1.sub_const 1).div_const (2 * (π : ℂ) * I)
    rwa [mul_zero, Complex.exp_zero, one_mul, div_self h2pi] at this
  have hmul := hA.mul (differentiable_Gfun τ 0).hasDerivAt
  have hval : (1 : ℂ) * Gfun τ 0 + (exp (2 * (π : ℂ) * I * 0) - 1) / (2 * (π : ℂ) * I)
      * deriv (Gfun τ) 0 = 1 := by
    rw [Gfun_zero]; simp
  rw [hval] at hmul
  exact hmul

private lemma gfun_order_zero (τ : ℍ) : meromorphicOrderAt (gfun τ) 0 = 1 := by
  have han : AnalyticAt ℂ (gfun τ) 0 := (differentiable_gfun τ).analyticAt 0
  have hval : gfun τ 0 = 0 := by
    simp only [gfun, mul_zero, Complex.exp_zero, sub_self, zero_div, zero_mul]
  have hderiv : deriv (gfun τ) 0 ≠ 0 := by rw [(gfun_hasDerivAt_zero τ).deriv]; exact one_ne_zero
  have hord : analyticOrderAt (gfun τ) 0 = 1 :=
    han.analyticOrderAt_eq_one_of_zero_deriv_ne_zero hval hderiv
  rw [han.meromorphicOrderAt_eq, hord]; rfl

private lemma phi_order (τ : ℍ) (z : ℂ) :
    meromorphicOrderAt (φfun τ) z = meromorphicOrderAt (Lτ τ).weierstrassSigma z := by
  have hexpan : AnalyticAt ℂ (fun z : ℂ => exp (-(Lτ τ).eta₁ / 2 * z ^ 2 + (π : ℂ) * I * z)) z :=
    Differentiable.analyticAt
      (by fun_prop : Differentiable ℂ
        (fun z : ℂ => -(Lτ τ).eta₁ / 2 * z ^ 2 + (π : ℂ) * I * z)).cexp z
  have hσ : MeromorphicAt (Lτ τ).weierstrassSigma z :=
    ((Lτ τ).differentiable_weierstrassSigma.analyticAt z).meromorphicAt
  have heq : φfun τ
      = (fun z : ℂ => exp (-(Lτ τ).eta₁ / 2 * z ^ 2 + (π : ℂ) * I * z)) * (Lτ τ).weierstrassSigma :=
    rfl
  rw [heq, meromorphicOrderAt_mul hexpan.meromorphicAt hσ, hexpan.meromorphicOrderAt_eq,
    hexpan.analyticOrderAt_eq_zero.mpr (Complex.exp_ne_zero _)]
  simp

/-- `H := φ/g` is periodic under the lattice `L_τ`. -/
private lemma hfun_add_lattice (τ : ℍ) (l : ℂ) (hl : l ∈ (Lτ τ).lattice) (z : ℂ) :
    φfun τ (z + l) / gfun τ (z + l) = φfun τ z / gfun τ z := by
  have hstep1 : ∀ w, φfun τ (w + 1) / gfun τ (w + 1) = φfun τ w / gfun τ w :=
    fun w => by rw [φfun_add_one, gfun_add_one]
  have hstep1' : ∀ w, φfun τ (w - 1) / gfun τ (w - 1) = φfun τ w / gfun τ w := fun w => by
    have := hstep1 (w - 1); rw [sub_add_cancel] at this; exact this.symm
  have hstepτ : ∀ w,
      φfun τ (w + (τ : ℂ)) / gfun τ (w + (τ : ℂ)) = φfun τ w / gfun τ w := fun w => by
    rw [φfun_add_tau, gfun_add_tau,
      mul_div_mul_left _ _ (neg_ne_zero.mpr (Complex.exp_ne_zero _))]
  have hstepτ' : ∀ w, φfun τ (w - (τ : ℂ)) / gfun τ (w - (τ : ℂ)) = φfun τ w / gfun τ w :=
    fun w => by have := hstepτ (w - (τ : ℂ)); rw [sub_add_cancel] at this; exact this.symm
  have h1 : ∀ (a : ℤ) (w : ℂ),
      φfun τ (w + (a : ℂ)) / gfun τ (w + (a : ℂ)) = φfun τ w / gfun τ w := by
    intro a
    induction a using Int.induction_on with
    | zero => intro w; simp
    | succ k ih =>
        intro w
        rw [show w + (((k : ℤ) + 1 : ℤ) : ℂ) = (w + ((k : ℤ) : ℂ)) + 1 by push_cast; ring,
          hstep1]
        simpa using ih w
    | pred k ih =>
        intro w
        rw [show w + ((-(k : ℤ) - 1 : ℤ) : ℂ) = (w + (-(k : ℤ) : ℂ)) - 1 by push_cast; ring,
          hstep1']
        simpa using ih w
  have hτ : ∀ (a : ℤ) (w : ℂ),
      φfun τ (w + (a : ℂ) * (τ : ℂ)) / gfun τ (w + (a : ℂ) * (τ : ℂ)) = φfun τ w / gfun τ w := by
    intro a
    induction a using Int.induction_on with
    | zero => intro w; simp
    | succ k ih =>
        intro w
        rw [show w + (((k : ℤ) + 1 : ℤ) : ℂ) * (τ : ℂ) = (w + ((k : ℤ) : ℂ) * (τ : ℂ)) + (τ : ℂ) by
          push_cast; ring, hstepτ]
        simpa using ih w
    | pred k ih =>
        intro w
        rw [show w + ((-(k : ℤ) - 1 : ℤ) : ℂ) * (τ : ℂ)
            = (w + (-(k : ℤ) : ℂ) * (τ : ℂ)) - (τ : ℂ) by
          push_cast; ring, hstepτ']
        simpa using ih w
  obtain ⟨m, n, hmn⟩ := PeriodPair.mem_lattice.mp hl
  simp only [Lτ_ω₁, Lτ_ω₂, mul_one] at hmn
  rw [← hmn, show z + ((m : ℂ) + (n : ℂ) * (τ : ℂ)) = (z + (n : ℂ) * (τ : ℂ)) + (m : ℂ) by ring,
    h1 m, hτ n]

/-- The σ product formula (paper `fouriersigma`): with `q = e^{2πiτ}` and
`q_z = e^{2πiz}`,

`σ(z; L_τ) = (2πi)⁻¹·e^{η₁z²/2}·(e^{πiz} - e^{-πiz})·∏_{n≥1} (1-qⁿq_z)(1-qⁿ/q_z)/(1-qⁿ)²`.

The half-integral powers `q_z^{±1/2}` of the paper are written branch-free as `e^{±πiz}`. -/
theorem weierstrassSigma_Lτ (τ : ℍ) (z : ℂ) :
    (Lτ τ).weierstrassSigma z =
      (2 * (π : ℂ) * I)⁻¹ * exp ((Lτ τ).eta₁ * z ^ 2 / 2) *
        (exp ((π : ℂ) * I * z) - exp (-((π : ℂ) * I * z))) *
        ∏' n : ℕ+,
          ((1 - q τ ^ (n : ℕ) * exp (2 * (π : ℂ) * I * z)) *
              (1 - q τ ^ (n : ℕ) / exp (2 * (π : ℂ) * I * z)) /
            (1 - q τ ^ (n : ℕ)) ^ 2) := by
  -- Set `H := φ/g`.
  set H : ℂ → ℂ := φfun τ / gfun τ with hH
  have hHmero : Meromorphic H := fun w =>
    (((differentiable_φfun τ).analyticAt w).meromorphicAt).div
      (((differentiable_gfun τ).analyticAt w).meromorphicAt)
  have hHell : (Lτ τ).IsEllipticWith H :=
    ⟨hHmero, fun w l => hfun_add_lattice τ (l : ℂ) l.2 w⟩
  -- `H` has order `0` everywhere.
  have hgmero : ∀ w, MeromorphicAt (gfun τ) w :=
    fun w => ((differentiable_gfun τ).analyticAt w).meromorphicAt
  have hφmero : ∀ w, MeromorphicAt (φfun τ) w :=
    fun w => ((differentiable_φfun τ).analyticAt w).meromorphicAt
  have hHord0 : meromorphicOrderAt H 0 = 0 := by
    rw [hH, meromorphicOrderAt_div (hφmero 0) (hgmero 0), phi_order τ 0,
      (Lτ τ).meromorphicOrderAt_weierstrassSigma 0 (Lτ τ).lattice.zero_mem, gfun_order_zero]
    simp
  have hHordAll : ∀ w, meromorphicOrderAt H w = 0 := by
    intro w
    by_cases hw : w ∈ (Lτ τ).lattice
    · -- periodicity of the order
      have hcomp : (H ∘ fun x => x + w) = H := by
        funext x
        have := hfun_add_lattice τ w hw x
        simpa [hH, Pi.div_apply] using this
      have hg : AnalyticAt ℂ (fun x : ℂ => x + w) 0 := by fun_prop
      have hg' : deriv (fun x : ℂ => x + w) 0 ≠ 0 := by
        rw [deriv_add_const, deriv_id'']; exact one_ne_zero
      have := meromorphicOrderAt_comp_of_deriv_ne_zero (f := H) hg hg'
      rw [hcomp] at this
      simp only [zero_add] at this
      rw [← this]; exact hHord0
    · rw [hH, meromorphicOrderAt_div (hφmero w) (hgmero w), phi_order τ w]
      have hσw : meromorphicOrderAt (Lτ τ).weierstrassSigma w = 0 := by
        have han : AnalyticAt ℂ (Lτ τ).weierstrassSigma w :=
          (Lτ τ).differentiable_weierstrassSigma.analyticAt w
        rw [han.meromorphicOrderAt_eq, han.analyticOrderAt_eq_zero.mpr
          (fun h => hw ((( Lτ τ).weierstrassSigma_eq_zero_iff w).mp h))]
        rfl
      have hgw : meromorphicOrderAt (gfun τ) w = 0 := by
        have han : AnalyticAt ℂ (gfun τ) w := (differentiable_gfun τ).analyticAt w
        rw [han.meromorphicOrderAt_eq, han.analyticOrderAt_eq_zero.mpr (gfun_ne_zero τ hw)]
        rfl
      rw [hσw, hgw]; simp
  -- Apply the workhorse against the constant `1`.
  have hone : (Lτ τ).IsEllipticWith (fun _ : ℂ => (1 : ℂ)) :=
    ⟨fun w => analyticAt_const.meromorphicAt, fun w l => rfl⟩
  have horder : ∀ w, meromorphicOrderAt H w = meromorphicOrderAt (fun _ : ℂ => (1 : ℂ)) w := by
    intro w
    rw [hHordAll w, analyticAt_const.meromorphicOrderAt_eq,
      analyticAt_const.analyticOrderAt_eq_zero.mpr (one_ne_zero)]
    rfl
  obtain ⟨c, hcne, hcodis⟩ := hHell.exists_const_mul_of_meromorphicOrderAt_eq hone horder
  -- Turn the codiscrete equality into `φ = c·g` everywhere.
  have hcodis' : {w : ℂ | H w = c} ∈ Filter.codiscrete ℂ := by
    have h : {w : ℂ | H w = (fun _ => c * (1 : ℂ)) w} ∈ Filter.codiscrete ℂ := hcodis
    simpa using h
  have hsub : {w : ℂ | H w = c} ⊆ {w : ℂ | φfun τ w = c * gfun τ w} := by
    intro w hw
    simp only [Set.mem_setOf_eq, hH, Pi.div_apply] at hw ⊢
    by_cases hg : gfun τ w = 0
    · exact absurd (by rw [hg, div_zero] at hw; exact hw.symm) hcne
    · exact (div_eq_iff hg).mp hw
  have hfreqset : {w : ℂ | φfun τ w = c * gfun τ w} ∈ Filter.codiscrete ℂ :=
    Filter.mem_of_superset hcodis' hsub
  have hfreq : ∃ᶠ w in nhdsWithin (0 : ℂ) {(0 : ℂ)}ᶜ, φfun τ w = c * gfun τ w := by
    have hm : ∀ᶠ w in nhdsWithin (0 : ℂ) {(0 : ℂ)}ᶜ, φfun τ w = c * gfun τ w := by
      rw [Filter.eventually_iff]
      have := mem_codiscrete.mp hfreqset (0 : ℂ)
      rwa [Filter.disjoint_principal_right, compl_compl] at this
    exact hm.frequently
  have hentire : φfun τ = fun w => c * gfun τ w := by
    have hana1 : AnalyticOnNhd ℂ (φfun τ) Set.univ :=
      fun w _ => (differentiable_φfun τ).analyticAt w
    have hana2 : AnalyticOnNhd ℂ (fun w => c * gfun τ w) Set.univ :=
      fun w _ => ((differentiable_gfun τ).const_mul c).analyticAt w
    funext w
    exact hana1.eqOn_of_preconnected_of_frequently_eq hana2 isPreconnected_univ
      (Set.mem_univ 0) hfreq (Set.mem_univ w)
  -- The constant is `1` (compare derivatives at `0`).
  have hc1 : c = 1 := by
    have hrhs : deriv (φfun τ) 0 = c := by
      rw [hentire, deriv_const_mul _ ((differentiable_gfun τ).differentiableAt),
        (gfun_hasDerivAt_zero τ).deriv, mul_one]
    have hvlin : HasDerivAt (fun z : ℂ => -(Lτ τ).eta₁ / 2 * z ^ 2 + (π : ℂ) * I * z)
        ((π : ℂ) * I) 0 := by
      have h1 : HasDerivAt (fun z : ℂ => -(Lτ τ).eta₁ / 2 * z ^ 2) 0 0 := by
        simpa using (hasDerivAt_pow 2 (0 : ℂ)).const_mul (-(Lτ τ).eta₁ / 2)
      have h2 : HasDerivAt (fun z : ℂ => (π : ℂ) * I * z) ((π : ℂ) * I) 0 := by
        simpa using (hasDerivAt_id (0 : ℂ)).const_mul ((π : ℂ) * I)
      have h3 := h1.add h2
      rw [zero_add] at h3
      exact h3
    have hE := hvlin.cexp
    have hσd : HasDerivAt (Lτ τ).weierstrassSigma 1 0 := by
      have := ((Lτ τ).differentiable_weierstrassSigma 0).hasDerivAt
      rwa [deriv_weierstrassSigma_zero] at this
    have hσ0 : (Lτ τ).weierstrassSigma 0 = 0 :=
      ((Lτ τ).weierstrassSigma_eq_zero_iff 0).mpr (Lτ τ).lattice.zero_mem
    have hφd : HasDerivAt (φfun τ) 1 0 := by
      have hm := hE.mul hσd
      have hEval : cexp (-(Lτ τ).eta₁ / 2 * (0 : ℂ) ^ 2 + (π : ℂ) * I * 0) = 1 := by
        rw [show -(Lτ τ).eta₁ / 2 * (0 : ℂ) ^ 2 + (π : ℂ) * I * 0 = 0 by ring, Complex.exp_zero]
      rw [hσ0, hEval, mul_zero, mul_one, zero_add] at hm
      exact hm
    rw [hφd.deriv] at hrhs
    exact hrhs.symm
  rw [hc1] at hentire
  have hφgz : (Lτ τ).weierstrassSigma z
      = exp (-(-(Lτ τ).eta₁ / 2 * z ^ 2 + (π : ℂ) * I * z)) * gfun τ z := by
    have h := congrFun hentire z
    rw [one_mul, φfun] at h
    rw [← h, ← mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, one_mul]
  -- Convert the target product into `Gfun`.
  have hGprod : (∏' n : ℕ+,
      ((1 - q τ ^ (n : ℕ) * exp (2 * (π : ℂ) * I * z)) *
          (1 - q τ ^ (n : ℕ) / exp (2 * (π : ℂ) * I * z)) /
        (1 - q τ ^ (n : ℕ)) ^ 2)) = Gfun τ z := by
    rw [Gfun, ← combined_eq_Gfun (norm_q_lt_one τ) (exp (2 * (π : ℂ) * I * z)),
      tprod_pnat_eq_tprod_succ (f := fun k => (1 - q τ ^ k * exp (2 * (π : ℂ) * I * z))
        * (1 - q τ ^ k / exp (2 * (π : ℂ) * I * z)) / (1 - q τ ^ k) ^ 2)]
    exact tprod_congr (fun k => by rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv])
  rw [hGprod, hφgz, gfun]
  have hexpv : exp (-(-(Lτ τ).eta₁ / 2 * z ^ 2 + (π : ℂ) * I * z))
      = exp ((Lτ τ).eta₁ * z ^ 2 / 2) * exp (-((π : ℂ) * I * z)) := by
    rw [← Complex.exp_add, show (Lτ τ).eta₁ * z ^ 2 / 2 + -((π : ℂ) * I * z)
      = -(-(Lτ τ).eta₁ / 2 * z ^ 2 + (π : ℂ) * I * z) by ring]
  have hexpm : exp (-((π : ℂ) * I * z)) * (exp (2 * (π : ℂ) * I * z) - 1)
      = exp ((π : ℂ) * I * z) - exp (-((π : ℂ) * I * z)) := by
    rw [mul_sub, mul_one, ← Complex.exp_add,
      show -((π : ℂ) * I * z) + 2 * (π : ℂ) * I * z = (π : ℂ) * I * z by ring]
  rw [hexpv, ← mul_assoc]
  rw [show exp ((Lτ τ).eta₁ * z ^ 2 / 2) * exp (-((π : ℂ) * I * z))
        * ((exp (2 * (π : ℂ) * I * z) - 1) / (2 * (π : ℂ) * I))
      = exp ((Lτ τ).eta₁ * z ^ 2 / 2)
        * (exp (-((π : ℂ) * I * z)) * (exp (2 * (π : ℂ) * I * z) - 1)) / (2 * (π : ℂ) * I) by ring,
    hexpm]
  ring

end Chudnovsky
