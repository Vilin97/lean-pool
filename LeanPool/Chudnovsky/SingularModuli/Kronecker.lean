/-
Copyright (c) 2026 Xuanji Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuanji Li
-/

import LeanPool.Chudnovsky.SingularModuli.ModularPolynomialZ

/-!
# Kronecker's unit-leading-coefficient lemma for the diagonal modular polynomial (Phase C, B7)

This file discharges the gated hypothesis `hlead` of
`ModularPolynomialZ.isIntegral_of_kronecker`: for a prime `m ≥ 2` and **any**
`PhiZ : ℤ[Y][X]` satisfying the keystone identity `orbitPoly m τ = Φ_m(X, j τ)`, the diagonal
`G_m := diagPhiZ PhiZ = Φ_m(X, X)` has

* `natDegree = 2·m`  (`diagPhiZ_natDegree_eq`), and
* `leadingCoeff = -1`  (`diagPhiZ_leadingCoeff_eq_neg_one`), hence `±1`
  (`diagPhiZ_leadingCoeff_eq`).

## The argument — pure limit calculus at the cusp `Im τ → ∞`

All series manipulation is already packaged upstream; here we only take limits along
`UpperHalfPlane.atImInfty`.

The single analytic input is `jq_tendsto_one : j τ · q τ → 1`, proved from the fact that the
`q`-expansion of `j·q` extends analytically across the cusp with value the constant coefficient
`jqInt.coeff 0 = 1` (`UpperHalfPlane.eq_cuspFunction` + continuity of `cuspFunction`). Composing
with the isogenies `Acol`/`AInf` (which push towards the cusp, `tendsto_smul_atImInfty`) and using
`q = wᵐ`, `q(Acol • τ) = ζᵇ·w`, `q(AInf • τ) = w^{m²}` gives, as `Im τ → ∞`:

* each `some b` factor `(j τ − f_b τ)·q → 1`   (`some_factor_tendsto_one`);
* the `∞` factor `(j τ − f_∞ τ)·qᵐ → −1`       (`none_factor_tendsto_neg_one`);

so the orbit product `D(τ)·q^{2m} = G_m(j τ)·q^{2m} → 1^m·(−1) = −1`
(`orbit_prod_tendsto_neg_one`). Matching this against the polynomial expansion
`G_m(j τ)·q^{d} → leadingCoeff` (`eval2_qpow_tendsto`, using `(j·q)ʳ·q^{d−r} → 0` for `d > r`),
uniqueness of limits (`atImInfty.NeBot`) forces `d = 2m` and `leadingCoeff = −1`.

Everything downstream of `±1` is `isIntegral_of_kronecker`; `isIntegral_j_of_cm` composes the two
so that only the CM relation `j τ = f m i τ` and the defining identity `hPhi` are needed.
-/

noncomputable section

namespace Chudnovsky

open UpperHalfPlane Complex ModularForm EisensteinSeries Polynomial Finset
open scoped Real ComplexOrder Manifold MatrixGroups

open Filter Topology

variable {m : ℕ}

/-! ### The cusp limit `j·q → 1` -/

/-- `q τ → 0` as `Im τ → ∞`. -/
lemma q_tendsto_zero : Tendsto (fun τ : ℍ ↦ q τ) atImInfty (nhds 0) := by
  simpa [q] using qParam_tendsto_atImInfty one_pos

/-- `j·q` is bounded at the cusp (it tends to `1`); reconstructed from
`discriminant = q · ∏ (1 − qⁿ)²⁴` and `j·Δ = E₄³`. -/
lemma isBoundedAtImInfty_jq' : IsBoundedAtImInfty (fun τ : ℍ ↦ j τ * q τ) := by
  have hrec : (fun τ : ℍ ↦ j τ * q τ)
      = ⇑E₄ * (⇑E₄ * (⇑E₄ * fun τ : ℍ ↦ (∏' n : ℕ, (1 - eta_q n ↑τ) ^ 24)⁻¹)) := by
    funext τ
    simp only [Pi.mul_apply]
    have hΔ : discriminant τ = q τ * ∏' n : ℕ, (1 - eta_q n ↑τ) ^ 24 := discriminant_eq_q_prod τ
    have hP0 : (∏' n : ℕ, (1 - eta_q n ↑τ) ^ 24) ≠ 0 := fun h0 ↦
      discriminant_ne_zero τ (by rw [hΔ, h0, mul_zero])
    have hjq : j τ * q τ = E₄ τ ^ 3 * (∏' n : ℕ, (1 - eta_q n ↑τ) ^ 24)⁻¹ := by
      rw [eq_mul_inv_iff_mul_eq₀ hP0, mul_assoc, ← hΔ]
      exact j_mul_discriminant τ
    rw [hjq]; ring
  rw [hrec]
  have hE : IsBoundedAtImInfty ⇑E₄ := ModularFormClass.bdd_at_infty E₄
  have hPinv : Tendsto (fun τ : ℍ ↦ (∏' n : ℕ, (1 - eta_q n ↑τ) ^ 24)⁻¹) atImInfty (nhds 1) := by
    simpa using tendsto_atImInfty_tprod_one_sub_eta_q_pow.inv₀ one_ne_zero
  have hPb : IsBoundedAtImInfty (fun τ : ℍ ↦ (∏' n : ℕ, (1 - eta_q n ↑τ) ^ 24)⁻¹) :=
    hPinv.isBigO_one ℝ
  exact Filter.BoundedAtFilter.mul hE (Filter.BoundedAtFilter.mul hE
    (Filter.BoundedAtFilter.mul hE hPb))

/-- **The single analytic input.** `j τ · q τ → 1` as `Im τ → ∞`: the `q`-expansion of `j·q`
extends analytically across the cusp with value its constant coefficient `jqInt.coeff 0 = 1`. -/
lemma jq_tendsto_one : Tendsto (fun τ : ℍ ↦ j τ * q τ) atImInfty (nhds 1) := by
  have hper : Function.Periodic ((fun τ : ℍ ↦ j τ * q τ) ∘ ofComplex) 1 :=
    periodic_comp_ofComplex_of_vadd (fun τ ↦ by rw [j_vadd_one, q_vadd_one])
  have han : AnalyticAt ℂ (cuspFunction 1 (fun τ : ℍ ↦ j τ * q τ)) 0 :=
    analyticAt_cuspFunction_zero one_pos hper mdifferentiable_j_mul_q isBoundedAtImInfty_jq'
  have hcts : ContinuousAt (cuspFunction 1 (fun τ : ℍ ↦ j τ * q τ)) 0 := han.continuousAt
  have hcusp0 : cuspFunction 1 (fun τ : ℍ ↦ j τ * q τ) 0 = 1 := by
    have h := j_mul_q_qExpansion_coeff_zero
    rw [qExpansion_coeff] at h
    simpa using h
  have hcomp : Tendsto (fun τ : ℍ ↦ cuspFunction 1 (fun ρ : ℍ ↦ j ρ * q ρ) (q τ)) atImInfty
      (nhds (cuspFunction 1 (fun τ : ℍ ↦ j τ * q τ) 0)) := hcts.tendsto.comp q_tendsto_zero
  rw [hcusp0] at hcomp
  refine hcomp.congr (fun τ ↦ ?_)
  exact eq_cuspFunction τ one_ne_zero hper

/-- `j·q` composed with an isogeny `A` of lower-left entry `0` (which pushes towards `i∞`) still
tends to `1`. -/
lemma jq_comp_tendsto_one {A : GL (Fin 2) ℝ} (hA : (A : Matrix (Fin 2) (Fin 2) ℝ) 1 0 = 0) :
    Tendsto (fun τ : ℍ ↦ j (A • τ) * q (A • τ)) atImInfty (nhds 1) :=
  jq_tendsto_one.comp (tendsto_smul_atImInfty hA)

/-- The base variable `w = wParam m τ → 0` at the cusp (it is `q` of the coset point at `b = 0`). -/
lemma wParam_tendsto_zero [NeZero m] :
    Tendsto (fun τ : ℍ ↦ wParam m τ) atImInfty (nhds 0) := by
  have h : Tendsto (fun τ : ℍ ↦ q (Acol m (0 : ℤ) • τ)) atImInfty (nhds 0) :=
    q_tendsto_zero.comp (tendsto_smul_atImInfty (g := Acol m (0 : ℤ)) (by simp [val_Acol]))
  refine h.congr (fun τ ↦ ?_)
  rw [q_Acol_smul]; simp

/-! ### Per-factor limits of the orbit product -/

/-- Each `some b` factor of the orbit product, times `q`, tends to `1`. -/
lemma some_factor_tendsto_one [Fact m.Prime] (b : ZMod m) :
    Tendsto (fun τ : ℍ ↦ (j τ - f m (some b) τ) * q τ) atImInfty (nhds 1) := by
  haveI : NeZero m := ⟨(Fact.out : m.Prime).ne_zero⟩
  have hm2 : 2 ≤ m := (Fact.out : m.Prime).two_le
  -- `f_b · q → 0`
  have hfac : Tendsto (fun τ : ℍ ↦ f m (some b) τ * q τ) atImInfty (nhds 0) := by
    have hkey : ∀ τ : ℍ, f m (some b) τ * q τ
        = (j (Acol m (b.val : ℤ) • τ) * q (Acol m (b.val : ℤ) • τ))
          * (zetaM m ^ (-(b.val : ℤ)) * wParam m τ ^ (m - 1)) := by
      intro τ
      have hz : zetaM m ≠ 0 := zetaM_ne_zero
      rw [f_some, q_Acol_smul (m := m), ← wParam_pow_m (m := m) τ]
      have hzz : zetaM m ^ (b.val : ℤ) * zetaM m ^ (-(b.val : ℤ)) = 1 := by
        rw [← zpow_add₀ hz, add_neg_cancel, zpow_zero]
      have hww : wParam m τ * wParam m τ ^ (m - 1) = wParam m τ ^ m := by
        rw [← pow_succ', Nat.sub_add_cancel (show 1 ≤ m by omega)]
      rw [show (j (Acol m (b.val : ℤ) • τ) * (zetaM m ^ (b.val : ℤ) * wParam m τ))
            * (zetaM m ^ (-(b.val : ℤ)) * wParam m τ ^ (m - 1))
          = j (Acol m (b.val : ℤ) • τ) * (zetaM m ^ (b.val : ℤ) * zetaM m ^ (-(b.val : ℤ)))
            * (wParam m τ * wParam m τ ^ (m - 1)) from by ring, hzz, hww, mul_one]
    have hA : Tendsto (fun τ : ℍ ↦ j (Acol m (b.val : ℤ) • τ) * q (Acol m (b.val : ℤ) • τ))
        atImInfty (nhds 1) :=
      jq_comp_tendsto_one (A := Acol m (b.val : ℤ)) (by simp [val_Acol])
    have hB : Tendsto (fun τ : ℍ ↦ zetaM m ^ (-(b.val : ℤ)) * wParam m τ ^ (m - 1)) atImInfty
        (nhds 0) := by
      have hw : Tendsto (fun τ : ℍ ↦ wParam m τ ^ (m - 1)) atImInfty (nhds 0) := by
        simpa [zero_pow (show m - 1 ≠ 0 by omega)] using wParam_tendsto_zero.pow (m - 1)
      simpa using tendsto_const_nhds.mul hw
    have hmul : Tendsto (fun τ : ℍ ↦ (j (Acol m (b.val : ℤ) • τ) * q (Acol m (b.val : ℤ) • τ))
        * (zetaM m ^ (-(b.val : ℤ)) * wParam m τ ^ (m - 1))) atImInfty (nhds 0) := by
      simpa using hA.mul hB
    exact hmul.congr (fun τ ↦ (hkey τ).symm)
  have hsub : Tendsto (fun τ : ℍ ↦ j τ * q τ - f m (some b) τ * q τ) atImInfty (nhds (1 - 0)) :=
    jq_tendsto_one.sub hfac
  rw [sub_zero] at hsub
  exact hsub.congr (fun τ ↦ (sub_mul (j τ) (f m (some b) τ) (q τ)).symm)

/-- The `∞` factor of the orbit product, times `qᵐ`, tends to `−1`. -/
lemma none_factor_tendsto_neg_one [Fact m.Prime] :
    Tendsto (fun τ : ℍ ↦ (j τ - f m none τ) * q τ ^ m) atImInfty (nhds (-1)) := by
  haveI : NeZero m := ⟨(Fact.out : m.Prime).ne_zero⟩
  have hm2 : 2 ≤ m := (Fact.out : m.Prime).two_le
  -- `j · qᵐ → 0`
  have hjqm : Tendsto (fun τ : ℍ ↦ j τ * q τ ^ m) atImInfty (nhds 0) := by
    have h1 : Tendsto (fun τ : ℍ ↦ (j τ * q τ) * q τ ^ (m - 1)) atImInfty (nhds (1 * 0)) :=
      jq_tendsto_one.mul (by
        simpa [zero_pow (show m - 1 ≠ 0 by omega)] using q_tendsto_zero.pow (m - 1))
    rw [mul_zero] at h1
    refine h1.congr (fun τ ↦ ?_)
    rw [mul_assoc, ← pow_succ', Nat.sub_add_cancel (show 1 ≤ m by omega)]
  -- `f_∞ · qᵐ = j(m·τ) · q(m·τ) → 1`
  have hfnone : Tendsto (fun τ : ℍ ↦ f m none τ * q τ ^ m) atImInfty (nhds 1) := by
    have hAI : Tendsto (fun τ : ℍ ↦ j (AInf m • τ) * q (AInf m • τ)) atImInfty (nhds 1) :=
      jq_comp_tendsto_one (A := AInf m) (by simp [val_AInf])
    refine hAI.congr (fun τ ↦ ?_)
    rw [f_none, q_AInf_smul (m := m), ← wParam_pow_m (m := m) τ, ← pow_mul, pow_two]
  have hsub : Tendsto (fun τ : ℍ ↦ j τ * q τ ^ m - f m none τ * q τ ^ m) atImInfty (nhds (0 - 1)) :=
    hjqm.sub hfnone
  rw [zero_sub] at hsub
  exact hsub.congr (fun τ ↦ (sub_mul (j τ) (f m none τ) (q τ ^ m)).symm)

/-- **The orbit product limit.** `D(τ)·q^{2m} = (∏_i (j τ − f_i τ))·q^{2m} → −1`. -/
lemma orbit_prod_tendsto_neg_one [Fact m.Prime] :
    Tendsto (fun τ : ℍ ↦ (∏ i : Option (ZMod m), (j τ - f m i τ)) * q τ ^ (2 * m)) atImInfty
      (nhds (-1)) := by
  haveI : NeZero m := ⟨(Fact.out : m.Prime).ne_zero⟩
  have hprod : Tendsto (fun τ : ℍ ↦ ∏ b : ZMod m, ((j τ - f m (some b) τ) * q τ)) atImInfty
      (nhds 1) := by
    have h := tendsto_finsetProd (Finset.univ : Finset (ZMod m))
      (f := fun b (τ : ℍ) ↦ (j τ - f m (some b) τ) * q τ) (a := fun _ ↦ (1 : ℂ))
      (fun b _ ↦ some_factor_tendsto_one b)
    simpa using h
  have hcombined : Tendsto (fun τ : ℍ ↦ ((j τ - f m none τ) * q τ ^ m)
      * ∏ b : ZMod m, ((j τ - f m (some b) τ) * q τ)) atImInfty (nhds (-1)) := by
    simpa using none_factor_tendsto_neg_one.mul hprod
  refine hcombined.congr (fun τ ↦ ?_)
  rw [Fintype.prod_option, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, ZMod.card,
    show 2 * m = m + m from two_mul m, pow_add]
  ring

/-! ### The polynomial side -/

/-- A single monomial term `c·(j τ)ʳ·qᵈ` tends to `c` if `r = d` and to `0` if `r < d`
(with `r ≤ d`), since it equals `c·(j·q)ʳ·q^{d−r}` and `j·q → 1`, `q → 0`. -/
lemma term_tendsto (c : ℂ) (r d : ℕ) (hrd : r ≤ d) :
    Tendsto (fun τ : ℍ ↦ c * (j τ) ^ r * q τ ^ d) atImInfty (nhds (if r = d then c else 0)) := by
  have hfun : ∀ τ : ℍ, c * (j τ) ^ r * q τ ^ d = c * (j τ * q τ) ^ r * q τ ^ (d - r) := by
    intro τ
    have hq : q τ ^ d = q τ ^ r * q τ ^ (d - r) := by
      rw [← pow_add, Nat.add_sub_cancel' hrd]
    rw [hq, mul_pow]; ring
  simp_rw [hfun]
  by_cases h : r = d
  · subst h
    simp only [Nat.sub_self, pow_zero, mul_one, if_true]
    simpa using tendsto_const_nhds.mul (jq_tendsto_one.pow r)
  · rw [if_neg h]
    have hqdr : Tendsto (fun τ : ℍ ↦ q τ ^ (d - r)) atImInfty (nhds 0) := by
      simpa [zero_pow (show d - r ≠ 0 by omega)] using q_tendsto_zero.pow (d - r)
    have h2 : Tendsto (fun τ : ℍ ↦ c * (j τ * q τ) ^ r) atImInfty (nhds c) := by
      simpa using tendsto_const_nhds.mul (jq_tendsto_one.pow r)
    simpa using h2.mul hqdr

/-- `G(j τ)·q^{natDegree G} → (leadingCoeff G : ℂ)`: matching the polynomial against its top
`q`-power isolates the leading coefficient. -/
lemma eval2_qpow_tendsto (G : Polynomial ℤ) :
    Tendsto (fun τ : ℍ ↦ G.eval₂ (Int.castRingHom ℂ) (j τ) * q τ ^ G.natDegree) atImInfty
      (nhds ((G.leadingCoeff : ℤ) : ℂ)) := by
  have hfun : ∀ τ : ℍ, G.eval₂ (Int.castRingHom ℂ) (j τ) * q τ ^ G.natDegree
      = ∑ r ∈ Finset.range (G.natDegree + 1),
        ((G.coeff r : ℤ) : ℂ) * (j τ) ^ r * q τ ^ G.natDegree := by
    intro τ
    rw [eval₂_eq_sum_range, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun r _ ↦ ?_)
    rw [eq_intCast (Int.castRingHom ℂ) (G.coeff r)]
  simp_rw [hfun]
  have hlim : Tendsto (fun τ : ℍ ↦ ∑ r ∈ Finset.range (G.natDegree + 1),
        ((G.coeff r : ℤ) : ℂ) * (j τ) ^ r * q τ ^ G.natDegree) atImInfty
      (nhds (∑ r ∈ Finset.range (G.natDegree + 1),
        if r = G.natDegree then ((G.coeff r : ℤ) : ℂ) else 0)) :=
    tendsto_finsetSum _ (fun r hr ↦
      term_tendsto _ r G.natDegree (by simp only [Finset.mem_range] at hr; omega))
  have hsum : (∑ r ∈ Finset.range (G.natDegree + 1),
        if r = G.natDegree then ((G.coeff r : ℤ) : ℂ) else 0) = ((G.leadingCoeff : ℤ) : ℂ) := by
    rw [Finset.sum_ite_eq' (Finset.range (G.natDegree + 1)) G.natDegree
      (fun r ↦ ((G.coeff r : ℤ) : ℂ))]
    simp only [Finset.mem_range, Nat.lt_succ_self, if_true]
    rfl
  rw [hsum] at hlim
  exact hlim

/-! ### Kronecker's lemma -/

/-- **(B7) Kronecker, sharp form.** For prime `m` and any `PhiZ` with the keystone identity, the
diagonal `G_m = diagPhiZ PhiZ` has `natDegree = 2·m` and `leadingCoeff = −1`. -/
theorem diagPhiZ_natDegree_and_leadingCoeff [Fact m.Prime]
    {PhiZ : Polynomial (Polynomial ℤ)}
    (hPhi : ∀ τ : ℍ, orbitPoly m τ = specializeZ (j τ) PhiZ) :
    (diagPhiZ PhiZ).natDegree = 2 * m ∧ (diagPhiZ PhiZ).leadingCoeff = -1 := by
  haveI : NeZero m := ⟨(Fact.out : m.Prime).ne_zero⟩
  set G := diagPhiZ PhiZ with hGdef
  -- `G(j τ) = ∏_i (j τ − f_i τ)`
  have hD : ∀ τ : ℍ, G.eval₂ (Int.castRingHom ℂ) (j τ) = ∏ i : Option (ZMod m), (j τ - f m i τ) :=
    fun τ ↦ diagPhiZ_map_eval hPhi τ
  -- limit A : `G(j τ)·q^{2m} → −1`
  have hA : Tendsto (fun τ : ℍ ↦ G.eval₂ (Int.castRingHom ℂ) (j τ) * q τ ^ (2 * m)) atImInfty
      (nhds (-1)) :=
    orbit_prod_tendsto_neg_one.congr (fun τ ↦ by rw [hD τ])
  -- limit B : `G(j τ)·q^{natDegree} → leadingCoeff`
  have hB := eval2_qpow_tendsto G
  rcases lt_trichotomy G.natDegree (2 * m) with hlt | heq | hgt
  · -- `natDegree < 2m` : the `2m`-limit would be `leadingCoeff·0 = 0 ≠ −1`
    have hshift : Tendsto (fun τ : ℍ ↦ (G.eval₂ (Int.castRingHom ℂ) (j τ) * q τ ^ G.natDegree)
        * q τ ^ (2 * m - G.natDegree)) atImInfty (nhds (((G.leadingCoeff : ℤ) : ℂ) * 0)) :=
      hB.mul (by
        simpa [zero_pow (show 2 * m - G.natDegree ≠ 0 by omega)]
          using q_tendsto_zero.pow (2 * m - G.natDegree))
    rw [mul_zero] at hshift
    have h0 : Tendsto (fun τ : ℍ ↦ G.eval₂ (Int.castRingHom ℂ) (j τ) * q τ ^ (2 * m)) atImInfty
        (nhds 0) :=
      hshift.congr (fun τ ↦ by rw [mul_assoc, ← pow_add, Nat.add_sub_cancel' hlt.le])
    exact absurd (tendsto_nhds_unique h0 hA) (by norm_num)
  · -- `natDegree = 2m` : the two limits agree, so `leadingCoeff = −1`
    have hBeq : Tendsto (fun τ : ℍ ↦ G.eval₂ (Int.castRingHom ℂ) (j τ) * q τ ^ (2 * m)) atImInfty
        (nhds ((G.leadingCoeff : ℤ) : ℂ)) := by rw [← heq]; exact hB
    have hlc : ((G.leadingCoeff : ℤ) : ℂ) = -1 := tendsto_nhds_unique hBeq hA
    exact ⟨heq, by exact_mod_cast hlc⟩
  · -- `natDegree > 2m` : the `natDegree`-limit would be `−1·0 = 0 = leadingCoeff`, forcing `G = 0`
    have hshift : Tendsto (fun τ : ℍ ↦ (G.eval₂ (Int.castRingHom ℂ) (j τ) * q τ ^ (2 * m))
        * q τ ^ (G.natDegree - 2 * m)) atImInfty (nhds ((-1 : ℂ) * 0)) :=
      hA.mul (by
        simpa [zero_pow (show G.natDegree - 2 * m ≠ 0 by omega)]
          using q_tendsto_zero.pow (G.natDegree - 2 * m))
    rw [mul_zero] at hshift
    have h0 : Tendsto (fun τ : ℍ ↦ G.eval₂ (Int.castRingHom ℂ) (j τ) * q τ ^ G.natDegree) atImInfty
        (nhds 0) :=
      hshift.congr (fun τ ↦ by rw [mul_assoc, ← pow_add, Nat.add_sub_cancel' hgt.le])
    have hlc0 : ((G.leadingCoeff : ℤ) : ℂ) = 0 := tendsto_nhds_unique hB h0
    have hlcZ : G.leadingCoeff = 0 := by exact_mod_cast hlc0
    rw [Polynomial.leadingCoeff_eq_zero] at hlcZ
    -- `G = 0` makes the `2m`-limit `0 ≠ −1`
    have hA0 : Tendsto (fun τ : ℍ ↦ G.eval₂ (Int.castRingHom ℂ) (j τ) * q τ ^ (2 * m)) atImInfty
        (nhds 0) := by
      have hz : (fun τ : ℍ ↦ G.eval₂ (Int.castRingHom ℂ) (j τ) * q τ ^ (2 * m))
          = fun _ ↦ (0 : ℂ) := by funext τ; rw [hlcZ]; simp
      rw [hz]; exact tendsto_const_nhds
    exact absurd (tendsto_nhds_unique hA0 hA) (by norm_num)

/-- **`natDegree (diagPhiZ PhiZ) = 2·m`.** -/
theorem diagPhiZ_natDegree_eq [Fact m.Prime] {PhiZ : Polynomial (Polynomial ℤ)}
    (hPhi : ∀ τ : ℍ, orbitPoly m τ = specializeZ (j τ) PhiZ) :
    (diagPhiZ PhiZ).natDegree = 2 * m :=
  (diagPhiZ_natDegree_and_leadingCoeff hPhi).1

/-- **`leadingCoeff (diagPhiZ PhiZ) = −1`** (the sharp form of Kronecker's lemma). -/
theorem diagPhiZ_leadingCoeff_eq_neg_one [Fact m.Prime] {PhiZ : Polynomial (Polynomial ℤ)}
    (hPhi : ∀ τ : ℍ, orbitPoly m τ = specializeZ (j τ) PhiZ) :
    (diagPhiZ PhiZ).leadingCoeff = -1 :=
  (diagPhiZ_natDegree_and_leadingCoeff hPhi).2

/-- **(B7) Kronecker's unit-leading-coefficient lemma.** The diagonal modular polynomial
`G_m = diagPhiZ PhiZ` has leading coefficient `±1`. This is exactly the `hlead` hypothesis of
`isIntegral_of_kronecker`. -/
theorem diagPhiZ_leadingCoeff_eq [Fact m.Prime] {PhiZ : Polynomial (Polynomial ℤ)}
    (hPhi : ∀ τ : ℍ, orbitPoly m τ = specializeZ (j τ) PhiZ) :
    (diagPhiZ PhiZ).leadingCoeff = 1 ∨ (diagPhiZ PhiZ).leadingCoeff = -1 :=
  Or.inr (diagPhiZ_leadingCoeff_eq_neg_one hPhi)

/-- **The composed integrality corollary.** For a prime `m`, any `PhiZ` with the keystone identity,
and a CM relation `j τ = f m i τ`, the value `j τ` is integral over `ℤ`. Discharges the `hlead`
argument of `isIntegral_of_kronecker`, so downstream only the identity `hPhi` (from `exists_PhiZ`)
and the CM root are needed. -/
theorem isIntegral_j_of_cm [Fact m.Prime] {PhiZ : Polynomial (Polynomial ℤ)}
    (hPhi : ∀ τ : ℍ, orbitPoly m τ = specializeZ (j τ) PhiZ)
    {τ : ℍ} {i : Option (ZMod m)} (hcm : j τ = f m i τ) : IsIntegral ℤ (j τ) := by
  haveI : NeZero m := ⟨(Fact.out : m.Prime).ne_zero⟩
  exact isIntegral_of_kronecker (m := m) (diagPhiZ_leadingCoeff_eq hPhi)
    (diagPhiZ_eval_eq_zero hPhi hcm)

end Chudnovsky
