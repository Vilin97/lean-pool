/-
Copyright (c) 2026 Xuanji Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuanji Li
-/

import LeanPool.Chudnovsky.Liouville

/-!
# The zeros of ℘′ and the factorization of ℘′²

Statements from chapter 1 of Milla (arXiv:1809.00533v6, file `060_ElliptFunct.tex`):

* `PeriodPair.e₁`, `PeriodPair.e₂`, `PeriodPair.e₃` : the half-lattice values
  `e₁ = ℘(ω₁/2)`, `e₂ = ℘(ω₂/2)`, `e₃ = ℘((ω₁+ω₂)/2)` (paper `pstrichprod`);
* the zeros of `℘'` are exactly the half-periods mod `L` (paper `zerowp`);
* the factorization `℘'(z)² = 4(℘(z)-e₁)(℘(z)-e₂)(℘(z)-e₃)` with pairwise distinct
  `e₁, e₂, e₃` (paper `pstrichprod`).

These results are proved here elementarily; the distinctness of `e₁, e₂, e₃` and the
characterisation of the zeros of `℘'` use the third Liouville theorem (from
`LeanPool.Chudnovsky.Liouville`) as a pinned interface.
-/

noncomputable section

namespace PeriodPair

variable (L : PeriodPair)

/-- The first half-lattice value `e₁ = ℘(ω₁/2)` (paper `pstrichprod`). -/
def e₁ : ℂ := ℘[L] (L.ω₁ / 2)

/-- The second half-lattice value `e₂ = ℘(ω₂/2)` (paper `pstrichprod`). -/
def e₂ : ℂ := ℘[L] (L.ω₂ / 2)

/-- The third half-lattice value `e₃ = ℘((ω₁+ω₂)/2)` (paper `pstrichprod`). -/
def e₃ : ℂ := ℘[L] ((L.ω₁ + L.ω₂) / 2)

/-! ## Zeros of ℘′ (paper `zerowp`) -/

/-- `℘'` vanishes at every half-lattice point `l/2` for `l ∈ L`.
This is purely algebraic: `℘'` is odd and `L`-periodic, so
`℘'(l/2) = ℘'(l/2 - l) = ℘'(-l/2) = -℘'(l/2)`. -/
theorem derivWeierstrassP_half_lattice (l : L.lattice) : ℘'[L] ((l : ℂ) / 2) = 0 := by
  have h := L.derivWeierstrassP_sub_coe ((l : ℂ) / 2) l
  rw [show (l : ℂ) / 2 - (l : ℂ) = -((l : ℂ) / 2) by ring, L.derivWeierstrassP_neg] at h
  exact CharZero.eq_neg_self_iff.mp h.symm

/-- `℘'` vanishes at the half-period `ω₁/2`. -/
theorem derivWeierstrassP_ω₁_div_two : ℘'[L] (L.ω₁ / 2) = 0 :=
  L.derivWeierstrassP_half_lattice ⟨L.ω₁, L.ω₁_mem_lattice⟩

/-- `℘'` vanishes at the half-period `ω₂/2`. -/
theorem derivWeierstrassP_ω₂_div_two : ℘'[L] (L.ω₂ / 2) = 0 :=
  L.derivWeierstrassP_half_lattice ⟨L.ω₂, L.ω₂_mem_lattice⟩

/-- `℘'` vanishes at the half-period `(ω₁+ω₂)/2`. -/
theorem derivWeierstrassP_add_div_two : ℘'[L] ((L.ω₁ + L.ω₂) / 2) = 0 :=
  L.derivWeierstrassP_half_lattice ⟨L.ω₁ + L.ω₂, add_mem L.ω₁_mem_lattice L.ω₂_mem_lattice⟩

/-! ### Auxiliary lemmas for the Liouville counting arguments -/

/-- The only lattice point of the fundamental parallelogram is `0`. -/
theorem notMem_lattice_of_mem_fund {z : ℂ} (hz : z ∈ L.fundamentalParallelogram)
    (hz0 : z ≠ 0) : z ∉ L.lattice := by
  obtain ⟨s, ⟨hs0, hs1⟩, t, ⟨ht0, ht1⟩, rfl⟩ := hz
  intro hlat
  rw [mem_lattice] at hlat
  obtain ⟨m, n, hmn⟩ := hlat
  have hmn' : (s : ℂ) * L.ω₁ + (t : ℂ) * L.ω₂ = (m : ℂ) * L.ω₁ + (n : ℂ) * L.ω₂ := by
    rw [hmn]; simp [Complex.real_smul]
  have key : (s - (m : ℝ)) • L.ω₁ + (t - (n : ℝ)) • L.ω₂ = 0 := by
    simp only [sub_smul, Complex.real_smul]
    push_cast
    linear_combination hmn'
  obtain ⟨hsm, htn⟩ := LinearIndependent.pair_iff.mp L.indep (s - (m : ℝ)) (t - (n : ℝ)) key
  have hs : (m : ℝ) = s := (sub_eq_zero.mp hsm).symm
  have ht : (n : ℝ) = t := (sub_eq_zero.mp htn).symm
  have hm0 : m = 0 := by
    have h1 : (0 : ℝ) ≤ (m : ℝ) := hs ▸ hs0
    have h2 : (m : ℝ) < 1 := hs ▸ hs1
    have : (0 : ℤ) ≤ m := by exact_mod_cast h1
    have : m < 1 := by exact_mod_cast h2
    omega
  have hn0 : n = 0 := by
    have h1 : (0 : ℝ) ≤ (n : ℝ) := ht ▸ ht0
    have h2 : (n : ℝ) < 1 := ht ▸ ht1
    have : (0 : ℤ) ≤ n := by exact_mod_cast h1
    have : n < 1 := by exact_mod_cast h2
    omega
  apply hz0
  rw [← hs, ← ht, hm0, hn0]
  simp

/-- `℘ - c` has a pole of order `2` at each lattice point. -/
theorem meromorphicOrderAt_weierstrassP_sub {c : ℂ} {l₀ : ℂ} (h : l₀ ∈ L.lattice) :
    meromorphicOrderAt (fun z => ℘[L] z - c) l₀ = -2 := by
  have heq : (fun z => ℘[L] z - c) = ℘[L] + fun _ => -c := by
    ext z; simp only [Pi.add_apply]; ring
  have hord : meromorphicOrderAt ℘[L] l₀ = -2 := L.order_weierstrassP l₀ h
  have hlt : meromorphicOrderAt ℘[L] l₀ < meromorphicOrderAt (fun _ => -c) l₀ := by
    rw [hord]
    have hneg : (-2 : WithTop ℤ) < 0 := by
      rw [show (-2 : WithTop ℤ) = ((-2 : ℤ) : WithTop ℤ) by norm_cast]
      exact WithTop.coe_lt_coe.mpr (by decide)
    exact lt_of_lt_of_le hneg analyticAt_const.meromorphicOrderAt_nonneg
  rw [heq, meromorphicOrderAt_add_eq_left_of_lt analyticAt_const.meromorphicAt hlt, hord]

/-- `℘ - c` is an elliptic function. -/
theorem isEllipticWith_weierstrassP_sub (c : ℂ) :
    L.IsEllipticWith (fun z => ℘[L] z - c) :=
  ⟨by fun_prop, fun z l => by simp⟩

/-- **Counting bound** from the third Liouville theorem: the elliptic function `℘ - c`
has, counted with multiplicity, at most `2` zeros in the fundamental parallelogram, since
it has a single double pole (at `0`). Concretely, for any finite set `A` of non-lattice
points of the fundamental parallelogram at which `℘ = c`, the multiplicities add up to at
most `2`. -/
theorem sum_untop₀_meromorphicOrderAt_le_two (c : ℂ) (A : Finset ℂ)
    (hAf : ∀ a ∈ A, a ∈ L.fundamentalParallelogram)
    (hAl : ∀ a ∈ A, a ∉ L.lattice) (hAz : ∀ a ∈ A, ℘[L] a = c) :
    ∑ a ∈ A, (meromorphicOrderAt (fun z => ℘[L] z - c) a).untop₀ ≤ 2 := by
  set f : ℂ → ℂ := fun z => ℘[L] z - c with hf_def
  have hell : L.IsEllipticWith f := L.isEllipticWith_weierstrassP_sub c
  have hmero : Meromorphic f := hell.1
  have h0 : ∃ z, meromorphicOrderAt f z ≠ ⊤ := by
    refine ⟨0, ?_⟩
    rw [hf_def, L.meromorphicOrderAt_weierstrassP_sub L.lattice.zero_mem]
    exact (WithTop.coe_ne_top (a := (-2 : ℤ)))
  set T := (hell.finite_order_ne_zero h0).toFinset with hT
  have hmemT : ∀ z, z ∈ T ↔
      z ∈ L.fundamentalParallelogram ∧ meromorphicOrderAt f z ≠ 0 := by
    intro z
    rw [hT, Set.Finite.mem_toFinset, Set.mem_sep_iff]
  have hLiou : ∑ z ∈ T, (meromorphicOrderAt f z).untop₀ = 0 :=
    hell.sum_meromorphicOrderAt_eq_zero h0
  have hfund0 : (0 : ℂ) ∈ L.fundamentalParallelogram :=
    ⟨0, Set.left_mem_Ico.mpr zero_lt_one, 0, Set.left_mem_Ico.mpr zero_lt_one, by simp⟩
  have hord0 : meromorphicOrderAt f (0 : ℂ) = -2 := by
    rw [hf_def, L.meromorphicOrderAt_weierstrassP_sub L.lattice.zero_mem]
  have h0T : (0 : ℂ) ∈ T := (hmemT 0).mpr ⟨hfund0, by rw [hord0]; decide⟩
  have hsum_erase : ∑ z ∈ T.erase 0, (meromorphicOrderAt f z).untop₀ = 2 := by
    have hsplit := Finset.add_sum_erase T (fun z => (meromorphicOrderAt f z).untop₀) h0T
    rw [hLiou] at hsplit
    have : (meromorphicOrderAt f (0 : ℂ)).untop₀ = -2 := by rw [hord0]; decide
    rw [this] at hsplit
    linarith
  have hsub : A ⊆ T.erase 0 := by
    intro a ha
    rw [Finset.mem_erase]
    have hane : a ≠ 0 := fun h => hAl a ha (h ▸ L.lattice.zero_mem)
    refine ⟨hane, (hmemT a).mpr ⟨hAf a ha, ?_⟩⟩
    have hAn : AnalyticAt ℂ f a := by
      rw [hf_def]; have := L.analyticOnNhd_weierstrassP a (hAl a ha); fun_prop
    have hfa : f a = 0 := by rw [hf_def]; simp [hAz a ha]
    rw [hAn.meromorphicOrderAt_eq]
    intro hcontra
    exact hAn.analyticOrderAt_ne_zero.mpr hfa (ENat.map_natCast_eq_zero.mp hcontra)
  calc ∑ a ∈ A, (meromorphicOrderAt f a).untop₀
      ≤ ∑ z ∈ T.erase 0, (meromorphicOrderAt f z).untop₀ := by
        refine Finset.sum_le_sum_of_subset_of_nonneg hsub fun z hz _ => ?_
        rw [Finset.mem_erase] at hz
        obtain ⟨hz0, hzT⟩ := hz
        have hzf : z ∈ L.fundamentalParallelogram := ((hmemT z).mp hzT).1
        have hznl : z ∉ L.lattice := L.notMem_lattice_of_mem_fund hzf hz0
        have hAn : AnalyticAt ℂ f z := by
          rw [hf_def]; have := L.analyticOnNhd_weierstrassP z hznl; fun_prop
        rw [WithTop.untop₀_nonneg]
        exact hAn.meromorphicOrderAt_nonneg
    _ = 2 := hsum_erase

/-- At a point `a ∉ L` where `℘ a = c` and `℘' a = 0`, the function `℘ - c` has a zero of
order at least `2`. -/
theorem two_le_untop₀_meromorphicOrderAt {c : ℂ} {a : ℂ} (ha : a ∉ L.lattice)
    (hc : ℘[L] a = c) (hderiv : ℘'[L] a = 0) :
    2 ≤ (meromorphicOrderAt (fun z => ℘[L] z - c) a).untop₀ := by
  set f : ℂ → ℂ := fun z => ℘[L] z - c with hf_def
  have hAn : AnalyticAt ℂ f a := by
    rw [hf_def]; have := L.analyticOnNhd_weierstrassP a ha; fun_prop
  have hfa : f a = 0 := by rw [hf_def]; simp [hc]
  have hderiv' : deriv f a = 0 := by
    rw [hf_def, deriv_sub_const, L.deriv_weierstrassP]; exact hderiv
  have h2 : (2 : ℕ) ≤ analyticOrderAt f a := by
    rw [natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hAn]
    intro i hi
    interval_cases i
    · simpa [iteratedDeriv_zero] using hfa
    · rw [iteratedDeriv_one]; exact hderiv'
  have hne : meromorphicOrderAt f a ≠ ⊤ := by
    have hmero : Meromorphic f := by rw [hf_def]; fun_prop
    have h0 : meromorphicOrderAt f 0 ≠ ⊤ := by
      rw [hf_def, L.meromorphicOrderAt_weierstrassP_sub L.lattice.zero_mem]
      exact (WithTop.coe_ne_top (a := (-2 : ℤ)))
    exact (meromorphicOn_univ.2 hmero).meromorphicOrderAt_ne_top_of_isPreconnected
      isPreconnected_univ (Set.mem_univ 0) (Set.mem_univ a) h0
  rw [hAn.meromorphicOrderAt_eq] at hne ⊢
  rw [Ne, ENat.map_eq_top_iff] at hne
  lift analyticOrderAt f a to ℕ using hne with n hn
  rw [ENat.map_coe, WithTop.untop₀_coe]
  have : (2 : ℕ) ≤ n := by exact_mod_cast h2
  exact_mod_cast this

/-! ## The factorization of ℘′² (paper `pstrichprod`) -/

/-- `(ω₁+ω₂)/2` is not a lattice point. -/
theorem add_div_two_notMem_lattice : (L.ω₁ + L.ω₂) / 2 ∉ L.lattice := by
  have h := (L.mul_ω₁_add_mul_ω₂_mem_lattice (α := 1 / 2) (β := 1 / 2)).not.mpr (by norm_num)
  intro hmem
  apply h
  rw [show (((1 : ℚ) / 2 : ℚ) : ℂ) * L.ω₁ + (((1 : ℚ) / 2 : ℚ) : ℂ) * L.ω₂
      = (L.ω₁ + L.ω₂) / 2 by push_cast; ring]
  exact hmem

/-- Two distinct real-linear combinations of the periods with coefficients in `[0,1)` differ. -/
theorem half_ne_half {a b a' b' : ℝ} (h : ¬ (a = a' ∧ b = b')) :
    a • L.ω₁ + b • L.ω₂ ≠ a' • L.ω₁ + b' • L.ω₂ := by
  intro he
  have he' : (a : ℂ) * L.ω₁ + (b : ℂ) * L.ω₂ = (a' : ℂ) * L.ω₁ + (b' : ℂ) * L.ω₂ := by
    simpa [Complex.real_smul] using he
  have key : (a - a') • L.ω₁ + (b - b') • L.ω₂ = 0 := by
    simp only [sub_smul, Complex.real_smul]; linear_combination he'
  obtain ⟨h1, h2⟩ := LinearIndependent.pair_iff.mp L.indep _ _ key
  exact h ⟨sub_eq_zero.mp h1, sub_eq_zero.mp h2⟩

/-- If two half-period points of the fundamental parallelogram are distinct, `℘` takes
different values there (both are double zeros of `℘ - value`, and `℘ - c` has at most a
double zero, by the counting bound). -/
theorem weierstrassP_ne_of_half {p q : ℂ}
    (hpf : p ∈ L.fundamentalParallelogram) (hqf : q ∈ L.fundamentalParallelogram)
    (hpl : p ∉ L.lattice) (hql : q ∉ L.lattice) (hpq : p ≠ q)
    (hp' : ℘'[L] p = 0) (hq' : ℘'[L] q = 0) : ℘[L] p ≠ ℘[L] q := by
  intro hEq
  have hp2 : 2 ≤ (meromorphicOrderAt (fun z => ℘[L] z - ℘[L] q) p).untop₀ :=
    L.two_le_untop₀_meromorphicOrderAt hpl hEq hp'
  have hq2 : 2 ≤ (meromorphicOrderAt (fun z => ℘[L] z - ℘[L] q) q).untop₀ :=
    L.two_le_untop₀_meromorphicOrderAt hql rfl hq'
  have hbound := L.sum_untop₀_meromorphicOrderAt_le_two (℘[L] q) {p, q}
    (fun a ha => by
      rcases Finset.mem_insert.mp ha with h | h
      · exact h ▸ hpf
      · exact (Finset.mem_singleton.mp h) ▸ hqf)
    (fun a ha => by
      rcases Finset.mem_insert.mp ha with h | h
      · exact h ▸ hpl
      · exact (Finset.mem_singleton.mp h) ▸ hql)
    (fun a ha => by
      rcases Finset.mem_insert.mp ha with h | h
      · exact h ▸ hEq
      · exact (Finset.mem_singleton.mp h) ▸ rfl)
  rw [Finset.sum_pair hpq] at hbound
  linarith

/-- Membership of `ω₁/2` in the fundamental parallelogram. -/
private theorem mem_fund_ω₁_div_two : L.ω₁ / 2 ∈ L.fundamentalParallelogram :=
  ⟨1 / 2, ⟨by norm_num, by norm_num⟩, 0, ⟨le_refl 0, zero_lt_one⟩, by
    simp [Complex.real_smul]; ring⟩

private theorem mem_fund_ω₂_div_two : L.ω₂ / 2 ∈ L.fundamentalParallelogram :=
  ⟨0, ⟨le_refl 0, zero_lt_one⟩, 1 / 2, ⟨by norm_num, by norm_num⟩, by
    simp [Complex.real_smul]; ring⟩

private theorem mem_fund_add_div_two : (L.ω₁ + L.ω₂) / 2 ∈ L.fundamentalParallelogram :=
  ⟨1 / 2, ⟨by norm_num, by norm_num⟩, 1 / 2, ⟨by norm_num, by norm_num⟩, by
    simp [Complex.real_smul]; ring⟩

private theorem ω₁_div_two_ne_ω₂_div_two : L.ω₁ / 2 ≠ L.ω₂ / 2 := by
  have h := L.half_ne_half (a := 1 / 2) (b := 0) (a' := 0) (b' := 1 / 2) (by norm_num)
  rwa [show (1 / 2 : ℝ) • L.ω₁ + (0 : ℝ) • L.ω₂ = L.ω₁ / 2 by
        simp [Complex.real_smul]; ring,
      show (0 : ℝ) • L.ω₁ + (1 / 2 : ℝ) • L.ω₂ = L.ω₂ / 2 by
        simp [Complex.real_smul]; ring] at h

private theorem ω₁_div_two_ne_add_div_two : L.ω₁ / 2 ≠ (L.ω₁ + L.ω₂) / 2 := by
  have h := L.half_ne_half (a := 1 / 2) (b := 0) (a' := 1 / 2) (b' := 1 / 2) (by norm_num)
  rwa [show (1 / 2 : ℝ) • L.ω₁ + (0 : ℝ) • L.ω₂ = L.ω₁ / 2 by
        simp [Complex.real_smul]; ring,
      show (1 / 2 : ℝ) • L.ω₁ + (1 / 2 : ℝ) • L.ω₂ = (L.ω₁ + L.ω₂) / 2 by
        simp [Complex.real_smul]; ring] at h

private theorem ω₂_div_two_ne_add_div_two : L.ω₂ / 2 ≠ (L.ω₁ + L.ω₂) / 2 := by
  have h := L.half_ne_half (a := 0) (b := 1 / 2) (a' := 1 / 2) (b' := 1 / 2) (by norm_num)
  rwa [show (0 : ℝ) • L.ω₁ + (1 / 2 : ℝ) • L.ω₂ = L.ω₂ / 2 by
        simp [Complex.real_smul]; ring,
      show (1 / 2 : ℝ) • L.ω₁ + (1 / 2 : ℝ) • L.ω₂ = (L.ω₁ + L.ω₂) / 2 by
        simp [Complex.real_smul]; ring] at h

/-- The half-lattice values are pairwise distinct: `e₁ ≠ e₂`. -/
theorem e₁_ne_e₂ : L.e₁ ≠ L.e₂ :=
  L.weierstrassP_ne_of_half L.mem_fund_ω₁_div_two L.mem_fund_ω₂_div_two
    L.ω₁_div_two_notMem_lattice L.ω₂_div_two_notMem_lattice
    L.ω₁_div_two_ne_ω₂_div_two L.derivWeierstrassP_ω₁_div_two L.derivWeierstrassP_ω₂_div_two

/-- The half-lattice values are pairwise distinct: `e₁ ≠ e₃`. -/
theorem e₁_ne_e₃ : L.e₁ ≠ L.e₃ :=
  L.weierstrassP_ne_of_half L.mem_fund_ω₁_div_two L.mem_fund_add_div_two
    L.ω₁_div_two_notMem_lattice L.add_div_two_notMem_lattice
    L.ω₁_div_two_ne_add_div_two L.derivWeierstrassP_ω₁_div_two L.derivWeierstrassP_add_div_two

/-- The half-lattice values are pairwise distinct: `e₂ ≠ e₃`. -/
theorem e₂_ne_e₃ : L.e₂ ≠ L.e₃ :=
  L.weierstrassP_ne_of_half L.mem_fund_ω₂_div_two L.mem_fund_add_div_two
    L.ω₂_div_two_notMem_lattice L.add_div_two_notMem_lattice
    L.ω₂_div_two_ne_add_div_two L.derivWeierstrassP_ω₂_div_two L.derivWeierstrassP_add_div_two

/-- Each `e_k` is a root of the cubic `4x³ - g₂ x - g₃`. -/
private theorem cubic_root_e₁ : 4 * L.e₁ ^ 3 - L.g₂ * L.e₁ - L.g₃ = 0 := by
  have h := L.derivWeierstrassP_sq (L.ω₁ / 2) L.ω₁_div_two_notMem_lattice
  rw [L.derivWeierstrassP_ω₁_div_two] at h
  have h' : (0 : ℂ) ^ 2 = 4 * L.e₁ ^ 3 - L.g₂ * L.e₁ - L.g₃ := h
  linear_combination -h'

private theorem cubic_root_e₂ : 4 * L.e₂ ^ 3 - L.g₂ * L.e₂ - L.g₃ = 0 := by
  have h := L.derivWeierstrassP_sq (L.ω₂ / 2) L.ω₂_div_two_notMem_lattice
  rw [L.derivWeierstrassP_ω₂_div_two] at h
  have h' : (0 : ℂ) ^ 2 = 4 * L.e₂ ^ 3 - L.g₂ * L.e₂ - L.g₃ := h
  linear_combination -h'

private theorem cubic_root_e₃ : 4 * L.e₃ ^ 3 - L.g₂ * L.e₃ - L.g₃ = 0 := by
  have h := L.derivWeierstrassP_sq ((L.ω₁ + L.ω₂) / 2) L.add_div_two_notMem_lattice
  rw [L.derivWeierstrassP_add_div_two] at h
  have h' : (0 : ℂ) ^ 2 = 4 * L.e₃ ^ 3 - L.g₂ * L.e₃ - L.g₃ := h
  linear_combination -h'

/-- The factorization `℘'(z)² = 4(℘(z)-e₁)(℘(z)-e₂)(℘(z)-e₃)` (paper `pstrichprod`). -/
theorem derivWeierstrassP_sq_eq_four_mul_prod (z : ℂ) (hz : z ∉ L.lattice) :
    ℘'[L] z ^ 2 = 4 * (℘[L] z - L.e₁) * (℘[L] z - L.e₂) * (℘[L] z - L.e₃) := by
  rw [L.derivWeierstrassP_sq z hz]
  set w := ℘[L] z
  have hr1 := L.cubic_root_e₁
  have hr2 := L.cubic_root_e₂
  have hr3 := L.cubic_root_e₃
  have d12 : L.e₁ - L.e₂ ≠ 0 := sub_ne_zero.mpr L.e₁_ne_e₂
  have d13 : L.e₁ - L.e₃ ≠ 0 := sub_ne_zero.mpr L.e₁_ne_e₃
  have d23 : L.e₂ - L.e₃ ≠ 0 := sub_ne_zero.mpr L.e₂_ne_e₃
  have s12 : 4 * (L.e₁ ^ 2 + L.e₁ * L.e₂ + L.e₂ ^ 2) - L.g₂ = 0 :=
    (mul_eq_zero.mp (show (L.e₁ - L.e₂) *
      (4 * (L.e₁ ^ 2 + L.e₁ * L.e₂ + L.e₂ ^ 2) - L.g₂) = 0 by
      linear_combination hr1 - hr2)).resolve_left d12
  have s13 : 4 * (L.e₁ ^ 2 + L.e₁ * L.e₃ + L.e₃ ^ 2) - L.g₂ = 0 :=
    (mul_eq_zero.mp (show (L.e₁ - L.e₃) *
      (4 * (L.e₁ ^ 2 + L.e₁ * L.e₃ + L.e₃ ^ 2) - L.g₂) = 0 by
      linear_combination hr1 - hr3)).resolve_left d13
  have sum0 : L.e₁ + L.e₂ + L.e₃ = 0 := by
    have h4 : 4 * (L.e₁ + L.e₂ + L.e₃) = 0 :=
      (mul_eq_zero.mp (show (L.e₂ - L.e₃) * (4 * (L.e₁ + L.e₂ + L.e₃)) = 0 by
        linear_combination s12 - s13)).resolve_left d23
    linear_combination (1 / 4 : ℂ) * h4
  have vieta2 : L.g₂ = -4 * (L.e₁ * L.e₂ + L.e₁ * L.e₃ + L.e₂ * L.e₃) := by
    linear_combination -s12 + 4 * (L.e₁ + L.e₂) * sum0
  have vieta3 : L.g₃ = 4 * (L.e₁ * L.e₂ * L.e₃) := by
    linear_combination -hr1 - L.e₁ * vieta2 + 4 * L.e₁ ^ 2 * sum0
  linear_combination 4 * w ^ 2 * sum0 - w * vieta2 - vieta3

/-! ## Characterisation of the zeros of `℘'` (paper `zerowp`) -/

/-- Every point of `ℂ` is congruent modulo `L` to a point of the fundamental
parallelogram. -/
theorem exists_mem_fund (z₀ : ℂ) :
    ∃ p ∈ L.fundamentalParallelogram, z₀ - p ∈ L.lattice := by
  set s := L.basis.repr z₀ 0 with hs
  set t := L.basis.repr z₀ 1 with ht
  have hz₀ : z₀ = s • L.ω₁ + t • L.ω₂ := by
    have h := L.basis.sum_repr z₀
    rw [Fin.sum_univ_two, L.basis_zero, L.basis_one] at h
    exact h.symm
  refine ⟨Int.fract s • L.ω₁ + Int.fract t • L.ω₂,
    ⟨Int.fract s, ⟨Int.fract_nonneg s, Int.fract_lt_one s⟩, Int.fract t,
      ⟨Int.fract_nonneg t, Int.fract_lt_one t⟩, rfl⟩, ?_⟩
  rw [mem_lattice]
  refine ⟨⌊s⌋, ⌊t⌋, ?_⟩
  rw [hz₀]
  simp only [Complex.real_smul, Int.fract]
  push_cast
  ring

/-- The zeros of `℘'` are exactly the points `ω/2` with `ω ∈ L` but `ω/2 ∉ L`, i.e. for
`z ∉ L` we have `℘'(z) = 0` iff `2z ∈ L` (paper `zerowp`). -/
theorem derivWeierstrassP_eq_zero_iff {z : ℂ} (hz : z ∉ L.lattice) :
    ℘'[L] z = 0 ↔ 2 * z ∈ L.lattice := by
  constructor
  · -- `℘'(z) = 0 → 2z ∈ L`
    intro hderiv0
    by_contra hcontra
    obtain ⟨p, hpf, hpl⟩ := L.exists_mem_fund z
    have hpp : ℘[L] p = ℘[L] z := by
      have h := L.weierstrassP_sub_coe z ⟨z - p, hpl⟩
      rwa [show z - ((⟨z - p, hpl⟩ : L.lattice) : ℂ) = p from by
        rw [show ((⟨z - p, hpl⟩ : L.lattice) : ℂ) = z - p from rfl]; ring] at h
    have hpd : ℘'[L] p = ℘'[L] z := by
      have h := L.derivWeierstrassP_sub_coe z ⟨z - p, hpl⟩
      rwa [show z - ((⟨z - p, hpl⟩ : L.lattice) : ℂ) = p from by
        rw [show ((⟨z - p, hpl⟩ : L.lattice) : ℂ) = z - p from rfl]; ring] at h
    have hpnl : p ∉ L.lattice := fun hp => hz (by
      have := add_mem hpl hp; rwa [sub_add_cancel] at this)
    have hfac : (℘[L] z - L.e₁) * (℘[L] z - L.e₂) * (℘[L] z - L.e₃) = 0 := by
      have h := L.derivWeierstrassP_sq_eq_four_mul_prod z hz
      rw [hderiv0] at h
      have h4 : (4 : ℂ) * ((℘[L] z - L.e₁) * (℘[L] z - L.e₂) * (℘[L] z - L.e₃)) = 0 := by
        linear_combination -h
      exact (mul_eq_zero.mp h4).resolve_left (by norm_num)
    -- If `℘ p = e_k` but `p ≠ ω_k/2`, we get 4 zeros vs 2 poles, contradiction.
    have finish : ∀ q ω : ℂ, ω ∈ L.lattice → q = ω / 2 →
        q ∈ L.fundamentalParallelogram → q ∉ L.lattice → ℘'[L] q = 0 →
        ℘[L] p = ℘[L] q → False := by
      intro q ω hω hqω hqf hqnl hqd hpq
      have hpeq : p = q := by
        by_contra hpne
        exact L.weierstrassP_ne_of_half hpf hqf hpnl hqnl hpne (hpd.trans hderiv0) hqd hpq
      apply hcontra
      have h1 : z - q ∈ L.lattice := hpeq ▸ hpl
      have h2 : (2 : ℤ) • (z - q) + ω ∈ L.lattice :=
        add_mem (Submodule.smul_mem _ _ h1) hω
      have he : (2 : ℤ) • (z - q) + ω = 2 * z := by
        rw [zsmul_eq_mul, hqω]; push_cast; ring
      rwa [he] at h2
    rcases mul_eq_zero.mp hfac with h | h
    · rcases mul_eq_zero.mp h with h | h
      · exact finish (L.ω₁ / 2) L.ω₁ L.ω₁_mem_lattice rfl L.mem_fund_ω₁_div_two
          L.ω₁_div_two_notMem_lattice L.derivWeierstrassP_ω₁_div_two
          (hpp.trans (sub_eq_zero.mp h))
      · exact finish (L.ω₂ / 2) L.ω₂ L.ω₂_mem_lattice rfl L.mem_fund_ω₂_div_two
          L.ω₂_div_two_notMem_lattice L.derivWeierstrassP_ω₂_div_two
          (hpp.trans (sub_eq_zero.mp h))
    · exact finish ((L.ω₁ + L.ω₂) / 2) (L.ω₁ + L.ω₂)
        (add_mem L.ω₁_mem_lattice L.ω₂_mem_lattice) rfl L.mem_fund_add_div_two
        L.add_div_two_notMem_lattice L.derivWeierstrassP_add_div_two
        (hpp.trans (sub_eq_zero.mp h))
  · -- `2z ∈ L → ℘'(z) = 0`
    intro h2z
    rw [mem_lattice] at h2z
    obtain ⟨m, n, hmn⟩ := h2z
    have key : ∀ d : L.lattice, ℘'[L] (z - (d : ℂ)) = 0 → ℘'[L] z = 0 := by
      intro d hp
      rwa [L.derivWeierstrassP_sub_coe z d] at hp
    rcases Int.even_or_odd m with ⟨a, ha⟩ | ⟨a, ha⟩ <;>
        rcases Int.even_or_odd n with ⟨b, hb⟩ | ⟨b, hb⟩
    · subst ha hb
      exact absurd (mem_lattice.mpr
        ⟨a, b, by push_cast at hmn ⊢; linear_combination (1 / 2 : ℂ) * hmn⟩) hz
    · subst ha hb
      refine key ⟨(a : ℂ) * L.ω₁ + (b : ℂ) * L.ω₂, mem_lattice.mpr ⟨a, b, rfl⟩⟩ ?_
      change ℘'[L] (z - ((a : ℂ) * L.ω₁ + (b : ℂ) * L.ω₂)) = 0
      rw [show z - ((a : ℂ) * L.ω₁ + (b : ℂ) * L.ω₂) = L.ω₂ / 2 by
        push_cast at hmn ⊢; linear_combination (-1 / 2 : ℂ) * hmn]
      exact L.derivWeierstrassP_ω₂_div_two
    · subst ha hb
      refine key ⟨(a : ℂ) * L.ω₁ + (b : ℂ) * L.ω₂, mem_lattice.mpr ⟨a, b, rfl⟩⟩ ?_
      change ℘'[L] (z - ((a : ℂ) * L.ω₁ + (b : ℂ) * L.ω₂)) = 0
      rw [show z - ((a : ℂ) * L.ω₁ + (b : ℂ) * L.ω₂) = L.ω₁ / 2 by
        push_cast at hmn ⊢; linear_combination (-1 / 2 : ℂ) * hmn]
      exact L.derivWeierstrassP_ω₁_div_two
    · subst ha hb
      refine key ⟨(a : ℂ) * L.ω₁ + (b : ℂ) * L.ω₂, mem_lattice.mpr ⟨a, b, rfl⟩⟩ ?_
      change ℘'[L] (z - ((a : ℂ) * L.ω₁ + (b : ℂ) * L.ω₂)) = 0
      rw [show z - ((a : ℂ) * L.ω₁ + (b : ℂ) * L.ω₂) = (L.ω₁ + L.ω₂) / 2 by
        push_cast at hmn ⊢; linear_combination (-1 / 2 : ℂ) * hmn]
      exact L.derivWeierstrassP_add_div_two

end PeriodPair
