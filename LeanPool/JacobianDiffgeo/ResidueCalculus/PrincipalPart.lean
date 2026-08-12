/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

/-
Blueprint unit: residue-calculus. Principal parts and the decomposition theorem.
-/
import LeanPool.JacobianDiffgeo.ResidueCalculus.LaurentCoeff

/-!
# Principal parts at a point (residue-calculus)

`RS.principalPartAt f z₀` is the finite sum of the negative-exponent Laurent terms of `f` at
`z₀` — an honest function `ℂ → ℂ`, analytic away from `z₀` and meromorphic at `z₀`; it is `0`
(empty sum) when `f` is analytic-after-repair at `z₀`, not meromorphic there, or locally `0`.

Main exports:
* `RS.MeromorphicAt.exists_principalPart_add_analyticAt` — THE decomposition
  `f =ᶠ[𝓝[≠] z₀] principalPartAt f z₀ + h` with `h` analytic whose Taylor coefficients are the
  nonnegative Laurent coefficients of `f`;
* `RS.MeromorphicAt.orderAt_sub_principalPartAt_nonneg` — repair form;
* `RS.laurentCoeffAt_principalPartAt` — the principal part has exactly the negative tail;
* `RS.eq_principalPart_of_eventuallyEq` — uniqueness of tail + analytic decompositions.
-/

open Filter Topology Metric Function

namespace RS

variable {f g h : ℂ → ℂ} {z₀ : ℂ} {k n : ℤ}

/-- The principal part of `f` at `z₀`: the finite sum of the negative-exponent Laurent terms.
An honest function `ℂ → ℂ`, analytic on `ℂ \ {z₀}`, meromorphic at `z₀`. Zero (empty sum)
when `f` is analytic-after-repair at `z₀`, not meromorphic there, or locally `0`. -/
noncomputable def principalPartAt (f : ℂ → ℂ) (z₀ : ℂ) : ℂ → ℂ := fun z =>
  ∑ k ∈ Finset.Icc (meromorphicOrderAt f z₀).untop₀ (-1),
    laurentCoeffAt f z₀ k * (z - z₀) ^ k

theorem meromorphicAt_principalPartAt : MeromorphicAt (principalPartAt f z₀) z₀ := by
  unfold principalPartAt
  apply MeromorphicAt.fun_sum
  intro i _
  fun_prop

theorem analyticOnNhd_principalPartAt : AnalyticOnNhd ℂ (principalPartAt f z₀) {z₀}ᶜ := by
  intro w hw
  have hwne : w ≠ z₀ := hw
  unfold principalPartAt
  apply Finset.analyticAt_fun_sum
  intro i _
  have hb : AnalyticAt ℂ (fun z => z - z₀) w := by fun_prop
  have hz : AnalyticAt ℂ (fun z => (z - z₀) ^ i) w :=
    hb.zpow (n := i) (by simpa [sub_ne_zero] using hwne)
  have : AnalyticAt ℂ (fun z => laurentCoeffAt f z₀ i * (z - z₀) ^ i) w :=
    analyticAt_const.mul hz
  exact this

theorem principalPartAt_eq_zero_of_order_nonneg (h : 0 ≤ meromorphicOrderAt f z₀) :
    principalPartAt f z₀ = 0 := by
  have huntop : (0 : ℤ) ≤ (meromorphicOrderAt f z₀).untop₀ := WithTop.untop₀_nonneg.2 h
  funext z
  unfold principalPartAt
  rw [Finset.Icc_eq_empty (by omega : ¬ (meromorphicOrderAt f z₀).untop₀ ≤ -1),
    Finset.sum_empty]
  rfl

theorem principalPartAt_of_not_meromorphicAt (h : ¬ MeromorphicAt f z₀) :
    principalPartAt f z₀ = 0 :=
  principalPartAt_eq_zero_of_order_nonneg
    (by simp [meromorphicOrderAt_of_not_meromorphicAt h])

theorem principalPartAt_of_order_eq_top (h : meromorphicOrderAt f z₀ = ⊤) :
    principalPartAt f z₀ = 0 :=
  principalPartAt_eq_zero_of_order_nonneg (by rw [h]; exact le_top)

/-- The Laurent coefficients of the principal part: exactly the negative tail of `f`. -/
theorem laurentCoeffAt_principalPartAt (_hf : MeromorphicAt f z₀) (k : ℤ) :
    laurentCoeffAt (principalPartAt f z₀) z₀ k
      = if k < 0 then laurentCoeffAt f z₀ k else 0 := by
  unfold principalPartAt
  rw [laurentCoeffAt_fun_sum (fun i _ => by fun_prop) k]
  have hterm : ∀ i ∈ Finset.Icc (meromorphicOrderAt f z₀).untop₀ (-1),
      laurentCoeffAt (fun z => laurentCoeffAt f z₀ i * (z - z₀) ^ i) z₀ k
        = if k = i then laurentCoeffAt f z₀ i else 0 := by
    intro i _
    rw [laurentCoeffAt_const_mul, laurentCoeffAt_zpow_monomial]
    split_ifs <;> simp
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq]
  simp only [Finset.mem_Icc]
  by_cases hne : meromorphicOrderAt f z₀ = ⊤
  · simp [laurentCoeffAt_of_order_eq_top hne]
  · split_ifs with h1 h2 h2
    · rfl
    · omega
    · have hk : k < (meromorphicOrderAt f z₀).untop₀ := by omega
      have hlt : (k : WithTop ℤ) < meromorphicOrderAt f z₀ := by
        rw [← WithTop.coe_untop₀_of_ne_top hne]
        exact_mod_cast hk
      exact (laurentCoeffAt_eq_zero_of_lt_order hlt).symm
    · rfl

/-- THE decomposition: `f = (principal part) + (analytic)` on a punctured neighborhood.
The analytic part's Taylor coefficients are the nonnegative Laurent coefficients of `f`. -/
theorem MeromorphicAt.exists_principalPart_add_analyticAt (hf : MeromorphicAt f z₀) :
    ∃ h : ℂ → ℂ, AnalyticAt ℂ h z₀ ∧
      (∀ j : ℕ, taylorCoeffAt h z₀ j = laurentCoeffAt f z₀ (j : ℤ)) ∧
      f =ᶠ[𝓝[≠] z₀] fun z => principalPartAt f z₀ z + h z := by
  by_cases h₂ : meromorphicOrderAt f z₀ = ⊤
  · refine ⟨fun _ => 0, analyticAt_const, ?_, ?_⟩
    · intro j
      simp [laurentCoeffAt_of_order_eq_top h₂]
    · have hP : principalPartAt f z₀ = 0 := principalPartAt_of_order_eq_top h₂
      filter_upwards [meromorphicOrderAt_eq_top_iff.1 h₂] with z hz
      rw [hz, hP]
      simp
  · obtain ⟨u, h₁u, h₂u, h₃u⟩ := (meromorphicOrderAt_ne_top_iff hf).1 h₂
    simp only [smul_eq_mul] at h₃u
    rcases lt_or_ge (meromorphicOrderAt f z₀).untop₀ 0 with hneg | hpos
    · -- pole case: Taylor remainder of `u` at depth `(-order).toNat`
      obtain ⟨r, hran, hrcoeff, hrpt⟩ :=
        AnalyticAt.exists_taylor_remainder h₁u (-(meromorphicOrderAt f z₀).untop₀).toNat
      refine ⟨r, hran, ?_, ?_⟩
      · intro j
        rw [hrcoeff j, laurentCoeffAt_of_eventuallyEq h₁u h₃u (j : ℤ),
          ite_eq_left (by omega : (meromorphicOrderAt f z₀).untop₀ ≤ (j : ℤ))]
        congr 1
        omega
      · filter_upwards [h₃u, self_mem_nhdsWithin] with z hz hz'
        have hzne : z ≠ z₀ := hz'
        have hw : z - z₀ ≠ 0 := sub_ne_zero.2 hzne
        rw [hz, hrpt z, mul_add]
        have hcancel : (z - z₀) ^ (meromorphicOrderAt f z₀).untop₀ *
            ((z - z₀) ^ (-(meromorphicOrderAt f z₀).untop₀).toNat * r z) = r z := by
          rw [← mul_assoc,
            ← zpow_natCast (z - z₀) (-(meromorphicOrderAt f z₀).untop₀).toNat,
            ← zpow_add₀ hw,
            (by omega : (meromorphicOrderAt f z₀).untop₀
              + ((-(meromorphicOrderAt f z₀).untop₀).toNat : ℤ) = 0),
            zpow_zero, one_mul]
        rw [hcancel]
        congr 1
        -- (z - z₀) ^ order * (Taylor polynomial of u) = principal part of f at z
        unfold principalPartAt
        rw [Finset.mul_sum]
        refine Finset.sum_nbij' (fun d => (meromorphicOrderAt f z₀).untop₀ + (d : ℤ))
          (fun k => (k - (meromorphicOrderAt f z₀).untop₀).toNat) ?_ ?_ ?_ ?_ ?_
        · intro d hd
          simp only [Finset.mem_range] at hd
          simp only [Finset.mem_Icc]
          omega
        · intro k hk
          simp only [Finset.mem_Icc] at hk
          simp only [Finset.mem_range]
          omega
        · intro d hd
          simp only [Finset.mem_range] at hd
          omega
        · intro k hk
          simp only [Finset.mem_Icc] at hk
          omega
        · intro d hd
          simp only [Finset.mem_range] at hd
          have hcoeff : laurentCoeffAt f z₀ ((meromorphicOrderAt f z₀).untop₀ + (d : ℤ))
              = taylorCoeffAt u z₀ d := by
            rw [laurentCoeffAt_of_eventuallyEq h₁u h₃u _, ite_eq_left (by omega)]
            congr 1
            omega
          rw [hcoeff, ← zpow_natCast (z - z₀) d,
            zpow_add₀ hw (meromorphicOrderAt f z₀).untop₀ (d : ℤ)]
          ring
    · -- analytic-after-repair: principal part vanishes
      have hP : principalPartAt f z₀ = 0 := principalPartAt_eq_zero_of_order_nonneg (by
        rw [← WithTop.coe_untop₀_of_ne_top h₂]
        exact_mod_cast hpos)
      refine ⟨fun z => (z - z₀) ^ (meromorphicOrderAt f z₀).untop₀.toNat * u z,
        by fun_prop, ?_, ?_⟩
      · intro j
        rw [taylorCoeffAt_sub_pow_mul h₁u, laurentCoeffAt_of_eventuallyEq h₁u h₃u (j : ℤ)]
        split_ifs <;> first | rfl | omega | (congr 1; omega)
      · filter_upwards [h₃u] with z hz
        rw [hP, hz]
        simp only [Pi.zero_apply, zero_add]
        congr 1
        rw [← zpow_natCast (z - z₀) (meromorphicOrderAt f z₀).untop₀.toNat]
        congr 1
        omega

/-- Repair form (`MeromorphicNFAt`-compatible corollary): subtracting the principal part
leaves a germ of nonnegative order. -/
theorem MeromorphicAt.orderAt_sub_principalPartAt_nonneg (hf : MeromorphicAt f z₀) :
    0 ≤ meromorphicOrderAt (fun z => f z - principalPartAt f z₀ z) z₀ := by
  obtain ⟨h, hh, _, hdecomp⟩ := MeromorphicAt.exists_principalPart_add_analyticAt hf
  have hcongr : (fun z => f z - principalPartAt f z₀ z) =ᶠ[𝓝[≠] z₀] h := by
    filter_upwards [hdecomp] with z hz
    rw [hz]
    ring
  rw [meromorphicOrderAt_congr hcongr, hh.meromorphicOrderAt_eq]
  cases analyticOrderAt h z₀ with
  | top => simp
  | coe m =>
    rw [ENat.map_natCast]
    exact_mod_cast Int.natCast_nonneg m

/-- Uniqueness: any Laurent-tail + analytic decomposition IS the canonical one. -/
theorem eq_principalPart_of_eventuallyEq {c : ℤ → ℂ} {s : Finset ℤ}
    (hs : ∀ k ∈ s, k < 0) (hh : AnalyticAt ℂ h z₀)
    (hfg : f =ᶠ[𝓝[≠] z₀] fun z => (∑ k ∈ s, c k * (z - z₀) ^ k) + h z) :
    (∀ k ∈ s, c k = laurentCoeffAt f z₀ k) ∧
      (∀ k < 0, k ∉ s → laurentCoeffAt f z₀ k = 0) ∧
      ∀ j : ℕ, taylorCoeffAt h z₀ j = laurentCoeffAt f z₀ (j : ℤ) := by
  classical
  have hTail : MeromorphicAt (fun z => ∑ k ∈ s, c k * (z - z₀) ^ k) z₀ :=
    MeromorphicAt.fun_sum fun i _ => by fun_prop
  have hkey : ∀ k : ℤ, laurentCoeffAt f z₀ k
      = (if k ∈ s then c k else 0)
        + (if 0 ≤ k then taylorCoeffAt h z₀ k.toNat else 0) := by
    intro k
    rw [laurentCoeffAt_congr hfg k, laurentCoeffAt_fun_add hTail hh.meromorphicAt k,
      laurentCoeffAt_fun_sum (fun i _ => by fun_prop) k, laurentCoeffAt_of_analyticAt hh k]
    congr 1
    have hterm : ∀ i ∈ s, laurentCoeffAt (fun z => c i * (z - z₀) ^ i) z₀ k
        = if k = i then c i else 0 := by
      intro i _
      rw [laurentCoeffAt_const_mul, laurentCoeffAt_zpow_monomial]
      split_ifs <;> simp
    rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq]
  refine ⟨?_, ?_, ?_⟩
  · intro k hk
    rw [hkey k, ite_eq_left hk, ite_eq_right (not_le.2 (hs k hk)), add_zero]
  · intro k hk hks
    rw [hkey k, ite_eq_right hks, ite_eq_right (not_le.2 hk), add_zero]
  · intro j
    rw [hkey (j : ℤ), ite_eq_right (fun hmem => absurd (hs _ hmem) (by omega)),
      ite_eq_left (Int.natCast_nonneg j), zero_add]
    simp

end RS
