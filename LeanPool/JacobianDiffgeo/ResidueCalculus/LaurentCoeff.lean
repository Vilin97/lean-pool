/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

/-
Blueprint unit: residue-calculus. Laurent coefficients of planar meromorphic germs.
-/
import LeanPool.JacobianDiffgeo.ResidueCalculus.TaylorCoeff
import Mathlib.Analysis.Meromorphic.TrailingCoefficient

/-!
# Laurent coefficients at a point (residue-calculus)

`RS.laurentCoeffAt f z₀ k` is the `k`-th Laurent coefficient of `f` at `z₀` (coefficient of
`(z - z₀) ^ k`), defined through the meromorphic order presentation and the `dslope`-iterate
Taylor extractor `RS.taylorCoeffAt`. Junk value `0` for non-meromorphic germs, the locally-zero
germ (order `⊤`), and coefficients below the order.

Main exports:
* `RS.laurentCoeffAt_of_eventuallyEq` — THE characterization: any presentation
  `f =ᶠ[𝓝[≠] z₀] (· - z₀) ^ n * g` with `g` analytic computes every Laurent coefficient
  (`n` need not be the order, `g z₀ = 0` is allowed);
* `RS.laurentCoeffAt_congr` — invariance under `=ᶠ[𝓝[≠] z₀]`;
* `RS.laurentCoeffAt_order` — compatibility with `meromorphicTrailingCoeffAt`;
* `RS.laurentCoeffAt_fun_add` / `_const_mul` / `_sub` / `_fun_sum` — ℂ-linearity;
* `RS.laurentCoeffAt_zpow_monomial`, `RS.laurentCoeffAt_zpow_mul` — monomials and shift;
* `RS.forall_neg_laurentCoeffAt_eq_zero_iff` — vanishing tail ↔ analytic-after-repair.
-/

open Filter Topology Metric Function

namespace RS

variable {f g : ℂ → ℂ} {z₀ : ℂ} {k n : ℤ}

/-- The `k`-th Laurent coefficient of `f` at `z₀` (coefficient of `(z - z₀) ^ k`).
Defined through the order presentation `f =ᶠ[𝓝[≠] z₀] (· - z₀) ^ n • g`, `g` analytic,
`g z₀ ≠ 0`, `n = meromorphicOrderAt f z₀`: the coefficient is the `(k - n)`-th Taylor
coefficient of `g`. Junk `0` if `f` is not meromorphic at `z₀`, on the locally-zero germ
(order `⊤`), and for `k <` order. -/
noncomputable def laurentCoeffAt (f : ℂ → ℂ) (z₀ : ℂ) (k : ℤ) : ℂ := by
  by_cases h₁ : MeromorphicAt f z₀
  · by_cases h₂ : meromorphicOrderAt f z₀ = ⊤
    · exact 0
    · exact if (meromorphicOrderAt f z₀).untop₀ ≤ k then
        taylorCoeffAt (((meromorphicOrderAt_ne_top_iff h₁).1 h₂).choose) z₀
          (k - (meromorphicOrderAt f z₀).untop₀).toNat
      else 0
  · exact 0

@[simp] theorem laurentCoeffAt_of_not_meromorphicAt (h : ¬ MeromorphicAt f z₀) (k : ℤ) :
    laurentCoeffAt f z₀ k = 0 := by
  simp [laurentCoeffAt, h]

@[simp] theorem laurentCoeffAt_of_order_eq_top (h : meromorphicOrderAt f z₀ = ⊤) (k : ℤ) :
    laurentCoeffAt f z₀ k = 0 := by
  by_cases h₁ : MeromorphicAt f z₀
  · simp [laurentCoeffAt, h₁, h]
  · simp [laurentCoeffAt, h₁]

/-- Cancel a `zpow` factor across an eventual equality on the punctured filter. -/
private theorem eventuallyEq_of_zpow_mul_eventuallyEq {u v : ℂ → ℂ} {a b : ℤ}
    (h : (fun z => (z - z₀) ^ a * u z) =ᶠ[𝓝[≠] z₀] fun z => (z - z₀) ^ b * v z)
    (hab : a ≤ b) : u =ᶠ[𝓝[≠] z₀] fun z => (z - z₀) ^ (b - a).toNat * v z := by
  filter_upwards [h, self_mem_nhdsWithin] with z hz hz'
  have hzne : z ≠ z₀ := hz'
  have hw : z - z₀ ≠ 0 := sub_ne_zero.2 hzne
  have hexp : (z - z₀) ^ a * (z - z₀) ^ ((b - a).toNat) = (z - z₀) ^ b := by
    rw [← zpow_natCast (z - z₀) (b - a).toNat, ← zpow_add₀ hw]
    congr 1
    omega
  apply mul_left_cancel₀ (zpow_ne_zero a hw)
  rw [hz, ← mul_assoc, hexp]

/-- Comparison of two presentations: the second one is a unit presentation (`u z₀ ≠ 0`). -/
private theorem taylor_eq_of_two_presentations {m : ℤ} {u : ℂ → ℂ}
    (hg : AnalyticAt ℂ g z₀) (hu : AnalyticAt ℂ u z₀) (hune : u z₀ ≠ 0)
    (h : (fun z => (z - z₀) ^ n * g z) =ᶠ[𝓝[≠] z₀] fun z => (z - z₀) ^ m * u z) (k : ℤ) :
    (if m ≤ k then taylorCoeffAt u z₀ (k - m).toNat else 0)
      = if n ≤ k then taylorCoeffAt g z₀ (k - n).toNat else 0 := by
  have hnm : n ≤ m := by
    by_contra hlt
    rw [not_le] at hlt
    have h1 : u =ᶠ[𝓝[≠] z₀] fun z => (z - z₀) ^ (n - m).toNat * g z :=
      eventuallyEq_of_zpow_mul_eventuallyEq h.symm hlt.le
    have h2 : u =ᶠ[𝓝 z₀] fun z => (z - z₀) ^ (n - m).toNat * g z :=
      (hu.continuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE (by fun_prop)).1 h1
    have h3 := h2.eq_of_nhds
    rw [sub_self, zero_pow (by omega : (n - m).toNat ≠ 0), zero_mul] at h3
    exact hune h3
  have h4 : g =ᶠ[𝓝[≠] z₀] fun z => (z - z₀) ^ (m - n).toNat * u z :=
    eventuallyEq_of_zpow_mul_eventuallyEq h hnm
  have h5 : g =ᶠ[𝓝 z₀] fun z => (z - z₀) ^ (m - n).toNat * u z :=
    (hg.continuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE (by fun_prop)).1 h4
  have h6 : ∀ j, taylorCoeffAt g z₀ j
      = if j < (m - n).toNat then 0 else taylorCoeffAt u z₀ (j - (m - n).toNat) := by
    intro j
    rw [taylorCoeffAt_congr h5 j, taylorCoeffAt_sub_pow_mul hu]
  rcases lt_or_ge k m with hkm | hmk
  · rw [if_neg (not_le.2 hkm)]
    split_ifs with hnk
    · rw [h6 (k - n).toNat, if_pos (by omega)]
    · rfl
  · rw [if_pos hmk, if_pos (hnm.trans hmk), h6 (k - n).toNat,
      if_neg (by omega : ¬ (k - n).toNat < (m - n).toNat)]
    congr 1
    omega

/-- THE characterization (workhorse; the only lemma that unfolds the definition).
Any zpow-presentation computes every Laurent coefficient — `n` need NOT be the order and
`g z₀ = 0` is allowed. -/
theorem laurentCoeffAt_of_eventuallyEq (hg : AnalyticAt ℂ g z₀)
    (hfg : f =ᶠ[𝓝[≠] z₀] fun z => (z - z₀) ^ n * g z) (k : ℤ) :
    laurentCoeffAt f z₀ k = if n ≤ k then taylorCoeffAt g z₀ (k - n).toNat else 0 := by
  have hf : MeromorphicAt f z₀ := by
    rw [MeromorphicAt.meromorphicAt_congr hfg]
    fun_prop
  by_cases h₂ : meromorphicOrderAt f z₀ = ⊤
  · -- locally-zero germ: `g` vanishes near `z₀`, both sides are `0`
    have hg0 : g =ᶠ[𝓝[≠] z₀] fun _ => (0 : ℂ) := by
      have h0 : (fun z => (z - z₀) ^ n * g z) =ᶠ[𝓝[≠] z₀] fun _ => (0 : ℂ) :=
        hfg.symm.trans (meromorphicOrderAt_eq_top_iff.1 h₂)
      filter_upwards [h0, self_mem_nhdsWithin] with z hz hz'
      have hzne : z ≠ z₀ := hz'
      exact (mul_eq_zero.1 hz).resolve_left (zpow_ne_zero n (sub_ne_zero.2 hzne))
    have hg0' : g =ᶠ[𝓝 z₀] fun _ => (0 : ℂ) :=
      (hg.continuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE continuousAt_const).1 hg0
    have hcoeff : ∀ j, taylorCoeffAt g z₀ j = 0 := fun j => by
      rw [taylorCoeffAt_congr hg0' j, taylorCoeffAt_const]
      simp
    rw [laurentCoeffAt_of_order_eq_top h₂]
    split_ifs with h
    · exact (hcoeff _).symm
    · rfl
  · have hE := (meromorphicOrderAt_ne_top_iff hf).1 h₂
    obtain ⟨h₁u, h₂u, h₃u⟩ := hE.choose_spec
    simp only [smul_eq_mul] at h₃u
    have hcomp := taylor_eq_of_two_presentations hg h₁u h₂u (hfg.symm.trans h₃u) k
    unfold laurentCoeffAt
    simp only [hf, reduceDIte, h₂]
    exact hcomp

theorem laurentCoeffAt_eq_zero_of_lt_order (h : (k : WithTop ℤ) < meromorphicOrderAt f z₀) :
    laurentCoeffAt f z₀ k = 0 := by
  by_cases hf : MeromorphicAt f z₀
  · by_cases h₂ : meromorphicOrderAt f z₀ = ⊤
    · exact laurentCoeffAt_of_order_eq_top h₂ k
    · obtain ⟨u, h₁u, h₂u, h₃u⟩ := (meromorphicOrderAt_ne_top_iff hf).1 h₂
      simp only [smul_eq_mul] at h₃u
      rw [laurentCoeffAt_of_eventuallyEq h₁u h₃u k, if_neg]
      intro hle
      rw [← WithTop.coe_untop₀_of_ne_top h₂] at h
      exact absurd (WithTop.coe_le_coe.2 hle) (not_le.2 h)
  · exact laurentCoeffAt_of_not_meromorphicAt hf k

/-- Congruence: Laurent coefficients live on the punctured germ. -/
theorem laurentCoeffAt_congr (hfg : f =ᶠ[𝓝[≠] z₀] g) (k : ℤ) :
    laurentCoeffAt f z₀ k = laurentCoeffAt g z₀ k := by
  by_cases hf : MeromorphicAt f z₀
  · by_cases h₂ : meromorphicOrderAt f z₀ = ⊤
    · rw [laurentCoeffAt_of_order_eq_top h₂,
        laurentCoeffAt_of_order_eq_top (by rwa [← meromorphicOrderAt_congr hfg])]
    · obtain ⟨u, h₁u, h₂u, h₃u⟩ := (meromorphicOrderAt_ne_top_iff hf).1 h₂
      simp only [smul_eq_mul] at h₃u
      rw [laurentCoeffAt_of_eventuallyEq h₁u h₃u k,
        laurentCoeffAt_of_eventuallyEq h₁u (hfg.symm.trans h₃u) k]
  · rw [laurentCoeffAt_of_not_meromorphicAt hf,
      laurentCoeffAt_of_not_meromorphicAt ((MeromorphicAt.meromorphicAt_congr hfg).not.1 hf)]

/-- At the order, the Laurent coefficient is mathlib's trailing coefficient. -/
theorem laurentCoeffAt_order (hf : MeromorphicAt f z₀) (h : meromorphicOrderAt f z₀ ≠ ⊤) :
    laurentCoeffAt f z₀ (meromorphicOrderAt f z₀).untop₀ = meromorphicTrailingCoeffAt f z₀ := by
  obtain ⟨u, h₁u, h₂u, h₃u⟩ := (meromorphicOrderAt_ne_top_iff hf).1 h
  have h₃u' := h₃u
  simp only [smul_eq_mul] at h₃u'
  rw [laurentCoeffAt_of_eventuallyEq h₁u h₃u' _, if_pos le_rfl, sub_self,
    AnalyticAt.meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE h₁u h₂u h₃u]
  rfl

theorem laurentCoeffAt_order_ne_zero (hf : MeromorphicAt f z₀)
    (h : meromorphicOrderAt f z₀ ≠ ⊤) :
    laurentCoeffAt f z₀ (meromorphicOrderAt f z₀).untop₀ ≠ 0 := by
  rw [laurentCoeffAt_order hf h]
  exact hf.meromorphicTrailingCoeffAt_ne_zero h

/-- For analytic `f` the Laurent coefficients are the Taylor coefficients. -/
theorem laurentCoeffAt_of_analyticAt (hf : AnalyticAt ℂ f z₀) (k : ℤ) :
    laurentCoeffAt f z₀ k = if 0 ≤ k then taylorCoeffAt f z₀ k.toNat else 0 := by
  have hpres : f =ᶠ[𝓝[≠] z₀] fun z => (z - z₀) ^ (0 : ℤ) * f z := by
    filter_upwards with z
    simp
  rw [laurentCoeffAt_of_eventuallyEq hf hpres k]
  simp only [sub_zero]

theorem laurentCoeffAt_zero_fun (k : ℤ) : laurentCoeffAt (fun _ => (0 : ℂ)) z₀ k = 0 :=
  laurentCoeffAt_of_order_eq_top
    (meromorphicOrderAt_eq_top_iff.2 (Eventually.of_forall fun _ => rfl)) k

/-- ℂ-additivity of Laurent coefficients on meromorphic germs. -/
theorem laurentCoeffAt_fun_add (hf : MeromorphicAt f z₀) (hg : MeromorphicAt g z₀) (k : ℤ) :
    laurentCoeffAt (fun z => f z + g z) z₀ k
      = laurentCoeffAt f z₀ k + laurentCoeffAt g z₀ k := by
  by_cases hft : meromorphicOrderAt f z₀ = ⊤
  · have hf0 : f =ᶠ[𝓝[≠] z₀] fun _ => (0 : ℂ) := meromorphicOrderAt_eq_top_iff.1 hft
    have hcongr : (fun z => f z + g z) =ᶠ[𝓝[≠] z₀] g := by
      filter_upwards [hf0] with z hz
      rw [hz, zero_add]
    rw [laurentCoeffAt_congr hcongr k, laurentCoeffAt_of_order_eq_top hft, zero_add]
  by_cases hgt : meromorphicOrderAt g z₀ = ⊤
  · have hg0 : g =ᶠ[𝓝[≠] z₀] fun _ => (0 : ℂ) := meromorphicOrderAt_eq_top_iff.1 hgt
    have hcongr : (fun z => f z + g z) =ᶠ[𝓝[≠] z₀] f := by
      filter_upwards [hg0] with z hz
      rw [hz, add_zero]
    rw [laurentCoeffAt_congr hcongr k, laurentCoeffAt_of_order_eq_top hgt, add_zero]
  -- both orders finite
  obtain ⟨u, h₁u, h₂u, h₃u⟩ := (meromorphicOrderAt_ne_top_iff hf).1 hft
  obtain ⟨v, h₁v, h₂v, h₃v⟩ := (meromorphicOrderAt_ne_top_iff hg).1 hgt
  simp only [smul_eq_mul] at h₃u h₃v
  set a := (meromorphicOrderAt f z₀).untop₀ with ha
  set b := (meromorphicOrderAt g z₀).untop₀ with hb
  set m := min a b with hm
  have hshift : ∀ (c : ℤ) (w : ℂ → ℂ), m ≤ c →
      (f =ᶠ[𝓝[≠] z₀] fun z => (z - z₀) ^ c * w z) →
      f =ᶠ[𝓝[≠] z₀] fun z => (z - z₀) ^ m * ((z - z₀) ^ (c - m).toNat * w z) := by
    intro c w hc hw
    filter_upwards [hw, self_mem_nhdsWithin] with z hz hz'
    have hzne : z ≠ z₀ := hz'
    have hwne : z - z₀ ≠ 0 := sub_ne_zero.2 hzne
    have hexp : (z - z₀) ^ m * (z - z₀) ^ ((c - m).toNat) = (z - z₀) ^ c := by
      rw [← zpow_natCast (z - z₀) (c - m).toNat, ← zpow_add₀ hwne]
      congr 1
      omega
    rw [hz, ← hexp, mul_assoc]
  have hu' := hshift a u (min_le_left a b) h₃u
  have hv' : g =ᶠ[𝓝[≠] z₀] fun z => (z - z₀) ^ m * ((z - z₀) ^ (b - m).toNat * v z) := by
    filter_upwards [h₃v, self_mem_nhdsWithin] with z hz hz'
    have hzne : z ≠ z₀ := hz'
    have hwne : z - z₀ ≠ 0 := sub_ne_zero.2 hzne
    have hexp : (z - z₀) ^ m * (z - z₀) ^ ((b - m).toNat) = (z - z₀) ^ b := by
      rw [← zpow_natCast (z - z₀) (b - m).toNat, ← zpow_add₀ hwne]
      congr 1
      omega
    rw [hz, ← hexp, mul_assoc]
  have hU : AnalyticAt ℂ (fun z => (z - z₀) ^ (a - m).toNat * u z) z₀ := by fun_prop
  have hV : AnalyticAt ℂ (fun z => (z - z₀) ^ (b - m).toNat * v z) z₀ := by fun_prop
  have hsum : (fun z => f z + g z) =ᶠ[𝓝[≠] z₀]
      fun z => (z - z₀) ^ m *
        ((z - z₀) ^ (a - m).toNat * u z + (z - z₀) ^ (b - m).toNat * v z) := by
    filter_upwards [hu', hv'] with z h1 h2
    rw [h1, h2, mul_add]
  have hW : AnalyticAt ℂ
      (fun z => (z - z₀) ^ (a - m).toNat * u z + (z - z₀) ^ (b - m).toNat * v z) z₀ := by
    fun_prop
  rw [laurentCoeffAt_of_eventuallyEq hW hsum k, laurentCoeffAt_of_eventuallyEq hU hu' k,
    laurentCoeffAt_of_eventuallyEq hV hv' k]
  split_ifs with hmk
  · rw [taylorCoeffAt_fun_add hU hV]
  · rw [add_zero]

theorem laurentCoeffAt_add (hf : MeromorphicAt f z₀) (hg : MeromorphicAt g z₀) (k : ℤ) :
    laurentCoeffAt (f + g) z₀ k = laurentCoeffAt f z₀ k + laurentCoeffAt g z₀ k :=
  laurentCoeffAt_fun_add hf hg k

theorem laurentCoeffAt_const_mul (c : ℂ) (k : ℤ) :
    laurentCoeffAt (fun z => c * f z) z₀ k = c * laurentCoeffAt f z₀ k := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp only [zero_mul]
    exact laurentCoeffAt_zero_fun k
  by_cases hf : MeromorphicAt f z₀
  · by_cases h₂ : meromorphicOrderAt f z₀ = ⊤
    · rw [laurentCoeffAt_of_order_eq_top h₂, mul_zero]
      apply laurentCoeffAt_of_order_eq_top
      rw [meromorphicOrderAt_eq_top_iff]
      filter_upwards [meromorphicOrderAt_eq_top_iff.1 h₂] with z hz
      rw [hz, mul_zero]
    · obtain ⟨u, h₁u, h₂u, h₃u⟩ := (meromorphicOrderAt_ne_top_iff hf).1 h₂
      simp only [smul_eq_mul] at h₃u
      have hcu : AnalyticAt ℂ (fun z => c * u z) z₀ := by fun_prop
      have hpres : (fun z => c * f z) =ᶠ[𝓝[≠] z₀]
          fun z => (z - z₀) ^ (meromorphicOrderAt f z₀).untop₀ * (c * u z) := by
        filter_upwards [h₃u] with z hz
        rw [hz]
        ring
      rw [laurentCoeffAt_of_eventuallyEq hcu hpres k,
        laurentCoeffAt_of_eventuallyEq h₁u h₃u k]
      split_ifs
      · rw [taylorCoeffAt_const_mul]
      · rw [mul_zero]
  · have hcf : ¬ MeromorphicAt (fun z => c * f z) z₀ := by
      intro hcon
      apply hf
      have h2 : MeromorphicAt (fun z => c⁻¹ * (c * f z)) z₀ :=
        (MeromorphicAt.const c⁻¹ z₀).mul hcon
      have h3 : (fun z => c⁻¹ * (c * f z)) = f := by
        funext z
        rw [inv_mul_cancel_left₀ hc]
      rwa [h3] at h2
    rw [laurentCoeffAt_of_not_meromorphicAt hf, laurentCoeffAt_of_not_meromorphicAt hcf,
      mul_zero]

theorem laurentCoeffAt_neg (k : ℤ) :
    laurentCoeffAt (fun z => -f z) z₀ k = -laurentCoeffAt f z₀ k := by
  simpa [neg_one_mul] using laurentCoeffAt_const_mul (f := f) (z₀ := z₀) (-1) k

theorem laurentCoeffAt_sub (hf : MeromorphicAt f z₀) (hg : MeromorphicAt g z₀) (k : ℤ) :
    laurentCoeffAt (fun z => f z - g z) z₀ k
      = laurentCoeffAt f z₀ k - laurentCoeffAt g z₀ k := by
  have hng : MeromorphicAt (fun z => -g z) z₀ := hg.neg
  have h2 := laurentCoeffAt_fun_add (g := fun z => -g z) hf hng k
  rw [laurentCoeffAt_neg] at h2
  have h1 : (fun z => f z - g z) = fun z => f z + -g z := by
    funext z
    ring
  rw [h1, h2, sub_eq_add_neg]

theorem laurentCoeffAt_fun_sum {ι : Type*} {s : Finset ι} {G : ι → ℂ → ℂ}
    (hG : ∀ i ∈ s, MeromorphicAt (G i) z₀) (k : ℤ) :
    laurentCoeffAt (fun z => ∑ i ∈ s, G i z) z₀ k = ∑ i ∈ s, laurentCoeffAt (G i) z₀ k := by
  classical
  induction s using Finset.induction with
  | empty => simpa using laurentCoeffAt_zero_fun (z₀ := z₀) k
  | insert a s ha ih =>
    have hstep : (fun z => ∑ i ∈ insert a s, G i z) = fun z => G a z + ∑ i ∈ s, G i z := by
      funext z
      rw [Finset.sum_insert ha]
    have hsum : MeromorphicAt (fun z => ∑ i ∈ s, G i z) z₀ :=
      MeromorphicAt.fun_sum fun i hi => hG i (Finset.mem_insert_of_mem hi)
    rw [hstep, Finset.sum_insert ha,
      laurentCoeffAt_fun_add (hG a (Finset.mem_insert_self a s)) hsum k,
      ih fun i hi => hG i (Finset.mem_insert_of_mem hi)]

@[simp] theorem laurentCoeffAt_zpow_monomial (m k : ℤ) :
    laurentCoeffAt (fun z => (z - z₀) ^ m) z₀ k = if k = m then 1 else 0 := by
  have hpres : (fun z => (z - z₀) ^ m) =ᶠ[𝓝[≠] z₀]
      fun z => (z - z₀) ^ m * (fun _ => (1 : ℂ)) z := by
    filter_upwards with z
    simp
  have h := laurentCoeffAt_of_eventuallyEq (g := fun _ => (1 : ℂ)) analyticAt_const hpres k
  rw [taylorCoeffAt_const] at h
  rw [h]
  split_ifs <;> first | rfl | omega

/-- Multiplying by `(· - z₀) ^ m` shifts Laurent coefficients. -/
theorem laurentCoeffAt_zpow_mul (hg : MeromorphicAt g z₀) (m k : ℤ) :
    laurentCoeffAt (fun z => (z - z₀) ^ m * g z) z₀ k = laurentCoeffAt g z₀ (k - m) := by
  by_cases h₂ : meromorphicOrderAt g z₀ = ⊤
  · rw [laurentCoeffAt_of_order_eq_top h₂]
    apply laurentCoeffAt_of_order_eq_top
    rw [meromorphicOrderAt_eq_top_iff]
    filter_upwards [meromorphicOrderAt_eq_top_iff.1 h₂] with z hz
    rw [hz, mul_zero]
  · obtain ⟨u, h₁u, h₂u, h₃u⟩ := (meromorphicOrderAt_ne_top_iff hg).1 h₂
    simp only [smul_eq_mul] at h₃u
    have hpres : (fun z => (z - z₀) ^ m * g z) =ᶠ[𝓝[≠] z₀]
        fun z => (z - z₀) ^ (m + (meromorphicOrderAt g z₀).untop₀) * u z := by
      filter_upwards [h₃u, self_mem_nhdsWithin] with z hz hz'
      have hzne : z ≠ z₀ := hz'
      have hw : z - z₀ ≠ 0 := sub_ne_zero.2 hzne
      rw [hz, ← mul_assoc, ← zpow_add₀ hw]
    rw [laurentCoeffAt_of_eventuallyEq h₁u hpres k,
      laurentCoeffAt_of_eventuallyEq h₁u h₃u (k - m)]
    split_ifs with h1 h2 h3
    · congr 1
      omega
    · omega
    · omega
    · rfl

/-- Vanishing principal tail ↔ analytic-after-repair (Mittag-Leffler-facing). -/
theorem forall_neg_laurentCoeffAt_eq_zero_iff (hf : MeromorphicAt f z₀) :
    (∀ k < 0, laurentCoeffAt f z₀ k = 0) ↔ 0 ≤ meromorphicOrderAt f z₀ := by
  constructor
  · intro h
    by_contra hlt
    rw [not_le] at hlt
    have hne : meromorphicOrderAt f z₀ ≠ ⊤ := hlt.ne_top
    have hto : (meromorphicOrderAt f z₀).untop₀ < 0 := by
      have hco := WithTop.coe_untop₀_of_ne_top hne
      rw [← hco] at hlt
      exact_mod_cast hlt
    exact laurentCoeffAt_order_ne_zero hf hne (h _ hto)
  · intro h k hk
    apply laurentCoeffAt_eq_zero_of_lt_order
    calc (k : WithTop ℤ) < (0 : WithTop ℤ) := by exact_mod_cast hk
      _ ≤ meromorphicOrderAt f z₀ := h

end RS
