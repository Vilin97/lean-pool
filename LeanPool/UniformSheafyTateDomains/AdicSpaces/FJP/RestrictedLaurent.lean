/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/
module


/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import Mathlib.Analysis.Normed.Ring.Ultra
public import Mathlib.Analysis.Normed.Group.Ultra
public import Mathlib.Analysis.Normed.Order.Lattice
public import Mathlib.Topology.Algebra.InfiniteSum.Ring
public import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Data.Real.Pointwise
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.Vendored.CoramRestrictedNorm
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.Vendored.CoramRestrictedIso
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.ExampleUnitDisc

/-!
# Restricted Laurent series `R⟨W, W⁻¹⟩` (finite-jet pinching, layer 𝓛)

Source: [FJP] = *Finite-jet pinching: a uniform strongly sheafy domain which is not stably
uniform* (16 July 2026), §1 (conventions) and Proposition 2.3. This file provides the radius-one
Laurent algebra `L = k⟨W, W⁻¹⟩` of [FJP] (1.4): ℤ-indexed series `∑_{a ∈ ℤ} c_a W^a` whose
coefficients tend to `0` along the cofinite filter, with the Gauss (sup) norm.

Over a base `R` that is a complete ultrametric normed commutative ring, `RestrictedLaurent R`
is a complete ultrametric normed commutative ring; when the base norm is multiplicative with
discrete value group (the [FJP] setting, `R = K = LaurentSeries F`), the Laurent–Gauss norm is
multiplicative ([FJP] Prop 2.3: "The Laurent Gauss norm on 𝒞 = L⟨Q⟩ is multiplicative"), the
norm is attained, and `W` is a norm-one unit.

The nonnegative-support subring recovers `K⟨W⟩` (`PowerSeries.Restricted K 1`) isometrically;
this is the inclusion `k⟨W⟩ ⊂ L` used throughout [FJP] §2.
-/

@[expose] public section

open Filter Topology
open scoped NNReal

namespace FiniteJet

/-- A **restricted Laurent series** over a normed ring `R`: a coefficient function on `ℤ`
whose norms tend to `0` along the cofinite filter ([FJP] §1: "restricted Laurent series";
the elements `∑_{a∈ℤ} c_a W^a` with `c_a → 0`). -/
structure RestrictedLaurent (R : Type*) [NormedCommRing R] where
  /-- The coefficient of `W^a`. -/
  coeff : ℤ → R
  /-- Coefficients tend to zero along the cofinite filter. -/
  tendsto_coeff : Tendsto (fun a => ‖coeff a‖) cofinite (𝓝 0)

namespace RestrictedLaurent

variable {R : Type*} [NormedCommRing R] [IsUltrametricDist R]

omit [IsUltrametricDist R] in
@[ext]
theorem ext {f g : RestrictedLaurent R} (h : ∀ a, f.coeff a = g.coeff a) : f = g := by
  cases f; cases g; simp only [mk.injEq]; exact funext h

/-! ### Decay helpers -/

omit [IsUltrametricDist R] in
/-- For every positive threshold, only finitely many coefficients reach it. -/
theorem finite_setOf_le_norm_coeff (f : RestrictedLaurent R) {ε : ℝ} (hε : 0 < ε) :
    {a : ℤ | ε ≤ ‖f.coeff a‖}.Finite := by
  have h := f.tendsto_coeff.eventually (eventually_lt_nhds hε (a := (0 : ℝ)))
  rw [Filter.eventually_cofinite] at h
  exact h.subset fun a ha => by simpa using not_lt.mpr ha

omit [IsUltrametricDist R] in
/-- The coefficients of a restricted Laurent series are uniformly bounded, by a bound `≥ 1`. -/
theorem exists_norm_coeff_le (f : RestrictedLaurent R) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ a, ‖f.coeff a‖ ≤ C := by
  classical
  have hfin : {a : ℤ | 1 ≤ ‖f.coeff a‖}.Finite := f.finite_setOf_le_norm_coeff one_pos
  refine ⟨max 1 (↑(hfin.toFinset.sup fun a => ‖f.coeff a‖₊) : ℝ), le_max_left _ _,
    fun a => ?_⟩
  by_cases ha : 1 ≤ ‖f.coeff a‖
  · refine le_max_of_le_right ?_
    rw [← coe_nnnorm]
    exact_mod_cast Finset.le_sup (f := fun a => ‖f.coeff a‖₊) (hfin.mem_toFinset.mpr ha)
  · exact le_max_of_le_left (not_le.mp ha).le

omit [IsUltrametricDist R] in
/-- Cofinite-tendsto-to-zero criterion via finiteness of super-level sets. -/
theorem tendsto_cofinite_zero_of_finite {ι : Type*} {F : ι → ℝ} (h0 : ∀ i, 0 ≤ F i)
    (h : ∀ ε : ℝ, 0 < ε → {i : ι | ε ≤ F i}.Finite) :
    Tendsto F cofinite (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  rw [Filter.eventually_cofinite]
  refine ((h (ε / 2) (by positivity)).subset ?_)
  intro i hi
  simp only [Set.mem_setOf_eq, Real.dist_eq, sub_zero, not_lt] at hi
  rw [abs_of_nonneg (h0 i)] at hi
  simp only [Set.mem_setOf_eq]
  linarith

/-! ### Additive and multiplicative structure

Multiplication is Cauchy convolution: `(f * g).coeff m = ∑' a, f.coeff a * g.coeff (m - a)`.
The sum converges because the base is complete and nonarchimedean and the terms tend to `0`
along cofinite ([FJP] §1 and Prop 2.3 use this implicitly via the support description (1.8)). -/

/-- The zero series. -/
instance : Zero (RestrictedLaurent R) :=
  ⟨⟨fun _ => 0, by simp only [norm_zero]; exact tendsto_const_nhds⟩⟩

/-- The one series (coefficient `1` at `0`). -/
instance : One (RestrictedLaurent R) :=
  ⟨⟨fun a => if a = 0 then 1 else 0, by
    refine tendsto_nhds_of_eventually_eq
      ((Filter.eventually_cofinite_ne (0 : ℤ)).mono fun a ha => ?_)
    simp [if_neg ha]⟩⟩

/-- Coefficientwise addition. -/
instance : Add (RestrictedLaurent R) :=
  ⟨fun f g => ⟨fun a => f.coeff a + g.coeff a, by
    have h := f.tendsto_coeff.add g.tendsto_coeff
    rw [add_zero] at h
    refine squeeze_zero (fun a => norm_nonneg _) (fun a => norm_add_le _ _) h⟩⟩

/-- Coefficientwise negation. -/
instance : Neg (RestrictedLaurent R) :=
  ⟨fun f => ⟨fun a => -f.coeff a, by simpa using f.tendsto_coeff⟩⟩

omit [IsUltrametricDist R] in
@[simp] theorem coeff_zero (a : ℤ) : (0 : RestrictedLaurent R).coeff a = 0 := rfl

omit [IsUltrametricDist R] in
@[simp] theorem coeff_one (a : ℤ) :
    (1 : RestrictedLaurent R).coeff a = if a = 0 then 1 else 0 := rfl

omit [IsUltrametricDist R] in
@[simp] theorem coeff_add (f g : RestrictedLaurent R) (a : ℤ) :
    (f + g).coeff a = f.coeff a + g.coeff a := rfl

omit [IsUltrametricDist R] in
@[simp] theorem coeff_neg (f : RestrictedLaurent R) (a : ℤ) : (-f).coeff a = -f.coeff a := rfl

/-- The monomial `c · W^a`. -/
def single (a : ℤ) (c : R) : RestrictedLaurent R :=
  ⟨fun b => if b = a then c else 0, by
    refine tendsto_nhds_of_eventually_eq
      ((Filter.eventually_cofinite_ne a).mono fun b hb => ?_)
    simp [if_neg hb]⟩

omit [IsUltrametricDist R] in
@[simp] theorem coeff_single (a b : ℤ) (c : R) :
    (single a c).coeff b = if b = a then c else 0 := rfl

section Complete

variable [CompleteSpace R]

omit [IsUltrametricDist R] [CompleteSpace R] in
/-- Termwise norm decay of the convolution family, for a fixed target index. -/
theorem tendsto_conv_term (f g : RestrictedLaurent R) (m : ℤ) :
    Tendsto (fun a : ℤ => ‖f.coeff a * g.coeff (m - a)‖) cofinite (𝓝 0) := by
  obtain ⟨Cg, hCg1, hCg⟩ := g.exists_norm_coeff_le
  have hbound : ∀ a : ℤ, ‖f.coeff a * g.coeff (m - a)‖ ≤ ‖f.coeff a‖ * Cg := fun a =>
    (norm_mul_le _ _).trans (by
      have := hCg (m - a)
      exact mul_le_mul_of_nonneg_left this (norm_nonneg _))
  have hlim : Tendsto (fun a : ℤ => ‖f.coeff a‖ * Cg) cofinite (𝓝 0) := by
    simpa using f.tendsto_coeff.mul_const Cg
  exact squeeze_zero (fun a => norm_nonneg _) hbound hlim

/-- The convolution defining `f * g` is summable (complete nonarchimedean base, terms → 0). -/
theorem summable_mul_coeff (f g : RestrictedLaurent R) (m : ℤ) :
    Summable (fun a : ℤ => f.coeff a * g.coeff (m - a)) := by
  rw [NonarchimedeanAddGroup.summable_iff_tendsto_cofinite_zero]
  exact tendsto_zero_iff_norm_tendsto_zero.mpr (tendsto_conv_term f g m)

/-- Convolution multiplication (requires a complete base for the `tsum`). -/
noncomputable instance : Mul (RestrictedLaurent R) :=
  ⟨fun f g => ⟨fun m => ∑' a : ℤ, f.coeff a * g.coeff (m - a), by
    obtain ⟨Cf, hCf1, hCf⟩ := f.exists_norm_coeff_le
    obtain ⟨Cg, hCg1, hCg⟩ := g.exists_norm_coeff_le
    refine tendsto_cofinite_zero_of_finite (fun m => norm_nonneg _) fun ε hε => ?_
    -- outside the sumset of the two super-level sets, every convolution term is ≤ ε/2
    have hS₁ : {a : ℤ | ε / 2 / Cg ≤ ‖f.coeff a‖}.Finite :=
      f.finite_setOf_le_norm_coeff (by positivity)
    have hS₂ : {b : ℤ | ε / 2 / Cf ≤ ‖g.coeff b‖}.Finite :=
      g.finite_setOf_le_norm_coeff (by positivity)
    refine (hS₁.image2 (· + ·) hS₂).subset fun m hm => ?_
    simp only [Set.mem_setOf_eq] at hm
    by_contra hnot
    -- every term of the convolution at such `m` has norm ≤ ε/2
    have hterm : ∀ a : ℤ, ‖f.coeff a * g.coeff (m - a)‖ ≤ ε / 2 := by
      intro a
      by_cases ha : ε / 2 / Cg ≤ ‖f.coeff a‖
      · -- then `m - a` is not in `S₂`
        have hb : ¬ ε / 2 / Cf ≤ ‖g.coeff (m - a)‖ := fun hb =>
          hnot ⟨a, ha, m - a, hb, by ring⟩
        push Not at hb
        calc ‖f.coeff a * g.coeff (m - a)‖ ≤ ‖f.coeff a‖ * ‖g.coeff (m - a)‖ :=
              norm_mul_le _ _
          _ ≤ Cf * ‖g.coeff (m - a)‖ :=
              mul_le_mul_of_nonneg_right (hCf a) (norm_nonneg _)
          _ ≤ Cf * (ε / 2 / Cf) :=
              mul_le_mul_of_nonneg_left hb.le (by positivity)
          _ = ε / 2 := by field_simp
      · push Not at ha
        calc ‖f.coeff a * g.coeff (m - a)‖ ≤ ‖f.coeff a‖ * ‖g.coeff (m - a)‖ :=
              norm_mul_le _ _
          _ ≤ ‖f.coeff a‖ * Cg :=
              mul_le_mul_of_nonneg_left (hCg _) (norm_nonneg _)
          _ ≤ (ε / 2 / Cg) * Cg :=
              mul_le_mul_of_nonneg_right ha.le (by positivity)
          _ = ε / 2 := by field_simp
    -- nonarchimedean: the whole sum then has norm ≤ ε/2 < ε, contradicting `ε ≤ ‖…‖`
    have hle : ‖∑' a : ℤ, f.coeff a * g.coeff (m - a)‖ ≤ ε / 2 :=
      IsUltrametricDist.norm_tsum_le_of_forall_le hterm
    linarith⟩⟩

/-- The doubly-indexed family behind associativity of the convolution is summable over
`ℤ × ℤ` (nonarchimedean criterion; only finitely many pairs have both an `f`- and a
`g`-coefficient large). -/
theorem summable_conv_triple (f g h : RestrictedLaurent R) (m : ℤ) :
    Summable (fun p : ℤ × ℤ => f.coeff p.2 * g.coeff (p.1 - p.2) * h.coeff (m - p.1)) := by
  rw [NonarchimedeanAddGroup.summable_iff_tendsto_cofinite_zero]
  refine tendsto_zero_iff_norm_tendsto_zero.mpr
    (tendsto_cofinite_zero_of_finite (fun p => norm_nonneg _) fun ε hε => ?_)
  obtain ⟨Cf, hCf1, hCf⟩ := f.exists_norm_coeff_le
  obtain ⟨Cg, hCg1, hCg⟩ := g.exists_norm_coeff_le
  obtain ⟨Ch, hCh1, hCh⟩ := h.exists_norm_coeff_le
  have hS₁ : {a : ℤ | ε / (Cg * Ch) ≤ ‖f.coeff a‖}.Finite :=
    f.finite_setOf_le_norm_coeff (by positivity)
  have hS₂ : {c : ℤ | ε / (Cf * Ch) ≤ ‖g.coeff c‖}.Finite :=
    g.finite_setOf_le_norm_coeff (by positivity)
  refine ((hS₁.prod hS₂).image fun q : ℤ × ℤ => ((q.1 + q.2 : ℤ), q.1)).subset fun p hp => ?_
  simp only [Set.mem_setOf_eq] at hp
  have hnorm : ‖f.coeff p.2 * g.coeff (p.1 - p.2) * h.coeff (m - p.1)‖ ≤
      ‖f.coeff p.2‖ * ‖g.coeff (p.1 - p.2)‖ * ‖h.coeff (m - p.1)‖ :=
    (norm_mul_le _ _).trans
      (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
  refine ⟨(p.2, p.1 - p.2), ⟨?_, ?_⟩, by simp⟩
  · -- `ε/(Cg·Ch) ≤ ‖f.coeff p.2‖`
    have : ε ≤ ‖f.coeff p.2‖ * Cg * Ch := by
      refine hp.trans (hnorm.trans ?_)
      have h1 : ‖f.coeff p.2‖ * ‖g.coeff (p.1 - p.2)‖ ≤ ‖f.coeff p.2‖ * Cg :=
        mul_le_mul_of_nonneg_left (hCg _) (norm_nonneg _)
      exact (mul_le_mul_of_nonneg_right h1 (norm_nonneg _)).trans
        (mul_le_mul_of_nonneg_left (hCh _) (by positivity))
    rw [Set.mem_setOf_eq, div_le_iff₀ (by positivity)]
    linarith [this, mul_assoc ‖f.coeff p.2‖ Cg Ch]
  · -- `ε/(Cf·Ch) ≤ ‖g.coeff (p.1 − p.2)‖`
    have : ε ≤ Cf * ‖g.coeff (p.1 - p.2)‖ * Ch := by
      refine hp.trans (hnorm.trans ?_)
      have h1 : ‖f.coeff p.2‖ * ‖g.coeff (p.1 - p.2)‖ ≤ Cf * ‖g.coeff (p.1 - p.2)‖ :=
        mul_le_mul_of_nonneg_right (hCf _) (norm_nonneg _)
      exact (mul_le_mul_of_nonneg_right h1 (norm_nonneg _)).trans
        (mul_le_mul_of_nonneg_left (hCh _) (by positivity))
    rw [Set.mem_setOf_eq, div_le_iff₀ (by positivity)]
    nlinarith [norm_nonneg (g.coeff (p.1 - p.2))]

theorem coeff_mul (f g : RestrictedLaurent R) (m : ℤ) :
    (f * g).coeff m = ∑' a : ℤ, f.coeff a * g.coeff (m - a) := rfl

/-- `RestrictedLaurent R` is a commutative ring under coefficientwise addition and Cauchy
convolution. -/
noncomputable instance : CommRing (RestrictedLaurent R) where
  add := (· + ·)
  add_assoc f g h := by ext a; simp [add_assoc]
  zero := 0
  zero_add f := by ext a; simp
  add_zero f := by ext a; simp
  add_comm f g := by ext a; simp [add_comm]
  mul := (· * ·)
  left_distrib f g h := by
    ext m
    simp only [coeff_mul, coeff_add]
    rw [← (summable_mul_coeff f g m).tsum_add (summable_mul_coeff f h m)]
    exact tsum_congr fun a => by rw [mul_add]
  right_distrib f g h := by
    ext m
    simp only [coeff_mul, coeff_add]
    rw [← (summable_mul_coeff f h m).tsum_add (summable_mul_coeff g h m)]
    exact tsum_congr fun a => by rw [add_mul]
  zero_mul f := by ext m; simp [coeff_mul]
  mul_zero f := by ext m; simp [coeff_mul]
  mul_assoc f g h := by
    ext m
    have hF := summable_conv_triple f g h m
    -- shear equivalence `(a, c) ↦ (a + c, a)` on `ℤ × ℤ`
    let e : ℤ × ℤ ≃ ℤ × ℤ :=
      ⟨fun q => (q.1 + q.2, q.1), fun p => (p.2, p.1 - p.2),
        fun q => by simp, fun p => by simp⟩
    have hG : Summable (fun q : ℤ × ℤ =>
        f.coeff q.1 * (g.coeff q.2 * h.coeff (m - q.1 - q.2))) := by
      refine (e.summable_iff.mpr hF).congr fun q => ?_
      show f.coeff (e q).2 * g.coeff ((e q).1 - (e q).2) * h.coeff (m - (e q).1) = _
      simp only [e, Equiv.coe_fn_mk, add_sub_cancel_left]
      rw [mul_assoc, sub_add_eq_sub_sub]
    have key : ((f * g) * h).coeff m =
        ∑' p : ℤ × ℤ, f.coeff p.2 * g.coeff (p.1 - p.2) * h.coeff (m - p.1) := by
      rw [coeff_mul,
        hF.tsum_prod' fun b => ((summable_mul_coeff f g b).mul_right (h.coeff (m - b)))]
      exact tsum_congr fun b => by
        rw [coeff_mul, ← (summable_mul_coeff f g b).tsum_mul_right (h.coeff (m - b))]
    have key2 : (f * (g * h)).coeff m =
        ∑' q : ℤ × ℤ, f.coeff q.1 * (g.coeff q.2 * h.coeff (m - q.1 - q.2)) := by
      rw [coeff_mul,
        hG.tsum_prod' fun a => ((summable_mul_coeff g h (m - a)).congr
          (fun c => by rw [sub_sub])).mul_left (f.coeff a)]
      exact tsum_congr fun a => by
        rw [coeff_mul, ← (summable_mul_coeff g h (m - a)).tsum_mul_left (f.coeff a)]
    rw [key, key2, ← Equiv.tsum_eq e]
    exact tsum_congr fun q => by
      show f.coeff (e q).2 * g.coeff ((e q).1 - (e q).2) * h.coeff (m - (e q).1) = _
      simp only [e, Equiv.coe_fn_mk, add_sub_cancel_left]
      rw [mul_assoc, sub_add_eq_sub_sub]
  one := 1
  one_mul f := by
    ext m
    rw [coeff_mul, tsum_eq_single 0 (fun a ha => by simp [if_neg ha])]
    simp
  mul_one f := by
    ext m
    rw [coeff_mul, tsum_eq_single m (fun a ha => by
      have : ¬ m - a = 0 := fun h => ha (by omega)
      simp [if_neg this])]
    simp
  neg := Neg.neg
  neg_add_cancel f := by ext a; simp
  mul_comm f g := by
    ext m
    rw [coeff_mul, coeff_mul, ← (Equiv.subLeft m).tsum_eq]
    exact tsum_congr fun a => by simp [mul_comm]
  nsmul := nsmulRec
  zsmul := zsmulRec

@[simp] theorem coeff_sub (f g : RestrictedLaurent R) (a : ℤ) :
    (f - g).coeff a = f.coeff a - g.coeff a := by
  show (f + -g).coeff a = _
  rw [coeff_add, coeff_neg, sub_eq_add_neg]

/-! ### Monomials and the algebra structure -/

theorem single_mul_single (a b : ℤ) (c d : R) :
    single a c * single b d = single (a + b) (c * d) := by
  ext m
  rw [coeff_mul, tsum_eq_single a (fun x hx => by simp [coeff_single, if_neg hx])]
  simp only [coeff_single]
  by_cases hm : m = a + b
  · have : m - a = b := by omega
    simp [hm]
  · have : ¬ m - a = b := fun h => hm (by omega)
    simp [if_neg this, if_neg hm]

@[simp] theorem single_zero_one : (single 0 (1 : R)) = 1 := by
  ext a; simp [coeff_single, coeff_one]

/-- The scalar embedding `R → RestrictedLaurent R` as `single 0`. -/
noncomputable def C : R →+* RestrictedLaurent R where
  toFun c := single 0 c
  map_one' := single_zero_one
  map_mul' c d := by rw [single_mul_single, add_zero]
  map_zero' := by ext a; simp [coeff_single]
  map_add' c d := by ext a; simp [coeff_single]; split <;> simp

noncomputable instance : Algebra R (RestrictedLaurent R) :=
  (C (R := R)).toAlgebra

/-- The variable `W` (norm-one monomial at exponent `1`). -/
noncomputable def W : RestrictedLaurent R := single 1 1

/-- `W` is a unit, with inverse the monomial at exponent `-1` ([FJP] §1.4: "both `W` and
`W⁻¹` are power-bounded"). -/
noncomputable def Wu : (RestrictedLaurent R)ˣ where
  val := single 1 1
  inv := single (-1) 1
  val_inv := by rw [single_mul_single]; norm_num
  inv_val := by rw [single_mul_single]; norm_num

end Complete

/-! ### The Gauss (sup) norm

[FJP] (1.8): "An element is a series `∑_{(a,b)∈S} c_{a,b} W^a Q^b` such that, for every ε > 0,
only finitely many coefficients have `|c_{a,b}| ≥ ε`; its norm is `sup |c_{a,b}|`." Here the
univariate (`Q`-free) case: `‖f‖ = ⨆ a, ‖f.coeff a‖`, attained because the coefficient family
is restricted. -/

/-- The sup norm of a restricted Laurent series. -/
noncomputable def gaussNorm (f : RestrictedLaurent R) : ℝ := ⨆ a : ℤ, ‖f.coeff a‖

omit [IsUltrametricDist R] in
theorem norm_coeff_le_gaussNorm (f : RestrictedLaurent R) (a : ℤ) :
    ‖f.coeff a‖ ≤ gaussNorm f :=
  le_ciSup f.tendsto_coeff.bddAbove_range_of_cofinite a

theorem gaussNorm_nonneg (f : RestrictedLaurent R) : 0 ≤ gaussNorm f :=
  (norm_nonneg _).trans (norm_coeff_le_gaussNorm f 0)

/-- The sup defining the Gauss norm is attained ([FJP] Prop 2.3: "the coefficient family of a
restricted Laurent series tends to zero, so its nonzero coefficient supremum is attained"). -/
theorem exists_gaussNorm_eq (f : RestrictedLaurent R) (hf : f ≠ 0) :
    ∃ a : ℤ, gaussNorm f = ‖f.coeff a‖ ∧ f.coeff a ≠ 0 := by
  have hne : ∃ a₀, f.coeff a₀ ≠ 0 := by
    by_contra h
    push Not at h
    exact hf (ext fun a => by rw [h a, coeff_zero])
  obtain ⟨a₀, ha₀⟩ := hne
  have hpos : 0 < ‖f.coeff a₀‖ := norm_pos_iff.mpr ha₀
  have hS : {a : ℤ | ‖f.coeff a₀‖ ≤ ‖f.coeff a‖}.Finite := f.finite_setOf_le_norm_coeff hpos
  obtain ⟨a, haS, hamax⟩ :=
    Set.exists_max_image _ (fun a => ‖f.coeff a‖) hS
      ⟨a₀, show ‖f.coeff a₀‖ ≤ ‖f.coeff a₀‖ from le_rfl⟩
  refine ⟨a, le_antisymm (ciSup_le fun b => ?_) (norm_coeff_le_gaussNorm f a), ?_⟩
  · by_cases hb : ‖f.coeff a₀‖ ≤ ‖f.coeff b‖
    · exact hamax b hb
    · exact (not_le.mp hb).le.trans haS
  · exact norm_pos_iff.mp (lt_of_lt_of_le hpos haS)

/-- The Gauss norm as a `RingNorm` (submultiplicative, ultrametric-compatible). -/
noncomputable def isRingNorm [CompleteSpace R] [NormOneClass R] :
    RingNorm (RestrictedLaurent R) where
  toFun := gaussNorm
  map_zero' := by
    have : ∀ a : ℤ, ‖(0 : RestrictedLaurent R).coeff a‖ = 0 := fun a => by simp
    simp only [gaussNorm, this, ciSup_const]
  add_le' f g := by
    refine ciSup_le fun a => (norm_add_le _ _).trans ?_
    exact add_le_add (norm_coeff_le_gaussNorm f a) (norm_coeff_le_gaussNorm g a)
  neg' f := by simp only [gaussNorm, coeff_neg, norm_neg]
  mul_le' f g := by
    refine ciSup_le fun m => ?_
    show ‖(f * g).coeff m‖ ≤ gaussNorm f * gaussNorm g
    rw [coeff_mul]
    refine IsUltrametricDist.norm_tsum_le_of_forall_le fun a => (norm_mul_le _ _).trans ?_
    exact mul_le_mul (norm_coeff_le_gaussNorm f a) (norm_coeff_le_gaussNorm g _)
      (norm_nonneg _) (gaussNorm_nonneg f)
  eq_zero_of_map_eq_zero' f hf := by
    refine ext fun a => norm_le_zero_iff.mp ?_
    exact hf ▸ norm_coeff_le_gaussNorm f a

/-- `RestrictedLaurent R` is a normed ring under the Gauss norm. -/
noncomputable instance [CompleteSpace R] [NormOneClass R] :
    NormedCommRing (RestrictedLaurent R) where
  toNormedRing := RingNorm.toNormedRing (isRingNorm (R := R))
  mul_comm := mul_comm

theorem norm_def [CompleteSpace R] [NormOneClass R] (f : RestrictedLaurent R) :
    ‖f‖ = gaussNorm f := rfl

@[simp] theorem norm_single [CompleteSpace R] [NormOneClass R] (a : ℤ) (c : R) :
    ‖single a c‖ = ‖c‖ := by
  rw [norm_def]
  refine le_antisymm (ciSup_le fun b => ?_) ?_
  · rcases eq_or_ne b a with rfl | hb
    · simp [coeff_single]
    · simp only [coeff_single, if_neg hb, norm_zero]
      exact norm_nonneg c
  · have h := norm_coeff_le_gaussNorm (single a c) a
    simpa using h

@[simp] theorem norm_W [CompleteSpace R] [NormOneClass R] :
    ‖(Wu (R := R)).val‖ = 1 := by
  show ‖single 1 (1 : R)‖ = 1
  rw [norm_single, norm_one]

@[simp] theorem norm_W_inv [CompleteSpace R] [NormOneClass R] :
    ‖((Wu (R := R))⁻¹ : (RestrictedLaurent R)ˣ).val‖ = 1 := by
  show ‖single (-1) (1 : R)‖ = 1
  rw [norm_single, norm_one]

/-- The Gauss norm is ultrametric. -/
instance [CompleteSpace R] [NormOneClass R] : IsUltrametricDist (RestrictedLaurent R) := by
  refine IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm fun f g => ?_
  refine ciSup_le fun a => (IsUltrametricDist.norm_add_le_max _ _).trans ?_
  exact max_le_max (norm_coeff_le_gaussNorm f a) (norm_coeff_le_gaussNorm g a)

theorem coeff_Wu_mul [CompleteSpace R] (f : RestrictedLaurent R) (m : ℤ) :
    ((Wu (R := R)).val * f).coeff m = f.coeff (m - 1) := by
  show (single 1 1 * f).coeff m = _
  rw [coeff_mul, tsum_eq_single 1 (fun b hb => by simp [coeff_single, if_neg hb])]
  simp [coeff_single]

/-- Multiplication by `W` is an isometry (used in [FJP] Prop 3.1: `‖W^{-n} y‖ = ‖y‖`). -/
theorem norm_W_mul [CompleteSpace R] [NormOneClass R] (f : RestrictedLaurent R) :
    ‖(Wu (R := R)).val * f‖ = ‖f‖ := by
  rw [norm_def, norm_def]
  refine le_antisymm (ciSup_le fun m => ?_) (ciSup_le fun a => ?_)
  · rw [show ((Wu (R := R)).val * f).coeff m = f.coeff (m - 1) from coeff_Wu_mul f m]
    exact norm_coeff_le_gaussNorm f _
  · have h := norm_coeff_le_gaussNorm ((Wu (R := R)).val * f) (a + 1)
    rw [coeff_Wu_mul] at h
    simpa using h

/-- Completeness of the restricted Laurent ring over a complete base ([FJP] §1: Banach
direct sums / restricted series are complete). -/
instance [CompleteSpace R] [NormOneClass R] : CompleteSpace (RestrictedLaurent R) := by
  refine Metric.complete_of_cauchySeq_tendsto fun u hu => ?_
  -- Step 1: the Gauss norm dominates each coefficient of a difference.
  have coeff_le : ∀ (f g : RestrictedLaurent R) (n : ℤ),
      ‖f.coeff n - g.coeff n‖ ≤ ‖f - g‖ := fun f g n => by
    have heq : f.coeff n - g.coeff n = (f - g).coeff n := by
      show _ = (f + -g).coeff n
      rw [coeff_add, coeff_neg, sub_eq_add_neg]
    rw [heq]
    exact norm_coeff_le_gaussNorm (f - g) n
  -- Step 2: coefficientwise Cauchy.
  have coeff_cauchy : ∀ n : ℤ, CauchySeq fun i => (u i).coeff n := fun n => by
    refine Metric.cauchySeq_iff.mpr fun ε hε => ?_
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hu ε hε
    refine ⟨N, fun i hi j hj => ?_⟩
    rw [dist_eq_norm]
    have h_uij : ‖u i - u j‖ < ε := by
      have := hN i hi j hj; rwa [dist_eq_norm] at this
    exact (coeff_le (u i) (u j) n).trans_lt h_uij
  -- Step 3: pointwise limits.
  choose a ha using fun n => cauchySeq_tendsto_of_complete (coeff_cauchy n)
  -- Step 4: uniform-in-`n` convergence.
  have unif_conv : ∀ ε > (0 : ℝ), ∃ N, ∀ i ≥ N, ∀ n, ‖(u i).coeff n - a n‖ ≤ ε := by
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hu ε hε
    refine ⟨N, fun i hi n => ?_⟩
    have h_lim : Tendsto (fun j => ‖(u i).coeff n - (u j).coeff n‖) atTop
        (𝓝 ‖(u i).coeff n - a n‖) := (tendsto_const_nhds.sub (ha n)).norm
    refine le_of_tendsto h_lim ?_
    filter_upwards [Filter.eventually_ge_atTop N] with j hj
    have h_dist := hN i hi j hj
    rw [dist_eq_norm] at h_dist
    exact ((coeff_le (u i) (u j) n).trans_lt h_dist).le
  -- Step 5: the pointwise limit is restricted.
  have hf : Tendsto (fun n => ‖a n‖) cofinite (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨N₁, hN₁⟩ := unif_conv (ε / 3) (by linarith)
    have h_uN1 := (u N₁).tendsto_coeff
    rw [Metric.tendsto_nhds] at h_uN1
    have h_uN1' := h_uN1 (ε / 3) (by linarith)
    rw [Filter.eventually_cofinite] at h_uN1' ⊢
    refine h_uN1'.subset fun n hn => ?_
    simp only [Set.mem_setOf_eq, dist_zero_right, Real.norm_eq_abs, not_lt,
      abs_of_nonneg (norm_nonneg _)] at hn ⊢
    have h1 : ‖(u N₁).coeff n - a n‖ ≤ ε / 3 := hN₁ N₁ le_rfl n
    have h2 : ‖a n‖ ≤ ‖(u N₁).coeff n - a n‖ + ‖(u N₁).coeff n‖ := by
      calc ‖a n‖ = ‖a n - (u N₁).coeff n + (u N₁).coeff n‖ := by rw [sub_add_cancel]
        _ ≤ ‖a n - (u N₁).coeff n‖ + ‖(u N₁).coeff n‖ := norm_add_le _ _
        _ = ‖(u N₁).coeff n - a n‖ + ‖(u N₁).coeff n‖ := by rw [norm_sub_rev]
    by_contra hcon
    push Not at hcon
    have : ‖(u N₁).coeff n‖ < ε / 3 := hcon.trans_le (by linarith)
    linarith [hn, this]
  set F : RestrictedLaurent R := ⟨a, hf⟩ with hF
  -- Step 6: `u → F` in the Gauss norm.
  refine ⟨F, Metric.tendsto_atTop.mpr fun ε hε => ?_⟩
  obtain ⟨N, hN⟩ := unif_conv (ε / 2) (by linarith)
  refine ⟨N, fun i hi => ?_⟩
  rw [dist_eq_norm]
  have hcoeff : ∀ n, ‖(u i - F).coeff n‖ ≤ ε / 2 := fun n => by
    have heq : (u i - F).coeff n = (u i).coeff n - a n := by
      show (u i + -F).coeff n = _
      rw [coeff_add, coeff_neg, sub_eq_add_neg]
    rw [heq]
    exact hN i hi n
  calc ‖u i - F‖ ≤ ε / 2 := ciSup_le hcoeff
    _ < ε := by linarith

/-- Coefficient functionals are `1`-Lipschitz, hence continuous. -/
theorem continuous_coeff [CompleteSpace R] [NormOneClass R] (a : ℤ) :
    Continuous fun f : RestrictedLaurent R => f.coeff a := by
  refine (LipschitzWith.of_dist_le_mul (K := 1) fun f g => ?_).continuous
  rw [NNReal.coe_one, one_mul, dist_eq_norm, dist_eq_norm, ← coeff_sub]
  exact norm_coeff_le_gaussNorm (f - g) a

/-! ### Multiplicativity over a discretely valued field

[FJP] Prop 2.3 (verbatim): "The Laurent Gauss norm on 𝒞 = L⟨Q⟩ is multiplicative. Indeed, the
coefficient family of a restricted Laurent series tends to zero, so its nonzero coefficient
supremum is attained. Since every nonzero coefficient norm belongs to `|k^×|`, so does every
nonzero Gauss norm. We may therefore scale two nonzero elements to norm one. Their reductions
are nonzero Laurent polynomials in `k̃[W, W⁻¹, Q]` … Their product remains nonzero because this
Laurent polynomial ring is a domain."  This file proves the `Q`-free (univariate Laurent) case;
`FiniteJetRings.lean` derives the `L⟨Q⟩` case over the base `𝓛`. -/

section Field

variable {K : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

omit [CompleteSpace K] in
/-- A nonarchimedean sum whose terms all lie strictly below a positive bound stays strictly
below it (the sup of a restricted family is attained, so the strict bound survives). -/
theorem norm_tsum_lt_of_forall_lt {F : ℤ → K}
    (hF : Tendsto (fun a => ‖F a‖) cofinite (𝓝 0)) {B : ℝ} (hB : 0 < B)
    (h : ∀ a, ‖F a‖ < B) : ‖∑' a : ℤ, F a‖ < B := by
  classical
  have hfin : {a : ℤ | B / 2 ≤ ‖F a‖}.Finite := by
    have hev := hF.eventually (eventually_lt_nhds (show (0 : ℝ) < B / 2 by positivity))
    rw [Filter.eventually_cofinite] at hev
    exact hev.subset fun a ha => by simpa using not_lt.mpr ha
  rcases hfin.toFinset.eq_empty_or_nonempty with hemp | hne
  · -- all terms < B/2
    have hall : ∀ a, ‖F a‖ ≤ B / 2 := fun a => by
      by_contra hcon
      exact (Finset.eq_empty_iff_forall_notMem.mp hemp a)
        (hfin.mem_toFinset.mpr (not_lt.mp fun hlt => hcon hlt.le))
    exact (IsUltrametricDist.norm_tsum_le_of_forall_le hall).trans_lt (by linarith)
  · obtain ⟨a₀, ha₀S, ha₀max⟩ := Finset.exists_max_image _ (fun a => ‖F a‖) hne
    have hbound : ∀ a, ‖F a‖ ≤ max ‖F a₀‖ (B / 2) := fun a => by
      by_cases haS : a ∈ hfin.toFinset
      · exact le_max_of_le_left (ha₀max a haS)
      · refine le_max_of_le_right ?_
        have hnot : ¬ B / 2 ≤ ‖F a‖ := fun hle => haS (hfin.mem_toFinset.mpr hle)
        exact (not_le.mp hnot).le
    refine (IsUltrametricDist.norm_tsum_le_of_forall_le hbound).trans_lt ?_
    exact max_lt (h a₀) (by linarith)

/-- Norm multiplicativity for restricted Laurent series over any complete nonarchimedean
field ([FJP] Prop 2.3 states this for a discretely valued base, but the minimal-achiever
proof below needs no discreteness of the value group). -/
theorem norm_mul_eq (f g : RestrictedLaurent K) : ‖f * g‖ = ‖f‖ * ‖g‖ := by
  classical
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  rcases eq_or_ne g 0 with rfl | hg
  · simp
  -- attained norms and their minimal achievers
  obtain ⟨af, hafeq, hafne⟩ := exists_gaussNorm_eq f hf
  obtain ⟨ag, hageq, hagne⟩ := exists_gaussNorm_eq g hg
  have hNf : (0 : ℝ) < ‖f‖ := by
    rw [norm_def, hafeq]; exact norm_pos_iff.mpr hafne
  have hNg : (0 : ℝ) < ‖g‖ := by
    rw [norm_def, hageq]; exact norm_pos_iff.mpr hagne
  have hAf : {a : ℤ | ‖f.coeff a‖ = ‖f‖}.Finite :=
    (f.finite_setOf_le_norm_coeff hNf).subset fun a ha => by
      rw [Set.mem_setOf_eq] at ha ⊢; rw [ha]
  have hAg : {a : ℤ | ‖g.coeff a‖ = ‖g‖}.Finite :=
    (g.finite_setOf_le_norm_coeff hNg).subset fun a ha => by
      rw [Set.mem_setOf_eq] at ha ⊢; rw [ha]
  obtain ⟨a₁, ha₁A, ha₁min⟩ := Set.exists_min_image _ (fun a : ℤ => a) hAf
    ⟨af, by rw [Set.mem_setOf_eq, ← hafeq, norm_def]⟩
  obtain ⟨b₁, hb₁A, hb₁min⟩ := Set.exists_min_image _ (fun a : ℤ => a) hAg
    ⟨ag, by rw [Set.mem_setOf_eq, ← hageq, norm_def]⟩
  rw [Set.mem_setOf_eq] at ha₁A hb₁A
  -- the coefficient at `a₁ + b₁` has norm exactly `‖f‖·‖g‖`
  have hkey : ‖(f * g).coeff (a₁ + b₁)‖ = ‖f‖ * ‖g‖ := by
    have hsplit := (summable_mul_coeff f g (a₁ + b₁)).tsum_eq_add_tsum_ite a₁
    rw [coeff_mul, hsplit, show a₁ + b₁ - a₁ = b₁ by ring]
    have hmain : ‖f.coeff a₁ * g.coeff b₁‖ = ‖f‖ * ‖g‖ := by
      rw [norm_mul, ha₁A, hb₁A]
    -- all remaining terms are strictly smaller
    have hrest : ‖∑' a : ℤ, (if a = a₁ then 0 else f.coeff a * g.coeff (a₁ + b₁ - a))‖ <
        ‖f‖ * ‖g‖ := by
      refine norm_tsum_lt_of_forall_lt ?_ (by positivity) fun a => ?_
      · refine squeeze_zero (fun a => norm_nonneg _) (fun a => ?_)
          (tendsto_conv_term f g (a₁ + b₁))
        split
        · simp only [norm_zero]
          exact norm_nonneg _
        · exact le_rfl
      · rcases eq_or_ne a a₁ with rfl | ha
        · rw [if_pos rfl, norm_zero]; positivity
        · rw [if_neg ha, norm_mul]
          rcases lt_or_gt_of_ne ha with hlt | hgt
          · -- `a < a₁`: the `f`-coefficient is strictly submaximal
            have hfa : ‖f.coeff a‖ < ‖f‖ := by
              rcases lt_or_eq_of_le (norm_coeff_le_gaussNorm f a) with h | h
              · exact h
              · have := ha₁min a h
                omega
            calc ‖f.coeff a‖ * ‖g.coeff (a₁ + b₁ - a)‖
                ≤ ‖f.coeff a‖ * ‖g‖ :=
                  mul_le_mul_of_nonneg_left (norm_coeff_le_gaussNorm g _) (norm_nonneg _)
              _ < ‖f‖ * ‖g‖ := mul_lt_mul_of_pos_right hfa hNg
          · -- `a > a₁`: the `g`-coefficient is strictly submaximal
            have hgb : ‖g.coeff (a₁ + b₁ - a)‖ < ‖g‖ := by
              rcases lt_or_eq_of_le (norm_coeff_le_gaussNorm g (a₁ + b₁ - a)) with h | h
              · exact h
              · have := hb₁min _ h
                omega
            calc ‖f.coeff a‖ * ‖g.coeff (a₁ + b₁ - a)‖
                ≤ ‖f‖ * ‖g.coeff (a₁ + b₁ - a)‖ :=
                  mul_le_mul_of_nonneg_right (norm_coeff_le_gaussNorm f a) (norm_nonneg _)
              _ < ‖f‖ * ‖g‖ := mul_lt_mul_of_pos_left hgb hNf
    -- ultrametric: adding a strictly smaller tail does not change the norm
    set x := f.coeff a₁ * g.coeff b₁ with hxdef
    set y := ∑' a : ℤ, (if a = a₁ then 0 else f.coeff a * g.coeff (a₁ + b₁ - a)) with hydef
    have hyx : ‖y‖ < ‖x‖ := by rw [hmain]; exact hrest
    rw [← hmain]
    refine le_antisymm ((IsUltrametricDist.norm_add_le_max x y).trans
      (max_le le_rfl hyx.le)) ?_
    by_contra hcon
    push Not at hcon
    have hle : ‖x‖ ≤ max ‖x + y‖ ‖y‖ := by
      have h1 : ‖x + y + -y‖ ≤ max ‖x + y‖ ‖-y‖ := IsUltrametricDist.norm_add_le_max _ _
      rw [add_neg_cancel_right, norm_neg] at h1
      exact h1
    rcases max_cases ‖x + y‖ ‖y‖ with ⟨heq, -⟩ | ⟨heq, -⟩
    · rw [heq] at hle
      exact absurd (hle.trans_lt hcon) (lt_irrefl _)
    · rw [heq] at hle
      exact absurd (hle.trans_lt hyx) (lt_irrefl _)
  refine le_antisymm (norm_mul_le f g) ?_
  rw [← hkey]
  exact norm_coeff_le_gaussNorm (f * g) (a₁ + b₁)

/-- `RestrictedLaurent K` is a domain when the base is a complete nonarchimedean field with
discrete value group ([FJP] Prop 2.3: "also that 𝒞 is a domain"; univariate case). -/
theorem coeff_C_mul (t : K) (f : RestrictedLaurent K) (m : ℤ) :
    (C t * f).coeff m = t * f.coeff m := by
  rw [show C t = single 0 t from rfl, coeff_mul,
    tsum_eq_single 0 (fun b hb => by simp [coeff_single, if_neg hb])]
  simp [coeff_single]

/-- Multiplication by a scalar constant scales the Gauss norm (field base). -/
theorem norm_C_mul (t : K) (f : RestrictedLaurent K) : ‖C t * f‖ = ‖t‖ * ‖f‖ := by
  rw [norm_def, norm_def, gaussNorm, gaussNorm, Real.mul_iSup_of_nonneg (norm_nonneg t)]
  exact iSup_congr fun a => by rw [coeff_C_mul, norm_mul]

/-- Multiplication by a scalar constant scales the vendored univariate Gauss norm. -/
theorem norm_restrictedC_mul (t : K) (f : PowerSeries.Restricted K (1 : ℝ)) :
    ‖PowerSeries.Restricted.C (1 : ℝ) t * f‖ = ‖t‖ * ‖f‖ := by
  rw [Restricted.norm_eq, Restricted.norm_eq, PowerSeries.gaussNorm_eq,
    PowerSeries.gaussNorm_eq, Real.mul_iSup_of_nonneg (norm_nonneg t)]
  refine iSup_congr fun i => ?_
  rw [show (PowerSeries.Restricted.C (1 : ℝ) t * f).1 = PowerSeries.C t * f.1 from rfl,
    PowerSeries.coeff_C_mul, norm_mul]
  ring

theorem mul_ne_zero_of_ne_zero {f g : RestrictedLaurent K} (hf : f ≠ 0) (hg : g ≠ 0) :
    f * g ≠ 0 := by
  intro hcon
  have h := norm_mul_eq f g
  rw [hcon] at h
  have h0 : ‖(0 : RestrictedLaurent K)‖ = 0 := norm_zero
  rw [h0] at h
  have hNf : (0 : ℝ) < ‖f‖ := norm_pos_iff.mpr hf
  have hNg : (0 : ℝ) < ‖g‖ := norm_pos_iff.mpr hg
  nlinarith

end Field

/-! ### The nonnegative-support subring `R⟨W⟩ ⊂ R⟨W, W⁻¹⟩` -/

/-- Radius-one positivity witnesses for the vendored Gauss-norm stack. -/
instance : StrongPos (fun _ : Unit => (1 : ℝ)) := ⟨fun _ => one_pos⟩

instance (n : ℕ) : StrongPos (fun _ : Fin n => (1 : ℝ)) := ⟨fun _ => one_pos⟩

section Nonneg

variable (R) in
/-- The subring of series supported in nonnegative exponents — the copy of `R⟨W⟩` inside
`R⟨W, W⁻¹⟩` ([FJP] Lemma 2.2: "the subspace `k⟨W⟩` is the intersection of the kernels of the
continuous negative-coefficient maps"). -/
noncomputable def nonnegSubring [CompleteSpace R] : Subring (RestrictedLaurent R) where
  carrier := {f | ∀ a : ℤ, a < 0 → f.coeff a = 0}
  zero_mem' := fun a _ => rfl
  one_mem' := fun a ha => by
    simp only [coeff_one, if_neg (by omega : ¬ a = 0)]
  add_mem' := fun {f g} hf hg a ha => by
    rw [coeff_add, hf a ha, hg a ha, add_zero]
  neg_mem' := fun {f} hf a ha => by rw [coeff_neg, hf a ha, neg_zero]
  mul_mem' := fun {f g} hf hg m hm => by
    rw [coeff_mul]
    have hz : ∀ a : ℤ, f.coeff a * g.coeff (m - a) = 0 := fun a => by
      rcases lt_or_ge a 0 with ha | ha
      · rw [hf a ha, zero_mul]
      · rw [hg (m - a) (by omega), mul_zero]
    exact (tsum_congr hz).trans tsum_zero

/-- The nonnegative-support subring is closed (kernels of the continuous coefficient
functionals; [FJP] Lemma 2.2). -/
theorem isClosed_nonnegSubring [CompleteSpace R] [NormOneClass R] :
    IsClosed (nonnegSubring R : Set (RestrictedLaurent R)) := by
  have heq : (nonnegSubring R : Set (RestrictedLaurent R)) =
      ⋂ (a : ℤ) (_ : a < 0), {f : RestrictedLaurent R | f.coeff a = 0} := by
    ext f
    simp only [SetLike.mem_coe, Set.mem_iInter, Set.mem_setOf_eq]
    rfl
  rw [heq]
  exact isClosed_iInter fun a => isClosed_iInter fun _ =>
    isClosed_eq (continuous_coeff a) continuous_const

section NonnegEquiv

variable [CompleteSpace R] [NormOneClass R]

/-- The ℤ-indexed extension-by-zero of a restricted power series. -/
noncomputable def ofPowerSeries (f : PowerSeries.Restricted R (1 : ℝ)) :
    RestrictedLaurent R :=
  ⟨fun a => if 0 ≤ a then PowerSeries.coeff a.toNat f.1 else 0, by
    refine tendsto_cofinite_zero_of_finite (fun a => norm_nonneg _) fun ε hε => ?_
    have hfin : {n : ℕ | ε ≤ ‖PowerSeries.coeff n f.1‖}.Finite := by
      have h := (Restricted.isRestricted_iff_cofinite (R := R) 1).mp f.2
      simp only [one_pow, mul_one] at h
      have hev := h.eventually (eventually_lt_nhds hε (a := (0 : ℝ)))
      rw [Filter.eventually_cofinite] at hev
      exact hev.subset fun n hn => by simpa using not_lt.mpr hn
    refine (hfin.image fun n : ℕ => (n : ℤ)).subset fun a ha => ?_
    rw [Set.mem_setOf_eq] at ha
    by_cases h0 : 0 ≤ a
    · rw [if_pos h0] at ha
      exact ⟨a.toNat, ha, show ((a.toNat : ℕ) : ℤ) = a from Int.toNat_of_nonneg h0⟩
    · rw [if_neg h0, norm_zero] at ha
      linarith⟩

@[simp] theorem coeff_ofPowerSeries (f : PowerSeries.Restricted R (1 : ℝ)) (a : ℤ) :
    (ofPowerSeries f).coeff a = if 0 ≤ a then PowerSeries.coeff a.toNat f.1 else 0 := rfl

theorem ofPowerSeries_mem (f : PowerSeries.Restricted R (1 : ℝ)) :
    ofPowerSeries f ∈ nonnegSubring R := fun a ha => by
  simp [if_neg (by omega : ¬ (0 : ℤ) ≤ a)]

theorem ofPowerSeries_mul (f g : PowerSeries.Restricted R (1 : ℝ)) :
    ofPowerSeries (f * g) = ofPowerSeries f * ofPowerSeries g := by
  classical
  ext a
  rw [coeff_mul]
  by_cases h0 : 0 ≤ a
  · -- the ℤ-convolution collapses to the finite `ℕ`-antidiagonal
    have hvanish : ∀ x : ℤ, x ∉ Finset.Icc (0 : ℤ) a →
        (ofPowerSeries f).coeff x * (ofPowerSeries g).coeff (a - x) = 0 := by
      intro x hx
      rw [Finset.mem_Icc, not_and_or] at hx
      rcases hx with hx | hx
      · rw [coeff_ofPowerSeries, if_neg (by omega), zero_mul]
      · rw [coeff_ofPowerSeries (a := a - x), if_neg (by omega), mul_zero]
    rw [tsum_eq_sum hvanish, coeff_ofPowerSeries, if_pos h0]
    have hcoe : (f * g : PowerSeries.Restricted R (1 : ℝ)).1 = f.1 * g.1 := rfl
    rw [hcoe, PowerSeries.coeff_mul]
    have hbij : ∑ p ∈ Finset.HasAntidiagonal.antidiagonal a.toNat,
        (PowerSeries.coeff p.1 f.1 * PowerSeries.coeff p.2 g.1 : R) =
        ∑ x ∈ Finset.Icc (0 : ℤ) a,
          (ofPowerSeries f).coeff x * (ofPowerSeries g).coeff (a - x) := by
      refine Finset.sum_nbij' (i := fun p : ℕ × ℕ => ((p.1 : ℕ) : ℤ))
        (j := fun x : ℤ => (x.toNat, a.toNat - x.toNat)) ?_ ?_ ?_ ?_ ?_
      · intro p hp
        rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
        rw [Finset.mem_Icc]
        omega
      · intro x hx
        rw [Finset.mem_Icc] at hx
        rw [Finset.HasAntidiagonal.mem_antidiagonal]
        omega
      · intro p hp
        rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
        simp only [Int.toNat_natCast]
        ext <;> omega
      · intro x hx
        rw [Finset.mem_Icc] at hx
        omega
      · intro p hp
        rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
        rw [coeff_ofPowerSeries, coeff_ofPowerSeries,
          if_pos (by omega : (0 : ℤ) ≤ ((p.1 : ℕ) : ℤ)),
          if_pos (by omega : (0 : ℤ) ≤ a - ((p.1 : ℕ) : ℤ)), Int.toNat_natCast,
          show (a - ((p.1 : ℕ) : ℤ)).toNat = p.2 by omega]
    exact hbij
  · -- negative index: both sides vanish
    have hz : ∀ x : ℤ,
        (ofPowerSeries f).coeff x * (ofPowerSeries g).coeff (a - x) = 0 := by
      intro x
      rcases lt_or_ge x 0 with hx | hx
      · rw [coeff_ofPowerSeries, if_neg (by omega), zero_mul]
      · rw [coeff_ofPowerSeries (a := a - x), if_neg (by omega), mul_zero]
    rw [(tsum_congr hz).trans tsum_zero, coeff_ofPowerSeries, if_neg h0]

/-- v4.33 (reducible-well-typed membership form): the `ℕ`-coefficient restriction of a
nonnegatively-supported restricted Laurent series is a restricted power series, stated as
membership in `PowerSeries.isSubring 1` — the syntactic field type of the subtype literal
in `nonnegEquiv.invFun`. (An inline `show IsRestricted …` proof types only at default
transparency and makes `kabstract` choke on every goal carrying the literal.) -/
theorem mk_coeff_mem_isSubring (F : ↥(nonnegSubring R)) :
    (PowerSeries.mk fun n => (F : RestrictedLaurent R).coeff n) ∈
      PowerSeries.isSubring (R := R) (1 : ℝ) := by
  show PowerSeries.IsRestricted (1 : ℝ) _
  rw [Restricted.isRestricted_iff_cofinite]
  simp only [PowerSeries.coeff_mk, one_pow, mul_one]
  exact (F : RestrictedLaurent R).tendsto_coeff.comp
    (Function.Injective.tendsto_cofinite Nat.cast_injective)

/-- v4.33 (named smart constructor): the inverse of `nonnegEquiv` as a `def`, so goals
carry `ofCoeffs F : PowerSeries.Restricted R 1` at its stated type. (An inline subtype
literal infers `↥(PowerSeries.isSubring 1)`, which is defeq to `Restricted R 1` only at
default transparency and makes `kabstract` choke.) -/
noncomputable def ofCoeffs (F : ↥(nonnegSubring R)) : PowerSeries.Restricted R (1 : ℝ) :=
  ⟨PowerSeries.mk fun n => (F : RestrictedLaurent R).coeff n, mk_coeff_mem_isSubring F⟩

@[simp] theorem coeff_ofCoeffs (F : ↥(nonnegSubring R)) (n : ℕ) :
    PowerSeries.coeff n (ofCoeffs F).1 = (F : RestrictedLaurent R).coeff n := by
  show PowerSeries.coeff n (PowerSeries.mk fun m => (F : RestrictedLaurent R).coeff m) =
    (F : RestrictedLaurent R).coeff n
  exact PowerSeries.coeff_mk n _

/-- The norm-preserving identification of `PowerSeries.Restricted R 1` (the vendored `R⟨W⟩`)
with the nonnegative-support subring of `R⟨W, W⁻¹⟩`. -/
noncomputable def nonnegEquiv :
    PowerSeries.Restricted R (1 : ℝ) ≃+* nonnegSubring R where
  toFun f := ⟨ofPowerSeries f, ofPowerSeries_mem f⟩
  invFun F := ofCoeffs F
  left_inv f := by
    apply Subtype.ext
    ext n
    simp only [coeff_ofCoeffs, coeff_ofPowerSeries,
      if_pos (by omega : (0 : ℤ) ≤ (n : ℤ)), Int.toNat_natCast]
  right_inv F := by
    apply Subtype.ext
    ext a
    show (ofPowerSeries _).coeff a = _
    -- v4.33: the goal carries a beta-redex `(fun F ↦ ofCoeffs F) F`; normalise it away
    -- before rewriting so `kabstract` sees the named-constructor spine.
    beta_reduce
    rw [coeff_ofPowerSeries]
    by_cases h0 : 0 ≤ a
    · rw [if_pos h0, coeff_ofCoeffs, Int.toNat_of_nonneg h0]
    · rw [if_neg h0, F.2 a (by omega)]
  map_mul' f g := Subtype.ext (ofPowerSeries_mul f g)
  map_add' f g := by
    apply Subtype.ext
    ext a
    show (ofPowerSeries _).coeff a = (ofPowerSeries f).coeff a + (ofPowerSeries g).coeff a
    simp only [coeff_ofPowerSeries]
    by_cases h0 : 0 ≤ a
    · simp only [if_pos h0]
      exact map_add (PowerSeries.coeff a.toNat) _ _
    · simp [if_neg h0]

end NonnegEquiv

/-- `nonnegEquiv` preserves norms. -/
theorem nonnegEquiv_norm [CompleteSpace R] [NormOneClass R]
    (f : PowerSeries.Restricted R (1 : ℝ)) :
    ‖((nonnegEquiv (R := R) f : nonnegSubring R) : RestrictedLaurent R)‖ = ‖f‖ := by
  show ‖ofPowerSeries f‖ = ‖f‖
  rw [norm_def, Restricted.norm_eq]
  refine le_antisymm (ciSup_le fun a => ?_) ?_
  · by_cases h0 : 0 ≤ a
    · rw [coeff_ofPowerSeries, if_pos h0]
      have h := PowerSeries.le_gaussNorm norm 1 f.1 (Restricted.hasGaussNorm (R := R) 1 f) a.toNat
      rwa [one_pow, mul_one] at h
    · rw [coeff_ofPowerSeries, if_neg h0, norm_zero]
      exact PowerSeries.gaussNorm_nonneg norm 1 f.1 norm_nonneg
  · rw [PowerSeries.gaussNorm_eq]
    refine Real.iSup_le (fun n => ?_) (gaussNorm_nonneg (ofPowerSeries f))
    rw [one_pow, mul_one]
    have h := norm_coeff_le_gaussNorm (ofPowerSeries f) (n : ℤ)
    rwa [coeff_ofPowerSeries, if_pos (by omega : (0 : ℤ) ≤ (n : ℤ)), Int.toNat_natCast] at h

/-- The norm-preserving embedding `R⟨W⟩ → R⟨W,W⁻¹⟩` (composite of `nonnegEquiv` with the
subring inclusion). -/
noncomputable def ofRestricted [CompleteSpace R] [NormOneClass R] :
    PowerSeries.Restricted R (1 : ℝ) →+* RestrictedLaurent R :=
  (nonnegSubring R).subtype.comp (nonnegEquiv (R := R)).toRingHom

theorem ofRestricted_norm [CompleteSpace R] [NormOneClass R]
    (f : PowerSeries.Restricted R (1 : ℝ)) : ‖ofRestricted (R := R) f‖ = ‖f‖ :=
  nonnegEquiv_norm f

theorem ofRestricted_injective [CompleteSpace R] [NormOneClass R] :
    Function.Injective (ofRestricted (R := R)) := fun f g h =>
  (nonnegEquiv (R := R)).injective (Subtype.ext h)

end Nonneg

/-! ### Density of Laurent polynomials and the affinoid presentation surjection

[FJP] Prop 2.1: "Each of 𝓑, 𝒞, 𝒟 is a quotient of a finite Tate algebra over `k`, so each is
strongly noetherian."  We realise the presentation as a *surjection* from the vendored
two-variable restricted ring (evaluating `W ↦ Wu`, `V ↦ Wu⁻¹`); surjectivity holds via the
explicit norm-preserving monomial section, and noetherianity of the target follows from
noetherianity of the source — no kernel identification is required. -/

section Eval

variable [CompleteSpace R] [NormOneClass R]

/-- Any normed ring with ultrametric distance is nonarchimedean (local copy of the
`ExampleUnitDisc` instance, to keep this file's imports light). -/
instance (priority := 90) nonarchOfUltra {S : Type*} [NormedRing S] [IsUltrametricDist S] :
    NonarchimedeanRing S where
  is_nonarchimedean := NonarchimedeanAddGroup.is_nonarchimedean

instance : NormOneClass (RestrictedLaurent R) :=
  ⟨by rw [← single_zero_one, norm_single, norm_one]⟩

/-- The negation of the coefficient index, as a plain map. -/
noncomputable def negateAux (f : RestrictedLaurent R) : RestrictedLaurent R :=
  ⟨fun a => f.coeff (-a), f.tendsto_coeff.comp ((Equiv.neg ℤ).injective.tendsto_cofinite)⟩

@[simp] theorem coeff_negateAux (f : RestrictedLaurent R) (a : ℤ) :
    (negateAux f).coeff a = f.coeff (-a) := rfl

theorem negateAux_mul (f g : RestrictedLaurent R) :
    negateAux (f * g) = negateAux f * negateAux g := by
  ext m
  have h1 : (negateAux f * negateAux g).coeff m =
      ∑' a : ℤ, f.coeff (-a) * g.coeff (-(m - a)) := coeff_mul _ _ m
  rw [coeff_negateAux, coeff_mul, h1, ← (Equiv.neg ℤ).tsum_eq]
  refine tsum_congr fun a => ?_
  simp only [Equiv.neg_apply, coeff_negateAux, neg_neg]
  rw [show -(m - a) = -m - -a by ring]

/-- The index-negation automorphism `W ↦ W⁻¹` of the restricted Laurent ring. -/
noncomputable def negate : RestrictedLaurent R ≃+* RestrictedLaurent R where
  toFun := negateAux
  invFun := negateAux
  left_inv f := by ext a; simp
  right_inv f := by ext a; simp
  map_add' f g := by ext a; rfl
  map_mul' := negateAux_mul

@[simp] theorem coeff_negate (f : RestrictedLaurent R) (a : ℤ) :
    (negate f).coeff a = f.coeff (-a) := rfl

theorem norm_negate (f : RestrictedLaurent R) : ‖negate f‖ = ‖f‖ := by
  rw [norm_def, norm_def]
  refine le_antisymm (ciSup_le fun a => ?_) (ciSup_le fun a => ?_)
  · exact norm_coeff_le_gaussNorm f (-a)
  · have h := norm_coeff_le_gaussNorm (negate f) (-a)
    simpa using h

/-- Powers of a norm-`≤ 1` element stay in the unit ball. -/
theorem norm_pow_le_one {s : RestrictedLaurent R} (hs : ‖s‖ ≤ 1) (i : ℕ) : ‖s ^ i‖ ≤ 1 := by
  induction i with
  | zero => rw [pow_zero, norm_one]
  | succ n ih =>
    rw [pow_succ]
    exact (norm_mul_le _ _).trans (mul_le_one₀ ih (norm_nonneg _) hs)

section EvalLE

variable {A : Type*} [NormedCommRing A] [IsUltrametricDist A]
variable (φ : A →+* RestrictedLaurent R) (s : RestrictedLaurent R)

/-- Coefficient decay of an evaluation family. -/
theorem tendsto_evalLE_term (hφ : ∀ x, ‖φ x‖ ≤ ‖x‖) (hs : ‖s‖ ≤ 1)
    (G : PowerSeries.Restricted A (1 : ℝ)) :
    Tendsto (fun i : ℕ => ‖φ (PowerSeries.coeff i G.1) * s ^ i‖) cofinite (𝓝 0) := by
  have hG := (Restricted.isRestricted_iff_cofinite (R := A) 1).mp G.2
  simp only [one_pow, mul_one] at hG
  refine squeeze_zero (fun i => norm_nonneg _) (fun i => ?_) hG
  refine (norm_mul_le _ _).trans ?_
  calc ‖φ (PowerSeries.coeff i G.1)‖ * ‖s ^ i‖
      ≤ ‖φ (PowerSeries.coeff i G.1)‖ * 1 :=
        mul_le_mul_of_nonneg_left (norm_pow_le_one hs i) (norm_nonneg _)
    _ = ‖φ (PowerSeries.coeff i G.1)‖ := mul_one _
    _ ≤ ‖PowerSeries.coeff i G.1‖ := hφ _

theorem summable_evalLE (hφ : ∀ x, ‖φ x‖ ≤ ‖x‖) (hs : ‖s‖ ≤ 1)
    (G : PowerSeries.Restricted A (1 : ℝ)) :
    Summable (fun i : ℕ => φ (PowerSeries.coeff i G.1) * s ^ i) := by
  rw [NonarchimedeanAddGroup.summable_iff_tendsto_cofinite_zero]
  exact tendsto_zero_iff_norm_tendsto_zero.mpr (tendsto_evalLE_term φ s hφ hs G)

/-- Evaluation of a radius-one restricted power series at a point of the closed unit ball,
with coefficients mapped by a norm-nonincreasing homomorphism — the elementary form of the
universal property ([FJP] Lemma 1.1, one variable): `G ↦ ∑ φ(cᵢ) sⁱ`. -/
noncomputable def evalLE (hφ : ∀ x, ‖φ x‖ ≤ ‖x‖) (hs : ‖s‖ ≤ 1) :
    PowerSeries.Restricted A (1 : ℝ) →+* RestrictedLaurent R where
  toFun G := ∑' i : ℕ, φ (PowerSeries.coeff i G.1) * s ^ i
  map_one' := by
    rw [tsum_eq_single 0 (fun i hi => by
      rw [show (1 : PowerSeries.Restricted A (1 : ℝ)).1 = 1 from rfl,
        PowerSeries.coeff_one, if_neg hi, map_zero, zero_mul])]
    rw [show (1 : PowerSeries.Restricted A (1 : ℝ)).1 = 1 from rfl,
      PowerSeries.coeff_one, if_pos rfl, map_one, pow_zero, mul_one]
  map_zero' := by
    have h0 : ∀ i : ℕ,
        φ (PowerSeries.coeff i (0 : PowerSeries.Restricted A (1 : ℝ)).1) * s ^ i = 0 :=
      fun i => by
        rw [show (0 : PowerSeries.Restricted A (1 : ℝ)).1 = 0 from rfl, map_zero, map_zero,
          zero_mul]
    exact (tsum_congr h0).trans tsum_zero
  map_add' G G' := by
    have hterm : ∀ i : ℕ,
        φ (PowerSeries.coeff i (G + G' : PowerSeries.Restricted A (1 : ℝ)).1) * s ^ i =
        φ (PowerSeries.coeff i G.1) * s ^ i + φ (PowerSeries.coeff i G'.1) * s ^ i :=
      fun i => by
        rw [show (G + G' : PowerSeries.Restricted A (1 : ℝ)).1 = G.1 + G'.1 from rfl,
          map_add, map_add, add_mul]
    rw [tsum_congr hterm,
      (summable_evalLE φ s hφ hs G).tsum_add (summable_evalLE φ s hφ hs G')]
  map_mul' G G' := by
    have hf := summable_evalLE φ s hφ hs G
    have hg := summable_evalLE φ s hφ hs G'
    have hfg := Summable.mul_of_nonarchimedean hf hg
    have key : (∑' i : ℕ, φ (PowerSeries.coeff i G.1) * s ^ i) *
        (∑' i : ℕ, φ (PowerSeries.coeff i G'.1) * s ^ i) =
        ∑' i : ℕ,
          φ (PowerSeries.coeff i (G * G' : PowerSeries.Restricted A (1 : ℝ)).1) * s ^ i := by
      rw [hf.tsum_mul_tsum_eq_tsum_sum_antidiagonal hg hfg]
      refine tsum_congr fun n => ?_
      rw [show (G * G' : PowerSeries.Restricted A (1 : ℝ)).1 = G.1 * G'.1 from rfl,
        PowerSeries.coeff_mul, map_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun kl hkl => ?_
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hkl
      rw [map_mul, ← hkl, pow_add]
      ring
    exact key.symm

theorem norm_evalLE_le (hφ : ∀ x, ‖φ x‖ ≤ ‖x‖) (hs : ‖s‖ ≤ 1)
    (G : PowerSeries.Restricted A (1 : ℝ)) :
    ‖evalLE φ s hφ hs G‖ ≤ ‖G‖ := by
  refine IsUltrametricDist.norm_tsum_le_of_forall_le fun i => ?_
  have h := PowerSeries.le_gaussNorm norm 1 G.1 (Restricted.hasGaussNorm (R := A) 1 G) i
  rw [one_pow, mul_one] at h
  refine (norm_mul_le _ _).trans ?_
  have h2 : ‖φ (PowerSeries.coeff i G.1)‖ * ‖s ^ i‖ ≤ ‖PowerSeries.coeff i G.1‖ * 1 :=
    mul_le_mul (hφ _) (norm_pow_le_one hs i) (norm_nonneg _) (norm_nonneg _)
  rw [mul_one] at h2
  exact h2.trans h

end EvalLE

/-- Base change of univariate restricted series along a norm-preserving isomorphism. -/
noncomputable def restrictedCongr {A B : Type*} [NormedCommRing A] [IsUltrametricDist A]
    [NormedCommRing B] [IsUltrametricDist B]
    (e : A ≃+* B) (he : ∀ x, ‖e x‖ = ‖x‖) :
    PowerSeries.Restricted A (1 : ℝ) ≃+* PowerSeries.Restricted B (1 : ℝ) where
  toFun G := ⟨PowerSeries.map (e : A →+* B) G.1, by
    show PowerSeries.IsRestricted (1 : ℝ) _
    rw [Restricted.isRestricted_iff_cofinite]
    have hG := (Restricted.isRestricted_iff_cofinite (R := A) 1).mp G.2
    simp only [one_pow, mul_one, PowerSeries.coeff_map] at hG ⊢
    refine hG.congr fun i => ?_
    exact (he _).symm⟩
  invFun G := ⟨PowerSeries.map (e.symm : B →+* A) G.1, by
    show PowerSeries.IsRestricted (1 : ℝ) _
    rw [Restricted.isRestricted_iff_cofinite]
    have hG := (Restricted.isRestricted_iff_cofinite (R := B) 1).mp G.2
    have hsymm : ∀ y : B, ‖e.symm y‖ = ‖y‖ := fun y => by
      conv_rhs => rw [← RingEquiv.apply_symm_apply e y]
      exact (he _).symm
    simp only [one_pow, mul_one, PowerSeries.coeff_map] at hG ⊢
    refine hG.congr fun i => ?_
    exact (hsymm _).symm⟩
  left_inv G := by
    apply Subtype.ext
    show PowerSeries.map _ (PowerSeries.map _ G.1) = G.1
    ext n
    simp [PowerSeries.coeff_map]
  right_inv G := by
    apply Subtype.ext
    show PowerSeries.map _ (PowerSeries.map _ G.1) = G.1
    ext n
    simp [PowerSeries.coeff_map]
  map_mul' G G' := by
    apply Subtype.ext
    show PowerSeries.map _ (G * G' : PowerSeries.Restricted A (1 : ℝ)).1 = _
    rw [show (G * G' : PowerSeries.Restricted A (1 : ℝ)).1 = G.1 * G'.1 from rfl, map_mul]
    rfl
  map_add' G G' := by
    apply Subtype.ext
    show PowerSeries.map _ (G + G' : PowerSeries.Restricted A (1 : ℝ)).1 = _
    rw [show (G + G' : PowerSeries.Restricted A (1 : ℝ)).1 = G.1 + G'.1 from rfl, map_add]
    rfl

@[simp] theorem coeff_restrictedCongr {A B : Type*} [NormedCommRing A] [IsUltrametricDist A]
    [NormedCommRing B] [IsUltrametricDist B] (e : A ≃+* B) (he : ∀ x, ‖e x‖ = ‖x‖)
    (G : PowerSeries.Restricted A (1 : ℝ)) (i : ℕ) :
    PowerSeries.coeff i (restrictedCongr e he G).1 = e (PowerSeries.coeff i G.1) :=
  PowerSeries.coeff_map _ _ _

theorem restrictedCongr_norm {A B : Type*} [NormedCommRing A] [IsUltrametricDist A]
    [NormedCommRing B] [IsUltrametricDist B] (e : A ≃+* B) (he : ∀ x, ‖e x‖ = ‖x‖)
    (G : PowerSeries.Restricted A (1 : ℝ)) :
    ‖restrictedCongr e he G‖ = ‖G‖ := by
  rw [Restricted.norm_eq, Restricted.norm_eq, PowerSeries.gaussNorm_eq,
    PowerSeries.gaussNorm_eq]
  refine iSup_congr fun i => ?_
  rw [coeff_restrictedCongr, he]

/-- v4.33 (reducible-well-typed coe form): norm-preservation of the `Fin 0`-collapse
`restrictedFinZeroEquiv`, stated at the `RingEquiv` coercion — the syntactic shape `restrictedCongr`'s
`he`-argument expects. (The bare `RingHomIsometric.norm_map (σ := ….toRingHom)` proof
carries the `RingHom`-coe type, which types only at default transparency and makes
`kabstract` choke on goals carrying `innerToSeries`.) -/
theorem foo_norm_map (x : MvPowerSeries.Restricted R (fun _ : Fin 0 => (1 : ℝ))) :
    ‖restrictedFinZeroEquiv R (fun _ : Fin 0 => (1 : ℝ)) x‖ = ‖x‖ :=
  RingHomIsometric.norm_map (σ := (restrictedFinZeroEquiv R (fun _ : Fin 0 => (1 : ℝ))).toRingHom)

/-- The one-variable restricted ring in `Fin 1`-indexed form, identified with the
univariate form. -/
noncomputable def innerToSeries :
    MvPowerSeries.Restricted R (fun _ : Fin 1 => (1 : ℝ)) ≃+*
      PowerSeries.Restricted R (1 : ℝ) :=
  (UnitDiscExample.finSuccOne R 0).trans
    (restrictedCongr (restrictedFinZeroEquiv R (fun _ : Fin 0 => (1 : ℝ)))
      (fun x => foo_norm_map x))

theorem innerToSeries_norm (f : MvPowerSeries.Restricted R (fun _ : Fin 1 => (1 : ℝ))) :
    ‖innerToSeries (R := R) f‖ = ‖f‖ := by
  rw [innerToSeries, RingEquiv.trans_apply, restrictedCongr_norm,
    UnitDiscExample.finSuccOne_norm]

/-- The coefficient map for the evaluation: `V`-series map to nonpositively supported
Laurent series through `negate ∘ ofRestricted ∘ innerToSeries`. -/
noncomputable def negOfSeries :
    MvPowerSeries.Restricted R (fun _ : Fin 1 => (1 : ℝ)) →+* RestrictedLaurent R :=
  ((negate (R := R)).toRingHom.comp (ofRestricted (R := R))).comp
    (innerToSeries (R := R)).toRingHom

theorem norm_negOfSeries (f : MvPowerSeries.Restricted R (fun _ : Fin 1 => (1 : ℝ))) :
    ‖negOfSeries (R := R) f‖ = ‖f‖ := by
  show ‖negate (ofRestricted (innerToSeries f))‖ = ‖f‖
  rw [norm_negate, ofRestricted_norm, innerToSeries_norm]

/-- Powers of `W` are monomials. -/
theorem Wu_pow (i : ℕ) : ((Wu (R := R)).val) ^ i = single (i : ℤ) 1 := by
  induction i with
  | zero => rw [pow_zero, ← single_zero_one]; norm_num
  | succ n ih =>
    rw [pow_succ, ih, show (Wu (R := R)).val = single 1 1 from rfl, single_mul_single,
      one_mul]
    norm_num

/-- Evaluation `R⟨W,V⟩ → R⟨W,W⁻¹⟩`, `W ↦ Wu, V ↦ Wu⁻¹`: a bounded ring homomorphism. -/
noncomputable def evalHom :
    MvPowerSeries.Restricted R (fun _ : Fin 2 => (1 : ℝ)) →+* RestrictedLaurent R :=
  (evalLE (negOfSeries (R := R)) (Wu (R := R)).val
      (fun x => (norm_negOfSeries x).le) norm_W.le).comp
    (UnitDiscExample.finSuccOne R 1).toRingHom

theorem evalHom_norm_le
    (f : MvPowerSeries.Restricted R (fun _ : Fin 2 => (1 : ℝ))) :
    ‖evalHom (R := R) f‖ ≤ ‖f‖ := by
  have h : evalHom (R := R) f = evalLE (negOfSeries (R := R)) (Wu (R := R)).val
      (fun x => (norm_negOfSeries x).le) norm_W.le (UnitDiscExample.finSuccOne R 1 f) := rfl
  rw [h]
  refine (norm_evalLE_le _ _ _ _ _).trans ?_
  rw [UnitDiscExample.finSuccOne_norm]

/-- The nonpositive-support truncation of a Laurent series. -/
noncomputable def truncNonpos (h : RestrictedLaurent R) : RestrictedLaurent R :=
  ⟨fun a => if a ≤ 0 then h.coeff a else 0, by
    refine squeeze_zero (fun a => norm_nonneg _) (fun a => ?_) h.tendsto_coeff
    split
    · exact le_rfl
    · simp only [norm_zero]
      exact norm_nonneg _⟩

@[simp] theorem negate_negate (f : RestrictedLaurent R) : negate (negate f) = f := by
  ext a; simp

theorem innerToSeries_symm_norm (g : PowerSeries.Restricted R (1 : ℝ)) :
    ‖(innerToSeries (R := R)).symm g‖ = ‖g‖ := by
  conv_rhs => rw [← RingEquiv.apply_symm_apply (innerToSeries (R := R)) g]
  rw [innerToSeries_norm]

theorem ofRestricted_nonnegEquiv_symm (F : nonnegSubring R) :
    ofRestricted (R := R) ((nonnegEquiv (R := R)).symm F) = (F : RestrictedLaurent R) := by
  show ((nonnegEquiv (R := R)) ((nonnegEquiv (R := R)).symm F) : RestrictedLaurent R) = _
  rw [RingEquiv.apply_symm_apply]

theorem ofRestricted_C (x : R) :
    ofRestricted (R := R) (PowerSeries.Restricted.C (1 : ℝ) x) = single 0 x := by
  ext a
  show (ofPowerSeries _).coeff a = _
  rw [coeff_ofPowerSeries, coeff_single]
  by_cases h0 : 0 ≤ a
  · rw [if_pos h0]
    show PowerSeries.coeff a.toNat (PowerSeries.C x) = _
    rw [PowerSeries.coeff_C]
    by_cases ha : a = 0
    · rw [if_pos (by omega), if_pos ha]
    · rw [if_neg (by omega), if_neg ha]
  · rw [if_neg h0, if_neg (by omega)]

theorem negate_single_zero (x : R) : negate (single 0 x) = single 0 x := by
  ext a
  rw [coeff_negate, coeff_single, coeff_single]
  by_cases ha : a = 0
  · rw [if_pos (by omega), if_pos ha]
  · rw [if_neg (by omega), if_neg ha]

theorem norm_restrictedC (x : R) : ‖PowerSeries.Restricted.C (1 : ℝ) x‖ = ‖x‖ := by
  rw [← ofRestricted_norm (R := R) (PowerSeries.Restricted.C (1 : ℝ) x), ofRestricted_C, norm_single]

/-- The vendored univariate restricted ring has norm-one unit. -/
instance : NormOneClass (PowerSeries.Restricted R (1 : ℝ)) :=
  ⟨by
    rw [show (1 : PowerSeries.Restricted R (1 : ℝ)) = PowerSeries.Restricted.C (1 : ℝ) 1 from
      Subtype.ext (map_one PowerSeries.C).symm, norm_restrictedC, norm_one]⟩

/-- The coefficient functional as an additive homomorphism. -/
noncomputable def coeffHom (m : ℤ) : RestrictedLaurent R →+ R where
  toFun f := f.coeff m
  map_zero' := rfl
  map_add' f g := rfl

/-- The norm of the nonpositive truncation is bounded by the norm. -/
theorem norm_truncNonpos_le (h : RestrictedLaurent R) : ‖truncNonpos h‖ ≤ ‖h‖ := by
  rw [norm_def]
  refine Real.iSup_le (fun a => ?_) (norm_nonneg h)
  show ‖if a ≤ 0 then h.coeff a else 0‖ ≤ ‖h‖
  split
  · exact (norm_coeff_le_gaussNorm h a).trans_eq (norm_def h).symm
  · rw [norm_zero]
    exact norm_nonneg h

/-- v4.33 (named witness): the negated nonpositive truncation is nonnegatively
supported — extracted so the `nonnegSubring`-subtype literal in
`evalHom_exists_norm_le` carries a named proof (an inline `by`-proof with
`if`-rewrites makes `kabstract` motive-checks choke on goals carrying the literal). -/
theorem negate_truncNonpos_mem (h : RestrictedLaurent R) :
    negate (truncNonpos h) ∈ nonnegSubring R := fun a ha => by
  show (truncNonpos h).coeff (-a) = 0
  show (if -a ≤ 0 then h.coeff (-a) else 0) = 0
  rw [if_neg (by omega)]

/-- v4.33 (named witness): the `evalHom_exists_norm_le` preimage series is restricted —
extracted for the same `kabstract` reason as `negate_truncNonpos_mem`. -/
theorem mk_if_coeff_mem_isSubring (h : RestrictedLaurent R)
    (c0 : PowerSeries.Restricted R (1 : ℝ)) :
    (PowerSeries.mk fun i =>
        if i = 0 then c0 else PowerSeries.Restricted.C (1 : ℝ) (h.coeff i)) ∈
      PowerSeries.isSubring (R := PowerSeries.Restricted R (1 : ℝ)) (1 : ℝ) := by
  classical
  show PowerSeries.IsRestricted (1 : ℝ) _
  rw [Restricted.isRestricted_iff_cofinite]
  simp only [PowerSeries.coeff_mk, one_pow, mul_one]
  refine tendsto_cofinite_zero_of_finite (fun i => norm_nonneg _) fun ε hε => ?_
  have hfin : {a : ℤ | ε ≤ ‖h.coeff a‖}.Finite := h.finite_setOf_le_norm_coeff hε
  refine ((hfin.image fun a : ℤ => a.toNat).union (Set.finite_singleton 0)).subset
    fun i hi => ?_
  rw [Set.mem_setOf_eq] at hi
  rcases eq_or_ne i 0 with rfl | hi0
  · exact Set.mem_union_right _ rfl
  · rw [if_neg hi0, norm_restrictedC] at hi
    exact Set.mem_union_left _ ⟨(i : ℤ), hi, Int.toNat_natCast i⟩

/-- v4.33 (named smart constructor): the `evalHom_exists_norm_le` preimage over the
univariate coefficient ring, at its stated doubly-restricted type (a bare subtype
literal infers `↥(PowerSeries.isSubring 1)`, defeq only at default transparency, and
makes `kabstract` choke on every goal carrying it — see `ofCoeffs`). -/
noncomputable def evalHomSection (h : RestrictedLaurent R)
    (c0 : PowerSeries.Restricted R (1 : ℝ)) :
    PowerSeries.Restricted (PowerSeries.Restricted R (1 : ℝ)) (1 : ℝ) :=
  ⟨PowerSeries.mk fun i => if i = 0 then c0 else PowerSeries.Restricted.C (1 : ℝ) (h.coeff i),
    mk_if_coeff_mem_isSubring h c0⟩

/-- `evalHom` has a norm-nonincreasing set-theoretic section: the preimage places the
nonpositive part on the `V`-axis and the positive coefficients on `W`-monomials
([FJP] §1.4's "norm-preserving monomial section"). -/
theorem evalHom_exists_norm_le (h : RestrictedLaurent R) :
    ∃ g : MvPowerSeries.Restricted R (fun _ : Fin 2 => (1 : ℝ)),
      evalHom (R := R) g = h ∧ ‖g‖ ≤ ‖h‖ := by
  classical
  -- the friendly preimage over the univariate coefficient ring
  set c0 : PowerSeries.Restricted R (1 : ℝ) :=
    (nonnegEquiv (R := R)).symm ⟨negate (truncNonpos h), negate_truncNonpos_mem h⟩ with hc0
  set G' : PowerSeries.Restricted (PowerSeries.Restricted R (1 : ℝ)) (1 : ℝ) :=
    evalHomSection h c0 with hG'
  -- transport to the `Fin 1`-indexed coefficient ring
  set G'' : PowerSeries.Restricted
      (MvPowerSeries.Restricted R (fun _ : Fin 1 => (1 : ℝ))) (1 : ℝ) :=
    restrictedCongr (innerToSeries (R := R)).symm (innerToSeries_symm_norm (R := R)) G'
    with hG''
  refine ⟨(UnitDiscExample.finSuccOne R 1).symm G'', ?_, ?_⟩
  swap
  · -- the norm bound: all coefficients of `G'` are coefficients of `h` (or its truncation)
    rw [UnitDiscExample.finSuccOne_symm_norm, hG'', restrictedCongr_norm, hG',
      Restricted.norm_eq, PowerSeries.gaussNorm_eq]
    refine Real.iSup_le (fun i => ?_) (norm_nonneg h)
    rw [one_pow, mul_one]
    show ‖PowerSeries.coeff i (PowerSeries.mk fun j =>
      if j = 0 then c0 else PowerSeries.Restricted.C (1 : ℝ) (h.coeff j))‖ ≤ ‖h‖
    rw [PowerSeries.coeff_mk]
    rcases eq_or_ne i 0 with rfl | hi0
    · rw [if_pos rfl]
      have h1 := nonnegEquiv_norm (R := R) c0
      conv_rhs at h1 => rw [hc0]
      rw [hc0, RingEquiv.apply_symm_apply] at h1
      calc ‖c0‖ = ‖negate (truncNonpos h)‖ := by rw [← hc0] at h1; exact h1.symm ▸ h1.symm
        _ = ‖truncNonpos h‖ := norm_negate _
        _ ≤ ‖h‖ := norm_truncNonpos_le h
    · rw [if_neg hi0, norm_restrictedC]
      exact (norm_coeff_le_gaussNorm h (i : ℤ)).trans_eq (norm_def h).symm
  have happ : evalHom (R := R) ((UnitDiscExample.finSuccOne R 1).symm G'') =
      evalLE (negOfSeries (R := R)) (Wu (R := R)).val
        (fun x => (norm_negOfSeries x).le) norm_W.le G'' := by
    have hrfl : evalHom (R := R) ((UnitDiscExample.finSuccOne R 1).symm G'') =
        evalLE (negOfSeries (R := R)) (Wu (R := R)).val
          (fun x => (norm_negOfSeries x).le) norm_W.le
          (UnitDiscExample.finSuccOne R 1
            ((UnitDiscExample.finSuccOne R 1).symm G'')) := rfl
    rw [hrfl, RingEquiv.apply_symm_apply]
  rw [happ]
  -- the terms of the evaluation
  have hterm : ∀ i : ℕ,
      negOfSeries (R := R) (PowerSeries.coeff i G''.1) * (Wu (R := R)).val ^ i =
      if i = 0 then truncNonpos h else single (i : ℤ) (h.coeff i) := by
    intro i
    have hcoeffG'' : PowerSeries.coeff i G''.1 =
        (innerToSeries (R := R)).symm (PowerSeries.coeff i G'.1) :=
      coeff_restrictedCongr _ _ _ _
    have hφ : negOfSeries (R := R) (PowerSeries.coeff i G''.1) =
        negate (ofRestricted (PowerSeries.coeff i G'.1)) := by
      rw [hcoeffG'']
      show negate (ofRestricted (innerToSeries (R := R)
        ((innerToSeries (R := R)).symm _))) = _
      rw [RingEquiv.apply_symm_apply]
    have hcoeffG' : PowerSeries.coeff i G'.1 =
        if i = 0 then c0 else PowerSeries.Restricted.C (1 : ℝ) (h.coeff i) := by
      show PowerSeries.coeff i (PowerSeries.mk fun j =>
        if j = 0 then c0 else PowerSeries.Restricted.C (1 : ℝ) (h.coeff j)) = _
      rw [PowerSeries.coeff_mk]
    rcases eq_or_ne i 0 with rfl | hi0
    · rw [hφ, hcoeffG', if_pos rfl, if_pos rfl, hc0, ofRestricted_nonnegEquiv_symm]
      show negate (negate (truncNonpos h)) * _ = _
      rw [negate_negate, pow_zero, mul_one]
    · rw [hφ, hcoeffG', if_neg hi0, if_neg hi0, ofRestricted_C, negate_single_zero, Wu_pow,
        single_mul_single, zero_add, mul_one]
  -- coefficientwise evaluation of the sum
  ext m
  have hsum := summable_evalLE (negOfSeries (R := R)) (Wu (R := R)).val
    (fun x => (norm_negOfSeries x).le) norm_W.le G''
  have hmap := (hsum.hasSum.map (coeffHom (R := R) m) (continuous_coeff m)).tsum_eq
  have hunfold : (evalLE (negOfSeries (R := R)) (Wu (R := R)).val
      (fun x => (norm_negOfSeries x).le) norm_W.le) G'' =
      ∑' i : ℕ, negOfSeries (R := R) (PowerSeries.coeff i G''.1) *
        (Wu (R := R)).val ^ i := rfl
  rw [hunfold]
  show coeffHom (R := R) m (∑' i : ℕ, negOfSeries (R := R) (PowerSeries.coeff i G''.1) *
    (Wu (R := R)).val ^ i) = h.coeff m
  rw [← hmap]
  simp only [Function.comp_apply]
  have hterm' : ∀ i : ℕ, coeffHom (R := R) m
      (negOfSeries (R := R) (PowerSeries.coeff i G''.1) * (Wu (R := R)).val ^ i) =
      if i = 0 then (if m ≤ 0 then h.coeff m else 0)
      else (if m = (i : ℤ) then h.coeff i else 0) := by
    intro i
    show (negOfSeries (R := R) (PowerSeries.coeff i G''.1) *
      (Wu (R := R)).val ^ i).coeff m = _
    rw [hterm i]
    rcases eq_or_ne i 0 with rfl | hi0
    · rw [if_pos rfl]; rfl
    · rw [if_neg hi0, coeff_single, if_neg hi0]
  rw [tsum_congr hterm']
  rcases le_or_gt m 0 with hm | hm
  · rw [tsum_eq_single 0 (fun i hi => by
      rw [if_neg hi, if_neg (by omega)]), if_pos rfl, if_pos hm]
  · rw [tsum_eq_single m.toNat (fun i hi => by
      rcases eq_or_ne i 0 with rfl | hi0
      · rw [if_pos rfl, if_neg (by omega)]
      · rw [if_neg hi0, if_neg (by omega)]),
      if_neg (by omega), if_pos (by omega), show ((m.toNat : ℕ) : ℤ) = m by omega]

theorem evalHom_surjective :
    Function.Surjective (evalHom (R := R)) := fun h =>
  let ⟨g, hg, _⟩ := evalHom_exists_norm_le h
  ⟨g, hg⟩

end Eval

end RestrictedLaurent

end FiniteJet
