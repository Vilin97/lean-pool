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
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.FJP.FiniteJetRings
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.NoetherianTateModules
public import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
public import Mathlib.RingTheory.LocalProperties.Submodule

/-!
# The restricted Gauss ring `P_E = E⟨T₁,…,T_m⟩` and its adic-completion model

Source: [FJP] (4.4). Over a normed ultrametric vertex `E`, this file defines the vendored
radius-one restricted power series ring `P E m = E⟨T₁,…,T_m⟩` together with its polynomial
subrings (`polyToP`, `polyBall`), the Gauss-norm coefficient estimates, level-`n`
truncations (`trnc`), and — given a scaling pseudouniformizer bundle
`(t, htu, ht1, ht0, hscale)` — the **(4.4) identification**

* `ballAdicEquiv : ↥(unitBall (P E m)) ≃+* AdicCompletion (I0 t ht1)
  (MvPolynomial (Fin m) ↥(unitBall E))`

of the unit ball of `E⟨T⟩` with the `(t)`-adic completion of `E₀[T]`, and its flatness
consequence `flat_polyToP : Module.Flat (MvPolynomial (Fin m) E) (P E m)` (Stacks 00MB +
the scalar-tower localization sandwich).

This file was extracted verbatim from `FiniteJetGraphKoszul.lean` (campaign ticket K2b,
crosswalk D4) so that the adic-completion model of `P_E` is available *upstream* of both
`FiniteJetNoetherianVertices.lean` and `FiniteJetGraphKoszul.lean`; the two generic
helpers `finsupp_prod_one` and the `NormOneClass` instance for radius-one restricted
rings were re-homed here from `FiniteJetNoetherianVertices.lean` for the same reason.
Declaration names and namespaces are unchanged (`FiniteJet.GraphKoszul.P` etc.), so call
sites are unaffected.
-/

@[expose] public section

open Filter Topology

namespace FiniteJet

theorem finsupp_prod_one {m : ℕ} (t : Fin m →₀ ℕ) :
    (t.prod fun _ k => (1 : ℝ) ^ k) = 1 := by
  simp

/-- Radius-one restricted rings over a `NormOneClass` base have norm-one unit. -/
noncomputable instance {R : Type*} [NormedCommRing R] [IsUltrametricDist R] [NormOneClass R]
    {k : ℕ} : NormOneClass (MvPowerSeries.Restricted R (fun _ : Fin k => (1 : ℝ))) := by
  refine ⟨?_⟩
  rw [MvRestricted.norm_eq]
  refine le_antisymm ?_ ?_
  · rw [MvPowerSeries.gaussNorm]
    refine Real.iSup_le (fun t => ?_) zero_le_one
    rw [finsupp_prod_one, mul_one]
    show ‖MvPowerSeries.coeff t (1 : MvPowerSeries (Fin k) R)‖ ≤ 1
    rw [MvPowerSeries.coeff_one]
    split
    · rw [norm_one]
    · rw [norm_zero]
      exact zero_le_one
  · have h := MvPowerSeries.le_gaussNorm _ _ _
      (MvRestricted.hasGaussNorm _ (1 : MvPowerSeries.Restricted R (fun _ : Fin k => (1 : ℝ))))
      (0 : Fin k →₀ ℕ)
    rw [finsupp_prod_one, mul_one] at h
    calc (1 : ℝ) = ‖MvPowerSeries.coeff (0 : Fin k →₀ ℕ) (1 : MvPowerSeries (Fin k) R)‖ := by
          rw [MvPowerSeries.coeff_one, if_pos rfl, norm_one]
      _ ≤ _ := h

namespace GraphKoszul

/-! ### Ball division along a scaling unit -/

section BallDivision

variable {A : Type*} [NormedCommRing A] [IsUltrametricDist A] [NormOneClass A]

/-- Ball division along a scaling unit: `‖x‖ ≤ ‖t‖ⁿ` forces `x ∈ tⁿ·(unit ball)`. -/
theorem exists_norm_le_one_eq_pow_mul {t : A} (htu : IsUnit t) (ht0 : 0 < ‖t‖)
    (hscale : ∀ x : A, ‖t * x‖ = ‖t‖ * ‖x‖) (n : ℕ) (x : A) (hx : ‖x‖ ≤ ‖t‖ ^ n) :
    ∃ y : A, ‖y‖ ≤ 1 ∧ x = t ^ n * y := by
  refine ⟨((htu.unit⁻¹ : Aˣ) : A) ^ n * x, ?_, ?_⟩
  · have hxy : t ^ n * (((htu.unit⁻¹ : Aˣ) : A) ^ n * x) = x := by
      rw [← mul_assoc, ← mul_pow, IsUnit.mul_val_inv, one_pow, one_mul]
    have hnorm := norm_pow_mul_of_scale (E := A) hscale n (((htu.unit⁻¹ : Aˣ) : A) ^ n * x)
    rw [hxy] at hnorm
    by_contra hgt
    push Not at hgt
    have hlt : ‖t‖ ^ n < ‖t‖ ^ n * ‖((htu.unit⁻¹ : Aˣ) : A) ^ n * x‖ := by
      calc ‖t‖ ^ n = ‖t‖ ^ n * 1 := (mul_one _).symm
        _ < _ := mul_lt_mul_of_pos_left hgt (pow_pos ht0 n)
    rw [← hnorm] at hlt
    exact absurd hx (not_le.mpr hlt)
  · rw [← mul_assoc, ← mul_pow, IsUnit.mul_val_inv, one_pow, one_mul]

end BallDivision

/-! ### The restricted ring `P_E` and its polynomial subrings -/

/-- `P_E = E⟨T₁,…,T_m⟩`. -/
abbrev P (E : Type*) [NormedCommRing E] [IsUltrametricDist E] (m : ℕ) : Type _ :=
  MvPowerSeries.Restricted E (fun _ : Fin m => (1 : ℝ))

section Restricted

variable {E : Type*} [NormedCommRing E] [IsUltrametricDist E] [NormOneClass E]
  [CompleteSpace E] {m : ℕ}

/-- The scalar embedding `MvPolynomial → P_E` ([FJP] (4.4)'s dense polynomial subring). -/
noncomputable def polyToP : MvPolynomial (Fin m) E →+* P E m where
  toFun q := ⟨q.toMvPowerSeries, MvPolynomial.IsRestrictedGauss _ q⟩
  map_one' := Subtype.ext (map_one (MvPolynomial.coeToMvPowerSeries.ringHom
    (σ := Fin m) (R := E)))
  map_mul' q r := Subtype.ext (map_mul (MvPolynomial.coeToMvPowerSeries.ringHom
    (σ := Fin m) (R := E)) q r)
  map_zero' := Subtype.ext (map_zero (MvPolynomial.coeToMvPowerSeries.ringHom
    (σ := Fin m) (R := E)))
  map_add' q r := Subtype.ext (map_add (MvPolynomial.coeToMvPowerSeries.ringHom
    (σ := Fin m) (R := E)) q r)

theorem coeff_polyToP (q : MvPolynomial (Fin m) E) (s : Fin m →₀ ℕ) :
    MvPowerSeries.coeff s ((polyToP (E := E) (m := m) q).1) = MvPolynomial.coeff s q :=
  MvPolynomial.coeff_coe q s

/-- Scaling by the constant `C t` on `P_E` scales the Gauss norm. -/
theorem norm_tP_mul (t : E) (hscale : ∀ x : E, ‖t * x‖ = ‖t‖ * ‖x‖) (F : P E m) :
    ‖polyToP (MvPolynomial.C t) * F‖ = ‖t‖ * ‖F‖ := by
  rw [MvRestricted.norm_eq, MvRestricted.norm_eq, MvPowerSeries.gaussNorm,
    MvPowerSeries.gaussNorm, Real.mul_iSup_of_nonneg (norm_nonneg t)]
  refine iSup_congr fun s => ?_
  show ‖MvPowerSeries.coeff s ((polyToP (MvPolynomial.C t) * F : P E m).1)‖ * _ = _
  rw [show (polyToP (MvPolynomial.C t) * F : P E m).1 =
      (polyToP (E := E) (m := m) (MvPolynomial.C t)).1 * F.1 from rfl,
    show (polyToP (E := E) (m := m) (MvPolynomial.C t)).1 =
      MvPowerSeries.C (σ := Fin m) (R := E) t from MvPolynomial.coe_C t,
    MvPowerSeries.coeff_C_mul, hscale, mul_assoc]

theorem norm_tP (t : E) (hscale : ∀ x : E, ‖t * x‖ = ‖t‖ * ‖x‖) :
    ‖(polyToP (MvPolynomial.C t) : P E m)‖ = ‖t‖ := by
  have h := norm_tP_mul (E := E) (m := m) t hscale 1
  rwa [mul_one, norm_one, mul_one] at h

theorem isUnit_tP (t : E) (htu : IsUnit t) :
    IsUnit (polyToP (MvPolynomial.C t) : P E m) :=
  (htu.map MvPolynomial.C).map (polyToP (E := E) (m := m))

/-- Ball division on `P_E` (instance of the generic lemma at `(P_E, C t)`). -/
theorem exists_ball_eq_tP_pow_mul {t : E} (htu : IsUnit t) (ht0 : 0 < ‖t‖)
    (hscale : ∀ x : E, ‖t * x‖ = ‖t‖ * ‖x‖) (n : ℕ) (F : P E m) (hF : ‖F‖ ≤ ‖t‖ ^ n) :
    ∃ G : P E m, ‖G‖ ≤ 1 ∧ F = polyToP (MvPolynomial.C t) ^ n * G :=
  exists_norm_le_one_eq_pow_mul (isUnit_tP t htu)
    (by rw [norm_tP t hscale]; exact ht0)
    (fun G => by rw [norm_tP t hscale]; exact norm_tP_mul t hscale G) n F
    (by rw [norm_tP t hscale]; exact hF)

/-- Polynomial division over the unit ball: a polynomial all of whose coefficients have
norm `≤ ‖t‖ⁿ` lies in the `n`-th power of the constant ideal `(C t₀) ⊂ E₀[T]`. -/
theorem mem_span_C_pow_of_coeff_norm_le {t : E} (htu : IsUnit t) (ht1 : ‖t‖ ≤ 1)
    (ht0 : 0 < ‖t‖) (hscale : ∀ x : E, ‖t * x‖ = ‖t‖ * ‖x‖) (n : ℕ)
    (q : MvPolynomial (Fin m) ↥(unitBall E))
    (hq : ∀ s, ‖MvPolynomial.coeff s q‖ ≤ ‖t‖ ^ n) :
    q ∈ Ideal.span {MvPolynomial.C (⟨t, ht1⟩ : ↥(unitBall E))} ^ n := by
  classical
  have hdiv : ∀ s, ∃ y : E, ‖y‖ ≤ 1 ∧ ((MvPolynomial.coeff s q : ↥(unitBall E)) : E) =
      t ^ n * y := fun s => exists_norm_le_one_eq_pow_mul htu ht0 hscale n _ (hq s)
  choose y hy1 hy2 using hdiv
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton']
  refine ⟨∑ s ∈ q.support, MvPolynomial.monomial s (⟨y s, hy1 s⟩ : ↥(unitBall E)), ?_⟩
  rw [Finset.sum_mul]
  refine MvPolynomial.ext _ _ fun s => ?_
  rw [MvPolynomial.coeff_sum]
  by_cases hs : s ∈ q.support
  · rw [Finset.sum_eq_single s (fun b _ hb => ?_) (fun hns => absurd hs hns)]
    · rw [← map_pow, show (MvPolynomial.C ((⟨t, ht1⟩ : ↥(unitBall E)) ^ n)) =
        MvPolynomial.monomial 0 ((⟨t, ht1⟩ : ↥(unitBall E)) ^ n) from rfl,
        MvPolynomial.monomial_mul, add_zero, MvPolynomial.coeff_monomial, if_pos rfl]
      refine Subtype.ext ?_
      show (⟨y s, hy1 s⟩ : ↥(unitBall E)).1 * ((⟨t, ht1⟩ : ↥(unitBall E)) ^ n).1 = _
      rw [hy2 s]
      show y s * t ^ n = t ^ n * y s
      ring
    · rw [← map_pow, show (MvPolynomial.C ((⟨t, ht1⟩ : ↥(unitBall E)) ^ n)) =
        MvPolynomial.monomial 0 ((⟨t, ht1⟩ : ↥(unitBall E)) ^ n) from rfl,
        MvPolynomial.monomial_mul, add_zero, MvPolynomial.coeff_monomial, if_neg hb]
  · rw [MvPolynomial.notMem_support_iff.mp hs, Finset.sum_eq_zero fun b hb => ?_]
    rw [← map_pow, show (MvPolynomial.C ((⟨t, ht1⟩ : ↥(unitBall E)) ^ n)) =
      MvPolynomial.monomial 0 ((⟨t, ht1⟩ : ↥(unitBall E)) ^ n) from rfl,
      MvPolynomial.monomial_mul, add_zero, MvPolynomial.coeff_monomial,
      if_neg (show ¬ b = s from fun hbs => hs (hbs ▸ hb))]

/-- Completeness of `P_E` for every arity (the vendored instance covers `Fin (n+1)`;
`Fin 0` is the isometric copy of `E`). -/
noncomputable instance : CompleteSpace (P E m) := by
  cases m with
  | zero => exact IsometryEquiv.completeSpace (restrictedFinZeroIsometry (R := E) (fun _ : Fin 0 => (1 : ℝ)))
  | succ k => infer_instance

section AdicBridge

variable (t : E) (htu : IsUnit t) (ht1 : ‖t‖ < 1) (ht0 : 0 < ‖t‖)
  (hscale : ∀ x : E, ‖t * x‖ = ‖t‖ * ‖x‖)

theorem norm_coeff_le_gauss (F : P E m) (s : Fin m →₀ ℕ) :
    ‖MvPowerSeries.coeff s F.1‖ ≤ ‖F‖ := by
  have h := MvPowerSeries.le_gaussNorm _ _ _ (MvRestricted.hasGaussNorm _ F) s
  rw [finsupp_prod_one, mul_one] at h
  rw [MvRestricted.norm_eq]
  exact h

/-- Superlevel sets of a restricted series are finite. -/
theorem finite_setOf_le_norm_coeff (F : P E m) {ε : ℝ} (hε : 0 < ε) :
    {s : Fin m →₀ ℕ | ε ≤ ‖MvPowerSeries.coeff s F.1‖}.Finite := by
  have hF : MvPowerSeries.IsRestrictedGauss (fun _ : Fin m => (1 : ℝ)) F.1 := F.2
  rw [MvPowerSeries.IsRestrictedGauss] at hF
  have hev := hF.eventually (eventually_lt_nhds hε (a := (0 : ℝ)))
  rw [Filter.eventually_cofinite] at hev
  refine hev.subset fun s hs => ?_
  rw [Set.mem_setOf_eq] at hs
  show ¬ _
  rw [finsupp_prod_one, mul_one]
  exact not_lt.mpr hs

/-- The polynomial subring with unit-ball coefficients, mapped into `P_E`. -/
noncomputable def polyBall : MvPolynomial (Fin m) ↥(unitBall E) →+* P E m :=
  (polyToP (E := E) (m := m)).comp (MvPolynomial.map (unitBall E).subtype)

theorem coeff_polyBall (q : MvPolynomial (Fin m) ↥(unitBall E)) (s : Fin m →₀ ℕ) :
    MvPowerSeries.coeff s ((polyBall (E := E) (m := m) q).1) =
      ((MvPolynomial.coeff s q : ↥(unitBall E)) : E) := by
  show MvPowerSeries.coeff s ((polyToP (MvPolynomial.map (unitBall E).subtype q)).1) = _
  rw [coeff_polyToP, MvPolynomial.coeff_map]
  rfl

theorem norm_polyBall_le_one (q : MvPolynomial (Fin m) ↥(unitBall E)) :
    ‖polyBall (E := E) (m := m) q‖ ≤ 1 := by
  rw [MvRestricted.norm_eq, MvPowerSeries.gaussNorm]
  refine Real.iSup_le (fun s => ?_) zero_le_one
  rw [finsupp_prod_one, mul_one, coeff_polyBall]
  exact (MvPolynomial.coeff s q).2

include hscale

/-- Membership of `I₀ⁿ`-elements is norm-detected after mapping to `P_E`. -/
theorem norm_polyBall_le_of_mem_span_pow (n : ℕ)
    (q : MvPolynomial (Fin m) ↥(unitBall E))
    (hq : q ∈ Ideal.span {MvPolynomial.C (⟨t, ht1.le⟩ : ↥(unitBall E))} ^ n) :
    ‖polyBall (E := E) (m := m) q‖ ≤ ‖t‖ ^ n := by
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at hq
  obtain ⟨q', hq'⟩ := hq
  rw [← hq', map_mul, map_pow]
  have hC : polyBall (E := E) (m := m)
      (MvPolynomial.C (⟨t, ht1.le⟩ : ↥(unitBall E))) = polyToP (MvPolynomial.C t) := by
    show polyToP (MvPolynomial.map (unitBall E).subtype
      (MvPolynomial.C (⟨t, ht1.le⟩ : ↥(unitBall E)))) = _
    rw [MvPolynomial.map_C]
    rfl
  rw [hC, mul_comm, norm_pow_mul_of_scale (E := P E m)
    (fun G => by rw [norm_tP t hscale]; exact norm_tP_mul t hscale G) n, norm_tP t hscale]
  calc ‖t‖ ^ n * ‖polyBall (E := E) (m := m) q'‖
      ≤ ‖t‖ ^ n * 1 :=
        mul_le_mul_of_nonneg_left (norm_polyBall_le_one q') (pow_nonneg (norm_nonneg t) n)
    _ = ‖t‖ ^ n := mul_one _

omit hscale

/-- The level-`n` truncation of a unit-ball restricted series, as a polynomial with
unit-ball coefficients. -/
noncomputable def trnc (n : ℕ) (F : ↥(unitBall (P E m))) :
    MvPolynomial (Fin m) ↥(unitBall E) :=
  ∑ s ∈ (finite_setOf_le_norm_coeff F.1 (pow_pos ht0 n)).toFinset,
    MvPolynomial.monomial s (⟨MvPowerSeries.coeff s F.1.1,
      (norm_coeff_le_gauss F.1 s).trans F.2⟩ : ↥(unitBall E))

theorem coeff_polyBall_trnc (n : ℕ) (F : ↥(unitBall (P E m))) (s : Fin m →₀ ℕ) :
    MvPowerSeries.coeff s ((polyBall (trnc t ht0 n F) : P E m).1) =
      if ‖t‖ ^ n ≤ ‖MvPowerSeries.coeff s F.1.1‖ then MvPowerSeries.coeff s F.1.1 else 0 := by
  classical
  rw [coeff_polyBall]
  unfold trnc
  rw [MvPolynomial.coeff_sum]
  by_cases hs : ‖t‖ ^ n ≤ ‖MvPowerSeries.coeff s F.1.1‖
  · rw [if_pos hs, Finset.sum_eq_single s (fun b _ hb => by
      rw [MvPolynomial.coeff_monomial, if_neg hb]) (fun hns => absurd
        ((finite_setOf_le_norm_coeff F.1 (pow_pos ht0 n)).mem_toFinset.mpr hs) hns),
      MvPolynomial.coeff_monomial, if_pos rfl]
  · rw [if_neg hs, Finset.sum_eq_zero fun b hb => ?_]
    · rfl
    · rw [MvPolynomial.coeff_monomial, if_neg]
      intro hbs
      rw [hbs] at hb
      exact hs ((finite_setOf_le_norm_coeff F.1 (pow_pos ht0 n)).mem_toFinset.mp hb)

/-- The truncation tail is `‖t‖ⁿ`-small. -/
theorem norm_sub_polyBall_trnc_le (n : ℕ) (F : ↥(unitBall (P E m))) :
    ‖F.1 - polyBall (trnc t ht0 n F)‖ ≤ ‖t‖ ^ n := by
  rw [MvRestricted.norm_eq, MvPowerSeries.gaussNorm]
  refine Real.iSup_le (fun s => ?_) (pow_nonneg (norm_nonneg t) n)
  rw [finsupp_prod_one, mul_one]
  show ‖MvPowerSeries.coeff s ((F.1 - polyBall (trnc t ht0 n F) : P E m).1)‖ ≤ _
  rw [show ((F.1 - polyBall (trnc t ht0 n F) : P E m)).1 =
    F.1.1 - (polyBall (trnc t ht0 n F) : P E m).1 from rfl, map_sub, coeff_polyBall_trnc]
  by_cases hs : ‖t‖ ^ n ≤ ‖MvPowerSeries.coeff s F.1.1‖
  · rw [if_pos hs, sub_self, norm_zero]
    exact pow_nonneg (norm_nonneg t) n
  · rw [if_neg hs, sub_zero]
    exact (not_le.mp hs).le

include htu hscale

/-- The workhorse: any `‖t‖ⁿ`-close polynomial has the same level-`n` class as the
truncation. -/
theorem mk_trnc_eq (n : ℕ) (F : ↥(unitBall (P E m)))
    (q : MvPolynomial (Fin m) ↥(unitBall E)) (hq : ‖F.1 - polyBall q‖ ≤ ‖t‖ ^ n) :
    Ideal.Quotient.mk ((Ideal.span {(MvPolynomial.C (⟨t, ht1.le⟩ : ↥(unitBall E)) :
          MvPolynomial (Fin m) ↥(unitBall E))}) ^ n • ⊤ :
        Ideal (MvPolynomial (Fin m) ↥(unitBall E))) (trnc t ht0 n F) =
      Ideal.Quotient.mk ((Ideal.span {(MvPolynomial.C (⟨t, ht1.le⟩ : ↥(unitBall E)) :
          MvPolynomial (Fin m) ↥(unitBall E))}) ^ n • ⊤ :
        Ideal (MvPolynomial (Fin m) ↥(unitBall E))) q := by
  rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem]
  have hsmul : ((Ideal.span {(MvPolynomial.C (⟨t, ht1.le⟩ : ↥(unitBall E)) :
          MvPolynomial (Fin m) ↥(unitBall E))}) ^ n • ⊤ :
      Ideal (MvPolynomial (Fin m) ↥(unitBall E))) =
      (Ideal.span {(MvPolynomial.C (⟨t, ht1.le⟩ : ↥(unitBall E)) :
          MvPolynomial (Fin m) ↥(unitBall E))}) ^ n := by
    ext x
    simp
  rw [hsmul]
  refine mem_span_C_pow_of_coeff_norm_le htu ht1.le ht0 hscale n _ (fun s => ?_)
  have hval : ((MvPolynomial.coeff s (trnc t ht0 n F - q) : ↥(unitBall E)) : E) =
      MvPowerSeries.coeff s ((polyBall (trnc t ht0 n F) - polyBall q : P E m).1) := by
    rw [show ((polyBall (trnc t ht0 n F) - polyBall q : P E m)).1 =
      (polyBall (trnc t ht0 n F) : P E m).1 - (polyBall q : P E m).1 from rfl, map_sub,
      coeff_polyBall, coeff_polyBall, MvPolynomial.coeff_sub]
    rfl
  show ‖((MvPolynomial.coeff s (trnc t ht0 n F - q) : ↥(unitBall E)) : E)‖ ≤ _
  rw [hval]
  refine (norm_coeff_le_gauss _ s).trans ?_
  have htri : ‖(polyBall (trnc t ht0 n F) - polyBall q : P E m)‖ ≤
      max ‖polyBall (trnc t ht0 n F) - F.1‖ ‖F.1 - polyBall q‖ := by
    have h := IsUltrametricDist.norm_add_le_max
      (polyBall (trnc t ht0 n F) - F.1) (F.1 - polyBall q)
    rwa [sub_add_sub_cancel] at h
  refine htri.trans (max_le ?_ hq)
  rw [norm_sub_rev]
  exact norm_sub_polyBall_trnc_le t ht0 n F

omit htu hscale

/-- `I₀ = (C t₀) ⊂ E₀[T]`, the constant ideal at the pseudouniformizer.

v4.33: the membership witness is threaded through `mem_unitBall_iff` (an `Iff.rfl`) so
the subtype literal carries a proof of the syntactic type `t ∈ unitBall E` — a bare
`ht1.le : ‖t‖ ≤ 1` types only at default transparency, and since `I0` is a (reducible)
`abbrev` the ill-typed literal would leak into every consumer goal and choke
`kabstract` there. -/
noncomputable abbrev I0 : Ideal (MvPolynomial (Fin m) ↥(unitBall E)) :=
  Ideal.span {(MvPolynomial.C (⟨t, (mem_unitBall_iff (E := E) t).mpr ht1.le⟩ :
      ↥(unitBall E)) :
    MvPolynomial (Fin m) ↥(unitBall E))}

theorem I0_pow_smul_top (n : ℕ) :
    ((I0 (E := E) (m := m) t ht1) ^ n • ⊤ : Ideal (MvPolynomial (Fin m) ↥(unitBall E))) =
      (I0 (E := E) (m := m) t ht1) ^ n := by
  ext x
  simp

include htu hscale

-- v4.33: the `⟨trnc …, ⋯⟩`-literals and `⟨t, ht1.le⟩`-witnesses throughout this layer
-- type only at default transparency; restore pre-v4.33 defeq behaviour for the
-- `kabstract`-heavy proof (established bump-repair pattern).
/-- The truncation-classes ring homomorphism into the adic completion. -/
noncomputable def toAdic : ↥(unitBall (P E m)) →+*
    AdicCompletion (I0 (E := E) (m := m) t ht1) (MvPolynomial (Fin m) ↥(unitBall E)) where
  toFun F := ⟨fun n => Ideal.Quotient.mk _ (trnc t ht0 n F), by
    intro a b hab
    show AdicCompletion.transitionMap _ _ hab (Ideal.Quotient.mk _ (trnc t ht0 b F)) = _
    rw [AdicCompletion.transitionMap_ideal_mk]
    exact (mk_trnc_eq t htu ht1 ht0 hscale a F (trnc t ht0 b F)
      ((norm_sub_polyBall_trnc_le t ht0 b F).trans
        (pow_le_pow_of_le_one (norm_nonneg t) ht1.le hab))).symm⟩
  map_one' := Subtype.ext (funext fun n => by
    show Ideal.Quotient.mk _ (trnc t ht0 n 1) = 1
    rw [← map_one (Ideal.Quotient.mk ((I0 (E := E) (m := m) t ht1) ^ n • ⊤ :
      Ideal (MvPolynomial (Fin m) ↥(unitBall E))))]
    exact mk_trnc_eq t htu ht1 ht0 hscale n 1 1 (by
      rw [map_one]
      show ‖(1 : P E m) - 1‖ ≤ _
      rw [sub_self, norm_zero]
      exact pow_nonneg (norm_nonneg t) n))
  map_mul' F G := Subtype.ext (funext fun n => by
    show Ideal.Quotient.mk _ (trnc t ht0 n (F * G)) = _
    rw [AdicCompletion.val_mul]
    show _ = Ideal.Quotient.mk _ (trnc t ht0 n F) * Ideal.Quotient.mk _ (trnc t ht0 n G)
    rw [← map_mul (Ideal.Quotient.mk ((I0 (E := E) (m := m) t ht1) ^ n • ⊤ :
      Ideal (MvPolynomial (Fin m) ↥(unitBall E))))]
    refine mk_trnc_eq t htu ht1 ht0 hscale n (F * G) (trnc t ht0 n F * trnc t ht0 n G) ?_
    rw [map_mul]
    show ‖F.1 * G.1 - polyBall (trnc t ht0 n F) * polyBall (trnc t ht0 n G)‖ ≤ _
    rw [show F.1 * G.1 - polyBall (trnc t ht0 n F) * polyBall (trnc t ht0 n G) =
      F.1 * (G.1 - polyBall (trnc t ht0 n G)) +
        (F.1 - polyBall (trnc t ht0 n F)) * polyBall (trnc t ht0 n G) from by ring]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · calc ‖F.1 * (G.1 - polyBall (trnc t ht0 n G))‖
          ≤ ‖F.1‖ * ‖G.1 - polyBall (trnc t ht0 n G)‖ := norm_mul_le _ _
        _ ≤ 1 * ‖t‖ ^ n := mul_le_mul F.2 (norm_sub_polyBall_trnc_le t ht0 n G)
            (norm_nonneg _) zero_le_one
        _ = ‖t‖ ^ n := one_mul _
    · calc ‖(F.1 - polyBall (trnc t ht0 n F)) * polyBall (trnc t ht0 n G)‖
          ≤ ‖F.1 - polyBall (trnc t ht0 n F)‖ * ‖polyBall (trnc t ht0 n G)‖ :=
            norm_mul_le _ _
        _ ≤ ‖t‖ ^ n * 1 := mul_le_mul (norm_sub_polyBall_trnc_le t ht0 n F)
            (norm_polyBall_le_one _) (norm_nonneg _) (pow_nonneg (norm_nonneg t) n)
        _ = ‖t‖ ^ n := mul_one _)
  map_zero' := Subtype.ext (funext fun n => by
    show Ideal.Quotient.mk _ (trnc t ht0 n 0) = 0
    rw [← map_zero (Ideal.Quotient.mk ((I0 (E := E) (m := m) t ht1) ^ n • ⊤ :
      Ideal (MvPolynomial (Fin m) ↥(unitBall E))))]
    exact mk_trnc_eq t htu ht1 ht0 hscale n 0 0 (by
      rw [map_zero]
      show ‖(0 : P E m) - 0‖ ≤ _
      rw [sub_self, norm_zero]
      exact pow_nonneg (norm_nonneg t) n))
  map_add' F G := Subtype.ext (funext fun n => by
    show Ideal.Quotient.mk _ (trnc t ht0 n (F + G)) = _
    show _ = Ideal.Quotient.mk _ (trnc t ht0 n F) + Ideal.Quotient.mk _ (trnc t ht0 n G)
    rw [← map_add (Ideal.Quotient.mk ((I0 (E := E) (m := m) t ht1) ^ n • ⊤ :
      Ideal (MvPolynomial (Fin m) ↥(unitBall E))))]
    refine mk_trnc_eq t htu ht1 ht0 hscale n (F + G) (trnc t ht0 n F + trnc t ht0 n G) ?_
    rw [map_add]
    show ‖F.1 + G.1 - (polyBall (trnc t ht0 n F) + polyBall (trnc t ht0 n G))‖ ≤ _
    rw [show F.1 + G.1 - (polyBall (trnc t ht0 n F) + polyBall (trnc t ht0 n G)) =
      (F.1 - polyBall (trnc t ht0 n F)) + (G.1 - polyBall (trnc t ht0 n G)) from by ring]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans
      (max_le (norm_sub_polyBall_trnc_le t ht0 n F) (norm_sub_polyBall_trnc_le t ht0 n G)))

theorem toAdic_injective :
    Function.Injective (toAdic (E := E) (m := m) t htu ht1 ht0 hscale) := by
  intro F G h
  have hn : ∀ n : ℕ, ‖F.1 - G.1‖ ≤ ‖t‖ ^ n := fun n => by
    have hcomp := congrFun (congrArg Subtype.val h) n
    show ‖F.1 - G.1‖ ≤ ‖t‖ ^ n
    have hmk : Ideal.Quotient.mk ((I0 (E := E) (m := m) t ht1) ^ n • ⊤ :
        Ideal (MvPolynomial (Fin m) ↥(unitBall E))) (trnc t ht0 n F) =
        Ideal.Quotient.mk ((I0 (E := E) (m := m) t ht1) ^ n • ⊤ :
        Ideal (MvPolynomial (Fin m) ↥(unitBall E))) (trnc t ht0 n G) := hcomp
    rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem, I0_pow_smul_top] at hmk
    have hb := norm_polyBall_le_of_mem_span_pow t ht1 hscale n _ hmk
    rw [map_sub] at hb
    have h1 : ‖F.1 - G.1‖ ≤ max ‖F.1 - polyBall (trnc t ht0 n F)‖
        (max ‖polyBall (trnc t ht0 n F) - polyBall (trnc t ht0 n G)‖
          ‖polyBall (trnc t ht0 n G) - G.1‖) := by
      have hstep : F.1 - G.1 = (F.1 - polyBall (trnc t ht0 n F)) +
          ((polyBall (trnc t ht0 n F) - polyBall (trnc t ht0 n G)) +
            (polyBall (trnc t ht0 n G) - G.1)) := by ring
      rw [hstep]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans
        (max_le_max le_rfl (IsUltrametricDist.norm_add_le_max _ _))
    refine h1.trans (max_le (norm_sub_polyBall_trnc_le t ht0 n F) (max_le hb ?_))
    rw [norm_sub_rev]
    exact norm_sub_polyBall_trnc_le t ht0 n G
  have h0 : ‖F.1 - G.1‖ ≤ 0 :=
    ge_of_tendsto (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg t) ht1)
      (Filter.Eventually.of_forall hn)
  refine Subtype.ext ?_
  rw [← sub_eq_zero]
  exact norm_le_zero_iff.mp h0

theorem toAdic_surjective :
    Function.Surjective (toAdic (E := E) (m := m) t htu ht1 ht0 hscale) := by
  intro x
  have hrep : ∀ n, ∃ q : MvPolynomial (Fin m) ↥(unitBall E),
      Ideal.Quotient.mk ((I0 (E := E) (m := m) t ht1) ^ n • ⊤ :
        Ideal (MvPolynomial (Fin m) ↥(unitBall E))) q = x.val n := fun n =>
    Ideal.Quotient.mk_surjective (x.val n)
  choose q hq using hrep
  have hcons : ∀ n, ‖polyBall (q (n + 1)) - polyBall (q n)‖ ≤ ‖t‖ ^ n := fun n => by
    have htrans := x.property (Nat.le_succ n)
    rw [← hq (n + 1), ← hq n, AdicCompletion.transitionMap_ideal_mk,
      Ideal.Quotient.mk_eq_mk_iff_sub_mem, I0_pow_smul_top] at htrans
    have hb := norm_polyBall_le_of_mem_span_pow t ht1 hscale n _ htrans
    rwa [map_sub] at hb
  set u : ℕ → P E m := fun n => polyBall (q n) with hu
  have hcauchy : CauchySeq u := by
    refine cauchySeq_of_le_geometric ‖t‖ 1 ht1 fun n => ?_
    rw [dist_eq_norm, one_mul, norm_sub_rev]
    exact hcons n
  obtain ⟨F, hF⟩ := cauchySeq_tendsto_of_complete hcauchy
  have hdist : ∀ n k, n ≤ k → ‖u k - u n‖ ≤ ‖t‖ ^ n := by
    intro n k hnk
    induction k with
    | zero =>
      have hn0 : n = 0 := Nat.le_zero.mp hnk
      rw [hn0, sub_self, norm_zero]
      exact pow_nonneg (norm_nonneg t) 0
    | succ j ih =>
      rcases Nat.lt_succ_iff_lt_or_eq.mp (Nat.lt_succ_of_le hnk) with hlt | rfl
      · have hnj : n ≤ j := Nat.lt_succ_iff.mp hlt
        have hstep : u (j + 1) - u n = (u (j + 1) - u j) + (u j - u n) := by ring
        rw [hstep]
        refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ (ih hnj))
        exact (hcons j).trans (pow_le_pow_of_le_one (norm_nonneg t) ht1.le hnj)
      · rw [sub_self, norm_zero]
        exact pow_nonneg (norm_nonneg t) _
  have hFn : ∀ n, ‖F - u n‖ ≤ ‖t‖ ^ n := fun n => by
    have hten : Filter.Tendsto (fun k => ‖u k - u n‖) Filter.atTop (𝓝 ‖F - u n‖) :=
      ((hF.sub tendsto_const_nhds).norm)
    exact le_of_tendsto hten (Filter.eventually_atTop.mpr ⟨n, fun k hk => hdist n k hk⟩)
  have hFball : ‖F‖ ≤ 1 := by
    have h := IsUltrametricDist.norm_add_le_max (F - u 0) (u 0)
    rw [sub_add_cancel] at h
    refine h.trans (max_le ?_ (norm_polyBall_le_one (q 0)))
    simpa using hFn 0
  refine ⟨⟨F, hFball⟩, Subtype.ext (funext fun n => ?_)⟩
  show Ideal.Quotient.mk _ (trnc t ht0 n ⟨F, hFball⟩) = x.val n
  rw [← hq n]
  exact mk_trnc_eq t htu ht1 ht0 hscale n ⟨F, hFball⟩ (q n) (hFn n)

/-- **The (4.4) identification**: the unit ball of `E⟨T₁,…,T_m⟩` is the `(t)`-adic
completion of `E₀[T₁,…,T_m]` ([FJP] (4.4)). -/
noncomputable def ballAdicEquiv : ↥(unitBall (P E m)) ≃+*
    AdicCompletion (I0 (E := E) (m := m) t ht1) (MvPolynomial (Fin m) ↥(unitBall E)) :=
  RingEquiv.ofBijective (toAdic (E := E) (m := m) t htu ht1 ht0 hscale)
    ⟨toAdic_injective t htu ht1 ht0 hscale, toAdic_surjective t htu ht1 ht0 hscale⟩

end AdicBridge

/-- The base change `E[T] → E⟨T⟩` is **flat** ([FJP] Lemma 4.2, proof: "Noetherian adic
completion is flat [8, Lemma 10.97.2, Tag 00MB], and localization preserves flatness";
via the (4.4) identification `P_E ≅ (E₀[T])^∧_ϖ[1/ϖ]` for the noetherian unit ball `E₀`).
Signature completion (recorded on the board): the scaling pseudouniformizer bundle
`(t, htu, ht1, ht0, hscale)` of the Tate vertex, exactly as in `unitBallPod`. -/
theorem flat_polyToP (hE₀ : IsNoetherianRing (unitBall E))
    (t : E) (htu : IsUnit t) (ht1 : ‖t‖ < 1) (ht0 : 0 < ‖t‖)
    (hscale : ∀ x : E, ‖t * x‖ = ‖t‖ * ‖x‖) :
    letI : Algebra (MvPolynomial (Fin m) E) (P E m) := (polyToP (E := E) (m := m)).toAlgebra
    Module.Flat (MvPolynomial (Fin m) E) (P E m) := by
  classical
  letI : Algebra (MvPolynomial (Fin m) E) (P E m) := (polyToP (E := E) (m := m)).toAlgebra
  haveI hE₀' : IsNoetherianRing ↥(unitBall E) := hE₀
  haveI hR₀ : IsNoetherianRing (MvPolynomial (Fin m) ↥(unitBall E)) := inferInstance
  -- the ball-valued polynomial hom and its ball corestriction
  set gB : MvPolynomial (Fin m) ↥(unitBall E) →+* ↥(unitBall (P E m)) :=
    RingHom.codRestrict (polyBall (E := E) (m := m)) (unitBall (P E m))
      (fun q => norm_polyBall_le_one q) with hgB
  letI : Algebra (MvPolynomial (Fin m) ↥(unitBall E)) (MvPolynomial (Fin m) E) :=
    (MvPolynomial.map (unitBall E).subtype).toAlgebra
  letI : Algebra (MvPolynomial (Fin m) ↥(unitBall E)) ↥(unitBall (P E m)) := gB.toAlgebra
  letI : Algebra ↥(unitBall (P E m)) (P E m) := (unitBall (P E m)).subtype.toAlgebra
  letI : Algebra (MvPolynomial (Fin m) ↥(unitBall E)) (P E m) :=
    (polyBall (E := E) (m := m)).toAlgebra
  haveI hT1 : IsScalarTower (MvPolynomial (Fin m) ↥(unitBall E))
      (MvPolynomial (Fin m) E) (P E m) :=
    IsScalarTower.of_algebraMap_eq (fun q => rfl)
  haveI hT2 : IsScalarTower (MvPolynomial (Fin m) ↥(unitBall E))
      ↥(unitBall (P E m)) (P E m) :=
    IsScalarTower.of_algebraMap_eq (fun q => rfl)
  -- Step B: the ball is flat over `R₀` (adic completion of a noetherian ring)
  haveI hflatB : Module.Flat (MvPolynomial (Fin m) ↥(unitBall E)) ↥(unitBall (P E m)) := by
    have hcompat : ∀ q : MvPolynomial (Fin m) ↥(unitBall E),
        ballAdicEquiv t htu ht1 ht0 hscale (gB q) =
          algebraMap (MvPolynomial (Fin m) ↥(unitBall E))
            (AdicCompletion (I0 (E := E) (m := m) t ht1)
              (MvPolynomial (Fin m) ↥(unitBall E))) q := fun q => by
      refine Subtype.ext (funext fun n => ?_)
      show Ideal.Quotient.mk _ (trnc t ht0 n (gB q)) = _
      have hval : (algebraMap (MvPolynomial (Fin m) ↥(unitBall E))
          (AdicCompletion (I0 (E := E) (m := m) t ht1)
            (MvPolynomial (Fin m) ↥(unitBall E))) q).val n =
          Ideal.Quotient.mk ((I0 (E := E) (m := m) t ht1) ^ n • ⊤ :
            Ideal (MvPolynomial (Fin m) ↥(unitBall E))) q := rfl
      rw [hval]
      refine mk_trnc_eq t htu ht1 ht0 hscale n (gB q) q ?_
      show ‖polyBall q - polyBall q‖ ≤ _
      rw [sub_self, norm_zero]
      exact pow_nonneg (norm_nonneg t) n
    -- transport flatness along the algebra equivalence
    let e : AdicCompletion (I0 (E := E) (m := m) t ht1)
        (MvPolynomial (Fin m) ↥(unitBall E)) ≃ₐ[MvPolynomial (Fin m) ↥(unitBall E)]
        ↥(unitBall (P E m)) :=
      AlgEquiv.ofRingEquiv (f := (ballAdicEquiv t htu ht1 ht0 hscale).symm)
        (fun q => by
          rw [← hcompat q]
          exact RingEquiv.symm_apply_apply _ _)
    exact Module.Flat.of_linearEquiv e.symm.toLinearEquiv
  -- Step C: localization instances
  set S₀ : Submonoid (MvPolynomial (Fin m) ↥(unitBall E)) :=
    Submonoid.powers (MvPolynomial.C (⟨t, ht1.le⟩ : ↥(unitBall E))) with hS₀
  haveI hloc1 : IsLocalization S₀ (MvPolynomial (Fin m) E) := by
    refine ⟨⟨?_, ?_, ?_⟩⟩
    · rintro ⟨y, hy⟩
      obtain ⟨k, hk⟩ := hy
      have heq : algebraMap (MvPolynomial (Fin m) ↥(unitBall E)) (MvPolynomial (Fin m) E) y =
          MvPolynomial.C t ^ k := by
        rw [← hk]
        show MvPolynomial.map (unitBall E).subtype _ = _
        rw [map_pow, MvPolynomial.map_C]
        rfl
      show IsUnit (algebraMap (MvPolynomial (Fin m) ↥(unitBall E)) (MvPolynomial (Fin m) E) y)
      rw [heq]
      exact (htu.map MvPolynomial.C).pow k
    · intro z
      have hex : ∀ s : Fin m →₀ ℕ, ∃ n : ℕ, ‖t ^ n * MvPolynomial.coeff s z‖ ≤ 1 := fun s => by
        rcases eq_or_ne (MvPolynomial.coeff s z) 0 with h0 | h0
        · exact ⟨0, by rw [h0, mul_zero, norm_zero]; exact zero_le_one⟩
        · have hpos : 0 < ‖MvPolynomial.coeff s z‖ := norm_pos_iff.mpr h0
          obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (inv_pos.mpr hpos) ht1
          refine ⟨n, ?_⟩
          rw [norm_pow_mul_of_scale (E := E) hscale n]
          calc ‖t‖ ^ n * ‖MvPolynomial.coeff s z‖
              ≤ ‖MvPolynomial.coeff s z‖⁻¹ * ‖MvPolynomial.coeff s z‖ :=
                mul_le_mul_of_nonneg_right hn.le (norm_nonneg _)
            _ = 1 := inv_mul_cancel₀ (ne_of_gt hpos)
      choose nf hnf using hex
      set N := z.support.sup nf with hN
      have hball : ∀ s : Fin m →₀ ℕ, ‖t ^ N * MvPolynomial.coeff s z‖ ≤ 1 := fun s => by
        by_cases hs : s ∈ z.support
        · have hle : nf s ≤ N := Finset.le_sup hs
          rw [show N = (N - nf s) + nf s by omega, pow_add, mul_assoc,
            norm_pow_mul_of_scale (E := E) hscale (N - nf s)]
          calc ‖t‖ ^ (N - nf s) * ‖t ^ nf s * MvPolynomial.coeff s z‖
              ≤ 1 * 1 := mul_le_mul (pow_le_one₀ (norm_nonneg t) ht1.le) (hnf s)
                (norm_nonneg _) zero_le_one
            _ = 1 := one_mul 1
        · rw [MvPolynomial.notMem_support_iff.mp hs, mul_zero, norm_zero]
          exact zero_le_one
      refine ⟨(∑ s ∈ z.support, MvPolynomial.monomial s
        (⟨t ^ N * MvPolynomial.coeff s z, hball s⟩ : ↥(unitBall E)),
        ⟨MvPolynomial.C (⟨t, ht1.le⟩ : ↥(unitBall E)) ^ N, ⟨N, rfl⟩⟩), ?_⟩
      show z * algebraMap (MvPolynomial (Fin m) ↥(unitBall E)) (MvPolynomial (Fin m) E)
          (MvPolynomial.C (⟨t, ht1.le⟩ : ↥(unitBall E)) ^ N) = _
      have hCt : algebraMap (MvPolynomial (Fin m) ↥(unitBall E)) (MvPolynomial (Fin m) E)
          (MvPolynomial.C (⟨t, ht1.le⟩ : ↥(unitBall E)) ^ N) = MvPolynomial.C t ^ N := by
        show MvPolynomial.map (unitBall E).subtype _ = _
        rw [map_pow, MvPolynomial.map_C]
        rfl
      rw [hCt, mul_comm z (MvPolynomial.C t ^ N)]
      refine MvPolynomial.ext _ _ fun s => ?_
      rw [← map_pow, MvPolynomial.coeff_C_mul]
      show _ = MvPolynomial.coeff s (MvPolynomial.map (unitBall E).subtype
        (∑ s ∈ z.support, MvPolynomial.monomial s
          (⟨t ^ N * MvPolynomial.coeff s z, hball s⟩ : ↥(unitBall E))))
      rw [MvPolynomial.coeff_map, MvPolynomial.coeff_sum]
      by_cases hs : s ∈ z.support
      · rw [Finset.sum_eq_single s (fun b _ hb => by
          rw [MvPolynomial.coeff_monomial, if_neg hb]) (fun hns => absurd hs hns),
          MvPolynomial.coeff_monomial, if_pos rfl]
        rfl
      · rw [MvPolynomial.notMem_support_iff.mp hs, mul_zero,
          Finset.sum_eq_zero fun b hb => by
            rw [MvPolynomial.coeff_monomial,
              if_neg (show ¬ b = s from fun hbs => hs (hbs ▸ hb))]]
        rfl
    · intro x y h
      refine ⟨1, ?_⟩
      have hinj : Function.Injective
          (MvPolynomial.map (σ := Fin m) (unitBall E).subtype) :=
        MvPolynomial.map_injective _ Subtype.val_injective
      rw [hinj h]
  -- Step D: `P_E` is the localized module of the ball along `S₀`
  haveI hloc2 : IsLocalization (Algebra.algebraMapSubmonoid ↥(unitBall (P E m)) S₀)
      (P E m) := by
    refine ⟨⟨?_, ?_, ?_⟩⟩
    · rintro ⟨y, ⟨w, hw, rfl⟩⟩
      obtain ⟨k, hk⟩ := hw
      show IsUnit ((unitBall (P E m)).subtype (gB w))
      have heq : (unitBall (P E m)).subtype (gB w) = polyBall (E := E) (m := m) w := rfl
      rw [heq, ← hk, map_pow]
      have hCt : polyBall (E := E) (m := m)
          (MvPolynomial.C (⟨t, ht1.le⟩ : ↥(unitBall E))) = polyToP (MvPolynomial.C t) := by
        show polyToP (MvPolynomial.map (unitBall E).subtype
          (MvPolynomial.C (⟨t, ht1.le⟩ : ↥(unitBall E)))) = _
        rw [MvPolynomial.map_C]
        rfl
      rw [hCt]
      exact (isUnit_tP t htu).pow k
    · intro F
      have hex : ∃ n : ℕ, ‖t‖ ^ n * ‖F‖ ≤ 1 := by
        rcases eq_or_ne ‖F‖ 0 with h0 | h0
        · exact ⟨0, by rw [h0, mul_zero]; exact zero_le_one⟩
        · have hpos : 0 < ‖F‖ := lt_of_le_of_ne (norm_nonneg F) (Ne.symm h0)
          obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (inv_pos.mpr hpos) ht1
          exact ⟨n, by
            calc ‖t‖ ^ n * ‖F‖ ≤ ‖F‖⁻¹ * ‖F‖ :=
                  mul_le_mul_of_nonneg_right hn.le (norm_nonneg _)
              _ = 1 := inv_mul_cancel₀ (ne_of_gt hpos)⟩
      obtain ⟨n, hn⟩ := hex
      have hmem : ‖polyToP (MvPolynomial.C t) ^ n * F‖ ≤ 1 := by
        rw [norm_pow_mul_of_scale (E := P E m)
          (fun G => by rw [norm_tP t hscale]; exact norm_tP_mul t hscale G) n,
          norm_tP t hscale]
        exact hn
      refine ⟨(⟨polyToP (MvPolynomial.C t) ^ n * F, hmem⟩,
        ⟨gB (MvPolynomial.C (⟨t, ht1.le⟩ : ↥(unitBall E)) ^ n),
          ⟨MvPolynomial.C (⟨t, ht1.le⟩ : ↥(unitBall E)) ^ n, ⟨n, rfl⟩, rfl⟩⟩), ?_⟩
      show F * (unitBall (P E m)).subtype (gB _) = (unitBall (P E m)).subtype _
      have hgBval : (unitBall (P E m)).subtype (gB (MvPolynomial.C
          (⟨t, ht1.le⟩ : ↥(unitBall E)) ^ n)) = polyToP (MvPolynomial.C t) ^ n := by
        show polyBall (E := E) (m := m)
          (MvPolynomial.C (⟨t, ht1.le⟩ : ↥(unitBall E)) ^ n) = _
        rw [map_pow]
        congr 1
        show polyToP (MvPolynomial.map (unitBall E).subtype
          (MvPolynomial.C (⟨t, ht1.le⟩ : ↥(unitBall E)))) = _
        rw [MvPolynomial.map_C]
        rfl
      rw [hgBval]
      show F * polyToP (MvPolynomial.C t) ^ n = polyToP (MvPolynomial.C t) ^ n * F
      ring
    · intro x y h
      refine ⟨1, ?_⟩
      have hinj : Function.Injective ((unitBall (P E m)).subtype) :=
        Subtype.val_injective
      rw [hinj h]
  -- Step E: base change along the localization and transport of flatness
  haveI hlocmod : IsLocalizedModule S₀
      ((IsScalarTower.toAlgHom (MvPolynomial (Fin m) ↥(unitBall E)) ↥(unitBall (P E m))
        (P E m)).toLinearMap) :=
    isLocalizedModule_iff_isLocalization.mpr hloc2
  have hBC := IsLocalizedModule.isBaseChange S₀ (MvPolynomial (Fin m) E)
    ((IsScalarTower.toAlgHom (MvPolynomial (Fin m) ↥(unitBall E)) ↥(unitBall (P E m))
      (P E m)).toLinearMap)
  exact Module.Flat.of_linearEquiv hBC.equiv.symm

end Restricted

end GraphKoszul

end FiniteJet
