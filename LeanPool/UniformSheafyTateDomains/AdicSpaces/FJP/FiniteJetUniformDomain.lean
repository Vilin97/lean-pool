/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanPool.UniformSheafyTateDomains.AdicSpaces.FJP.FiniteJetRings
import LeanPool.UniformSheafyTateDomains.AdicSpaces.Uniform

/-!
# 𝓐 is a uniform domain and is not noetherian ([FJP] Propositions 2.3, 2.4, and (5.2))

* **Prop 2.3**: the Gauss norm on `𝒞 = L⟨Q⟩` is multiplicative; `𝓐° = 𝓐₀` is the unit ball;
  hence `𝓐` is a complete uniform Tate ring and an integral domain.
* **(5.2)**: the maximal plus rings of 𝓑 and 𝓓 are `k°⟨W⟩ ⊕ Qk⟨W⟩` resp. `L° ⊕ QL` —
  power-boundedness depends only on the constant-jet component (`(f+Qg)ⁿ = fⁿ + nf^{n-1}Qg`).
* **Prop 2.4**: `𝓐` is not noetherian: the ideal `J = Q²𝒞 = ker(jB)` is not finitely
  generated, since `J/KJ ≅ L` over `𝓐/K ≅ k⟨W⟩` and `W⁻¹` is not integral over `k⟨W⟩`.
-/

open Filter Topology

namespace FiniteJet

open RestrictedLaurent TopologicalRing

variable (F : Type*) [Field F]

local notation "K" => LaurentSeries F

/-! ### Norm multiplicativity and the domain property ([FJP] Prop 2.3) -/

/-- The Gauss norm on `L = K⟨W,W⁻¹⟩` is multiplicative (specialisation of
`RestrictedLaurent.norm_mul_eq` to `K`). -/
theorem norm_L_mul (f g : L F) : ‖f * g‖ = ‖f‖ * ‖g‖ :=
  RestrictedLaurent.norm_mul_eq f g

theorem norm_L_eq_zero {f : L F} (hf : ‖f‖ = 0) : f = 0 :=
  norm_eq_zero.mp hf

section GenericMult

variable {R : Type*} [NormedCommRing R] [IsUltrametricDist R] [NormOneClass R]

/-- Coefficient decay of a radius-one restricted series, super-level-set form. -/
theorem finite_setOf_le_norm_psCoeff (f : PowerSeries.Restricted R (1 : ℝ)) {ε : ℝ}
    (hε : 0 < ε) : {n : ℕ | ε ≤ ‖PowerSeries.coeff n f.1‖}.Finite := by
  have h := (Restricted.isRestricted_iff_cofinite (R := R) 1).mp f.2
  simp only [one_pow, mul_one] at h
  have hev := h.eventually (eventually_lt_nhds hε (a := (0 : ℝ)))
  rw [Filter.eventually_cofinite] at hev
  exact hev.subset fun n hn => by simpa using not_lt.mpr hn

theorem norm_psCoeff_le (f : PowerSeries.Restricted R (1 : ℝ)) (n : ℕ) :
    ‖PowerSeries.coeff n f.1‖ ≤ ‖f‖ := by
  have h := PowerSeries.le_gaussNorm norm 1 f.1 (Restricted.hasGaussNorm (R := R) 1 f) n
  rwa [one_pow, mul_one] at h

/-- The Gauss norm of a nonzero radius-one restricted series is attained. -/
theorem exists_norm_psCoeff_eq (f : PowerSeries.Restricted R (1 : ℝ)) (hf : f ≠ 0) :
    ∃ n : ℕ, ‖f‖ = ‖PowerSeries.coeff n f.1‖ ∧ PowerSeries.coeff n f.1 ≠ 0 := by
  have hne : ∃ n, PowerSeries.coeff n f.1 ≠ 0 := by
    by_contra h
    push Not at h
    refine hf (Subtype.ext (PowerSeries.ext fun n => ?_))
    rw [show (0 : PowerSeries.Restricted R (1 : ℝ)).1 = (0 : PowerSeries R) from rfl,
      map_zero]
    exact h n
  obtain ⟨n₀, hn₀⟩ := hne
  have hpos : 0 < ‖PowerSeries.coeff n₀ f.1‖ := norm_pos_iff.mpr hn₀
  obtain ⟨n, hnS, hnmax⟩ := Set.exists_max_image _ (fun n => ‖PowerSeries.coeff n f.1‖)
    (finite_setOf_le_norm_psCoeff f hpos)
    ⟨n₀, show ‖PowerSeries.coeff n₀ f.1‖ ≤ ‖PowerSeries.coeff n₀ f.1‖ from le_rfl⟩
  refine ⟨n, le_antisymm ?_ (norm_psCoeff_le f n), ?_⟩
  · rw [Restricted.norm_eq, PowerSeries.gaussNorm_eq]
    refine Real.iSup_le (fun m => ?_) (norm_nonneg _)
    rw [one_pow, mul_one]
    by_cases hm : ‖PowerSeries.coeff n₀ f.1‖ ≤ ‖PowerSeries.coeff m f.1‖
    · exact hnmax m hm
    · exact ((not_le.mp hm).le.trans hnS)
  · exact norm_pos_iff.mp (lt_of_lt_of_le hpos hnS)

/-- Multiplicativity of the radius-one Gauss norm over a base with multiplicative,
zero-faithful norm (the minimal-achiever argument through the vendored
`PowerSeries.gaussNorm_mul_eq_mul`). -/
theorem norm_restricted_mul (hmul : ∀ a b : R, ‖a * b‖ = ‖a‖ * ‖b‖)
    (hzero : ∀ x : R, ‖x‖ = 0 → x = 0)
    (f g : PowerSeries.Restricted R (1 : ℝ)) : ‖f * g‖ = ‖f‖ * ‖g‖ := by
  classical
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  rcases eq_or_ne g 0 with rfl | hg
  · simp
  obtain ⟨nf, hnf_eq, hnf_ne⟩ := exists_norm_psCoeff_eq f hf
  obtain ⟨ng, hng_eq, hng_ne⟩ := exists_norm_psCoeff_eq g hg
  have hposf : 0 < ‖f‖ := hnf_eq ▸ norm_pos_iff.mpr hnf_ne
  have hposg : 0 < ‖g‖ := hng_eq ▸ norm_pos_iff.mpr hng_ne
  have hAf : {n : ℕ | ‖PowerSeries.coeff n f.1‖ = ‖f‖}.Finite :=
    (finite_setOf_le_norm_psCoeff f hposf).subset fun n hn => by
      rw [Set.mem_setOf_eq] at hn ⊢; rw [hn]
  have hAg : {n : ℕ | ‖PowerSeries.coeff n g.1‖ = ‖g‖}.Finite :=
    (finite_setOf_le_norm_psCoeff g hposg).subset fun n hn => by
      rw [Set.mem_setOf_eq] at hn ⊢; rw [hn]
  obtain ⟨i, hiA, himin⟩ := Set.exists_min_image _ (fun n : ℕ => n) hAf ⟨nf, hnf_eq.symm⟩
  obtain ⟨j, hjA, hjmin⟩ := Set.exists_min_image _ (fun n : ℕ => n) hAg ⟨ng, hng_eq.symm⟩
  rw [Set.mem_setOf_eq] at hiA hjA
  rw [Restricted.norm_eq (R := R) 1 (f * g), Restricted.norm_eq (R := R) 1 f,
    Restricted.norm_eq (R := R) 1 g,
    show (f * g : PowerSeries.Restricted R (1 : ℝ)).1 = f.1 * g.1 from rfl]
  refine PowerSeries.gaussNorm_mul_eq_mul (v := (norm : R → ℝ)) (c := 1) f.1 g.1
    (Restricted.hasGaussNorm 1 f) (Restricted.hasGaussNorm 1 g)
    (Restricted.hasGaussNorm 1 (f * g)) norm_nonneg norm_zero
    (fun a b => IsUltrametricDist.norm_add_le_max a b) hmul
    norm_neg hzero one_pos ⟨i, j, ?_, ?_, ?_⟩
  · rw [PowerSeries.achievesGaussNorm_iff]
    show ‖PowerSeries.coeff i f.1‖ * (1 : ℝ) ^ i = _
    rw [one_pow, mul_one, hiA, Restricted.norm_eq]
  · rw [PowerSeries.achievesGaussNorm_iff]
    show ‖PowerSeries.coeff j g.1‖ * (1 : ℝ) ^ j = _
    rw [one_pow, mul_one, hjA, Restricted.norm_eq]
  · intro p hp hpne
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    show ‖PowerSeries.coeff p.1 f.1 * PowerSeries.coeff p.2 g.1‖ <
      ‖PowerSeries.coeff i f.1‖ * ‖PowerSeries.coeff j g.1‖
    rw [hmul, hiA, hjA]
    rcases lt_or_gt_of_ne (show p.1 ≠ i from fun h => hpne (by
      refine Prod.ext h ?_
      omega)) with hlt | hgt
    · have hf1 : ‖PowerSeries.coeff p.1 f.1‖ < ‖f‖ := by
        rcases lt_or_eq_of_le (norm_psCoeff_le f p.1) with h | h
        · exact h
        · have := himin p.1 h
          omega
      calc ‖PowerSeries.coeff p.1 f.1‖ * ‖PowerSeries.coeff p.2 g.1‖
          ≤ ‖PowerSeries.coeff p.1 f.1‖ * ‖g‖ :=
            mul_le_mul_of_nonneg_left (norm_psCoeff_le g p.2) (norm_nonneg _)
        _ < ‖f‖ * ‖g‖ := mul_lt_mul_of_pos_right hf1 hposg
    · have hg1 : ‖PowerSeries.coeff p.2 g.1‖ < ‖g‖ := by
        rcases lt_or_eq_of_le (norm_psCoeff_le g p.2) with h | h
        · exact h
        · have := hjmin p.2 h
          omega
      calc ‖PowerSeries.coeff p.1 f.1‖ * ‖PowerSeries.coeff p.2 g.1‖
          ≤ ‖f‖ * ‖PowerSeries.coeff p.2 g.1‖ :=
            mul_le_mul_of_nonneg_right (norm_psCoeff_le f p.1) (norm_nonneg _)
        _ < ‖f‖ * ‖g‖ := mul_lt_mul_of_pos_left hg1 hposf

end GenericMult

/-- The Gauss norm on `𝒞 = L⟨Q⟩` is multiplicative ([FJP] Prop 2.3: "The Laurent Gauss norm
on 𝒞 = L⟨Q⟩ is multiplicative"). -/
theorem norm_JetC_mul (f g : JetC F) : ‖f * g‖ = ‖f‖ * ‖g‖ :=
  norm_restricted_mul (norm_L_mul F) (fun x hx => norm_L_eq_zero F hx) f g

/-- Multiplicativity of the `K⟨W⟩` Gauss norm (base of `𝓑`). -/
theorem norm_KW_mul (f g : PowerSeries.Restricted K (1 : ℝ)) : ‖f * g‖ = ‖f‖ * ‖g‖ :=
  norm_restricted_mul norm_mul (fun x hx => norm_eq_zero.mp hx) f g

instance : Nontrivial (JetC F) := by
  refine ⟨⟨0, 1, fun h => ?_⟩⟩
  have := congrArg (norm : JetC F → ℝ) h
  rw [norm_zero, norm_one] at this
  exact zero_ne_one this

instance : NoZeroDivisors (JetC F) := by
  refine ⟨fun {f g} hfg => ?_⟩
  by_contra hcon
  push Not at hcon
  obtain ⟨hf, hg⟩ := hcon
  have h := norm_JetC_mul F f g
  rw [hfg, norm_zero] at h
  have hposf : 0 < ‖f‖ := norm_pos_iff.mpr hf
  have hposg : 0 < ‖g‖ := norm_pos_iff.mpr hg
  nlinarith

/-- `𝒞` is an integral domain ([FJP] Prop 2.3: "also that 𝒞 is a domain"). -/
instance : IsDomain (JetC F) := NoZeroDivisors.to_isDomain _

instance : Nontrivial (JetA F) := by
  refine ⟨⟨0, 1, fun h => ?_⟩⟩
  have := congrArg (norm : JetA F → ℝ) h
  rw [norm_zero, norm_one] at this
  exact zero_ne_one this

instance : NoZeroDivisors (JetA F) := by
  refine ⟨fun {a b} hab => ?_⟩
  have h : (a : JetC F) * (b : JetC F) = 0 := by
    rw [show (a : JetC F) * (b : JetC F) = ((a * b : JetA F) : JetC F) from rfl, hab]
    rfl
  rcases mul_eq_zero.mp h with h1 | h1
  · exact Or.inl (Subtype.ext h1)
  · exact Or.inr (Subtype.ext h1)

/-- `𝓐` is an integral domain ([FJP] Prop 2.3: "𝒜 is a domain because it is a subring
of 𝒞"). -/
instance : IsDomain (JetA F) := NoZeroDivisors.to_isDomain _

/-! ### The power-bounded subring of 𝓐 is the unit ball ([FJP] Prop 2.3) -/

theorem norm_JetA_mul (a b : JetA F) : ‖a * b‖ = ‖a‖ * ‖b‖ := by
  show ‖((a * b : JetA F) : JetC F)‖ = _
  rw [show ((a * b : JetA F) : JetC F) = (a : JetC F) * (b : JetC F) from rfl,
    norm_JetC_mul]
  rfl

theorem norm_JetA_pow (a : JetA F) (n : ℕ) : ‖a ^ n‖ = ‖a‖ ^ n := by
  induction n with
  | zero => simp
  | succ m ih => rw [pow_succ, pow_succ, norm_JetA_mul, ih]

/-- Power-boundedness in 𝓐 is having norm at most one ([FJP] Prop 2.3: "If `v(a) < 0` …
`a` is not power-bounded. If `v(a) ≥ 0`, all powers of `a` lie in 𝒜₀. Thus the valuation
formulation gives directly `𝒜° = 𝒜₀`"). (`maxHeartbeats`: subtype-instance whnf; cleanup
candidate.) -/
theorem isPowerBounded_JetA_iff (a : JetA F) :
    TopologicalRing.IsPowerBounded a ↔ ‖a‖ ≤ 1 := by
  constructor
  · intro h
    by_contra hlt
    push Not at hlt
    obtain ⟨V, hV, hVsub⟩ := h (Metric.ball 0 1) (Metric.ball_mem_nhds 0 one_pos)
    obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hV
    obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one hδ (norm_tA_lt_one F)
    have hwV : (tA F) ^ m ∈ V := by
      refine hball ?_
      rw [Metric.mem_ball, dist_zero_right, norm_JetA_pow]
      exact hm
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (((‖tA F‖) ^ m)⁻¹) hlt
    have hmem : a ^ n * (tA F) ^ m ∈ Metric.ball (0 : JetA F) 1 :=
      hVsub ⟨a ^ n, ⟨n, rfl⟩, (tA F) ^ m, hwV, rfl⟩
    rw [Metric.mem_ball, dist_zero_right, norm_JetA_mul, norm_JetA_pow, norm_JetA_pow]
      at hmem
    have hge : (1 : ℝ) ≤ ‖a‖ ^ n * ‖tA F‖ ^ m := by
      have hpos : (0 : ℝ) < ‖tA F‖ ^ m := pow_pos (norm_tA_pos F) m
      calc (1 : ℝ) = (‖tA F‖ ^ m)⁻¹ * ‖tA F‖ ^ m := (inv_mul_cancel₀ (ne_of_gt hpos)).symm
        _ ≤ ‖a‖ ^ n * ‖tA F‖ ^ m := by gcongr
    exact absurd hmem (not_lt.mpr hge)
  · intro h
    intro U hU
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hU
    refine ⟨Metric.ball 0 ε, Metric.ball_mem_nhds 0 hε, ?_⟩
    rintro z ⟨s, ⟨k, rfl⟩, y, hy, rfl⟩
    rw [Metric.mem_ball, dist_zero_right] at hy
    refine hball ?_
    rw [Metric.mem_ball, dist_zero_right]
    calc ‖a ^ k * y‖ ≤ ‖a ^ k‖ * ‖y‖ := norm_mul_le _ _
      _ ≤ 1 * ‖y‖ := by
          rw [norm_JetA_pow]
          exact mul_le_mul_of_nonneg_right (pow_le_one₀ (norm_nonneg _) h) (norm_nonneg _)
      _ = ‖y‖ := one_mul _
      _ < ε := hy

/-- The power-bounded subring of 𝓐 is bounded — **𝓐 is uniform**
([FJP] Prop 2.3: "The ring 𝒜 is a complete uniform Tate k-algebra"). -/
theorem isUniform_JetA : TopologicalRing.IsUniform (JetA F) := by
  refine ⟨fun U hU => ?_⟩
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hU
  refine ⟨Metric.ball 0 ε, Metric.ball_mem_nhds 0 hε, ?_⟩
  rintro z ⟨s, hs, y, hy, rfl⟩
  rw [Metric.mem_ball, dist_zero_right] at hy
  refine hball ?_
  rw [Metric.mem_ball, dist_zero_right]
  have hs1 : ‖s‖ ≤ 1 := (isPowerBounded_JetA_iff F s).mp hs
  calc ‖s * y‖ ≤ ‖s‖ * ‖y‖ := norm_mul_le _ _
    _ ≤ 1 * ‖y‖ := mul_le_mul_of_nonneg_right hs1 (norm_nonneg _)
    _ = ‖y‖ := one_mul _
    _ < ε := hy

/-! ### The plus rings of the jet vertices ([FJP] (5.2)) -/

section JetIff

/-- The jet-power norm bound: over a multiplicative base, `‖xⁿ‖ ≤ max 1 ‖x.snd‖` whenever
`‖x.fst‖ ≤ 1` ([FJP] (5.2): "is bounded independently of `n`"). -/
theorem norm_pow_le_of_fst_le {R : Type*} [NormedCommRing R] [IsUltrametricDist R]
    [NormOneClass R] (hmul : ∀ a b : R, ‖a * b‖ = ‖a‖ * ‖b‖)
    (x : DualNumber R) (hx : ‖x.fst‖ ≤ 1) (n : ℕ) :
    ‖x ^ n‖ ≤ max 1 ‖x.snd‖ := by
  have hxeq : x = TrivSqZeroExt.inl x.fst + TrivSqZeroExt.inr x.snd :=
    (TrivSqZeroExt.inl_fst_add_inr_snd_eq x).symm
  conv_lhs => rw [hxeq, JetNorm.pow_eq]
  rw [JetNorm.norm_def]
  have hfst : ((TrivSqZeroExt.inl (x.fst ^ n) +
      TrivSqZeroExt.inr ((n : R) * x.fst ^ (n - 1) * x.snd) : DualNumber R)).fst =
      x.fst ^ n := by
    rw [TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, add_zero]
  have hsnd : ((TrivSqZeroExt.inl (x.fst ^ n) +
      TrivSqZeroExt.inr ((n : R) * x.fst ^ (n - 1) * x.snd) : DualNumber R)).snd =
      (n : R) * x.fst ^ (n - 1) * x.snd := by
    rw [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add]
  rw [hfst, hsnd]
  have hpow : ∀ k : ℕ, ‖x.fst ^ k‖ ≤ 1 := fun k => by
    induction k with
    | zero => rw [pow_zero, norm_one]
    | succ m ih =>
      rw [pow_succ]
      exact (norm_mul_le _ _).trans (mul_le_one₀ ih (norm_nonneg _) hx)
  refine max_le (le_max_of_le_left (hpow n)) (le_max_of_le_right ?_)
  calc ‖(n : R) * x.fst ^ (n - 1) * x.snd‖
      ≤ ‖(n : R) * x.fst ^ (n - 1)‖ * ‖x.snd‖ := norm_mul_le _ _
    _ ≤ ‖(n : R)‖ * ‖x.fst ^ (n - 1)‖ * ‖x.snd‖ :=
        mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
    _ ≤ 1 * 1 * ‖x.snd‖ := by
        refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
        exact mul_le_mul (IsUltrametricDist.norm_natCast_le_one R n) (hpow (n - 1))
          (norm_nonneg _) zero_le_one
    _ = ‖x.snd‖ := by ring

/-- Generic (5.2): power-boundedness in dual numbers over a multiplicative base is a
condition on the constant jet, given a scaling pseudouniformizer. -/
theorem isPowerBounded_dualNumber_iff {R : Type*} [NormedCommRing R] [IsUltrametricDist R]
    [NormOneClass R] (hmul : ∀ a b : R, ‖a * b‖ = ‖a‖ * ‖b‖)
    (t : DualNumber R) (ht1 : ‖t‖ < 1) (ht0 : 0 < ‖t‖)
    (hscale : ∀ z : DualNumber R, ‖t * z‖ = ‖t‖ * ‖z‖)
    (x : DualNumber R) :
    TopologicalRing.IsPowerBounded x ↔ ‖x.fst‖ ≤ 1 := by
  constructor
  · intro h
    by_contra hlt
    push Not at hlt
    obtain ⟨V, hV, hVsub⟩ := h (Metric.ball 0 1) (Metric.ball_mem_nhds 0 one_pos)
    obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hV
    obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one hδ ht1
    have hwV : t ^ m ∈ V := by
      refine hball ?_
      rw [Metric.mem_ball, dist_zero_right]
      have := norm_pow_mul_of_scale (E := DualNumber R) hscale m 1
      rw [mul_one, norm_one, mul_one] at this
      rw [this]
      exact hm
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt ((‖t‖ ^ m)⁻¹) hlt
    have hmem : x ^ n * t ^ m ∈ Metric.ball (0 : DualNumber R) 1 :=
      hVsub ⟨x ^ n, ⟨n, rfl⟩, t ^ m, hwV, rfl⟩
    rw [Metric.mem_ball, dist_zero_right, mul_comm,
      norm_pow_mul_of_scale (E := DualNumber R) hscale m] at hmem
    have hfstpow : ∀ k : ℕ, ‖x.fst ^ k‖ = ‖x.fst‖ ^ k := fun k => by
      induction k with
      | zero => simp
      | succ j ih => rw [pow_succ, pow_succ, hmul, ih]
    have hxn : ‖x.fst‖ ^ n ≤ ‖x ^ n‖ := by
      rw [JetNorm.norm_def]
      refine le_max_of_le_left ?_
      rw [TrivSqZeroExt.fst_pow, hfstpow n]
    have hge : (1 : ℝ) ≤ ‖t‖ ^ m * ‖x ^ n‖ := by
      have hpos : (0 : ℝ) < ‖t‖ ^ m := by positivity
      calc (1 : ℝ) = (‖t‖ ^ m)⁻¹ * ‖t‖ ^ m := (inv_mul_cancel₀ (ne_of_gt hpos)).symm
        _ ≤ ‖x.fst‖ ^ n * ‖t‖ ^ m := by gcongr
        _ = ‖t‖ ^ m * ‖x.fst‖ ^ n := by ring
        _ ≤ ‖t‖ ^ m * ‖x ^ n‖ := mul_le_mul_of_nonneg_left hxn hpos.le
    exact absurd hmem (not_lt.mpr hge)
  · intro h
    intro U hU
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hU
    have hC : (0 : ℝ) < max 1 ‖x.snd‖ + 1 := by positivity
    refine ⟨Metric.ball 0 (ε / (max 1 ‖x.snd‖ + 1)),
      Metric.ball_mem_nhds 0 (by positivity), ?_⟩
    rintro z ⟨s, ⟨k, rfl⟩, y, hy, rfl⟩
    rw [Metric.mem_ball, dist_zero_right] at hy
    refine hball ?_
    rw [Metric.mem_ball, dist_zero_right]
    calc ‖x ^ k * y‖ ≤ ‖x ^ k‖ * ‖y‖ := norm_mul_le _ _
      _ ≤ (max 1 ‖x.snd‖) * ‖y‖ :=
          mul_le_mul_of_nonneg_right (norm_pow_le_of_fst_le hmul x h k) (norm_nonneg _)
      _ < (max 1 ‖x.snd‖ + 1) * (ε / (max 1 ‖x.snd‖ + 1)) := by
          refine mul_lt_mul' (by linarith) hy (norm_nonneg _) hC
      _ = ε := by field_simp

end JetIff

/-- Power-boundedness in `𝓑` depends only on the constant-jet component
([FJP] (5.2): `ℬ° = k°⟨W⟩ ⊕ Qk⟨W⟩`, via `(f+Qg)ⁿ = fⁿ + nf^{n-1}Qg`). -/
theorem isPowerBounded_JetB_iff (x : JetB F) :
    TopologicalRing.IsPowerBounded x ↔ ‖x.fst‖ ≤ 1 :=
  isPowerBounded_dualNumber_iff (norm_KW_mul F) (tB F)
    (by rw [norm_tB]; exact norm_t_lt_one F)
    (by rw [norm_tB]; exact norm_t_pos F) (norm_tB_mul F) x

/-- Power-boundedness in `𝓓` depends only on the constant-jet component
([FJP] (5.2): `𝒟° = L° + QL`). -/
theorem isPowerBounded_JetD_iff (x : JetD F) :
    TopologicalRing.IsPowerBounded x ↔ ‖x.fst‖ ≤ 1 :=
  isPowerBounded_dualNumber_iff (norm_L_mul F) (tD F)
    (by rw [norm_tD]; exact norm_t_lt_one F)
    (by rw [norm_tD]; exact norm_t_pos F) (norm_tD_mul F) x

/-- `𝓑` is **not** uniform: the square-zero line `K·ε` is power-bounded and unbounded
([FJP] (2.1d): "the summand `kQ` is an unbounded line"). -/
theorem not_isUniform_JetB : ¬ TopologicalRing.IsUniform (JetB F) := by
  intro h
  obtain ⟨V, hV, hVsub⟩ := h.isBounded_powerBounded (Metric.ball 0 1)
    (Metric.ball_mem_nhds 0 one_pos)
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hV
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one hδ
    (show ‖tB F‖ < 1 by rw [norm_tB]; exact norm_t_lt_one F)
  have hwV : (tB F) ^ m ∈ V := by
    refine hball ?_
    rw [Metric.mem_ball, dist_zero_right]
    have := norm_pow_mul_of_scale (E := JetB F) (norm_tB_mul F) m 1
    rw [mul_one, norm_one, mul_one] at this
    rw [this]
    exact hm
  -- the square-zero element with huge norm
  set w : K := (LaurentSeriesExample.t F) ^ (m + 1)
  have hw : w ≠ 0 := pow_ne_zero _ (LaurentSeriesExample.t_ne_zero F)
  set z : JetB F := TrivSqZeroExt.inr (constHomPS F w⁻¹)
  have hzpb : TopologicalRing.IsPowerBounded z := by
    rw [isPowerBounded_JetB_iff]
    rw [show z.fst = 0 from rfl, norm_zero]
    exact zero_le_one
  have hmem : z * (tB F) ^ m ∈ Metric.ball (0 : JetB F) 1 :=
    hVsub ⟨z, hzpb, (tB F) ^ m, hwV, rfl⟩
  rw [Metric.mem_ball, dist_zero_right, mul_comm,
    norm_pow_mul_of_scale (E := JetB F) (norm_tB_mul F) m] at hmem
  have hznorm : ‖z‖ = ‖w⁻¹‖ := by
    rw [show z = TrivSqZeroExt.inr (constHomPS F w⁻¹) from rfl, JetNorm.norm_eps_smul]
    exact norm_restrictedC _
  rw [norm_tB, hznorm] at hmem
  have hwnorm : ‖w⁻¹‖ = ‖LaurentSeriesExample.t F‖ ^ (-(m + 1) : ℤ) := by
    rw [norm_inv, show w = (LaurentSeriesExample.t F) ^ (m + 1) from rfl, norm_pow,
      ← zpow_natCast, ← zpow_neg]
    congr 1
  rw [hwnorm] at hmem
  have ht01 : 0 < ‖LaurentSeriesExample.t F‖ := norm_t_pos F
  have hcalc : (1 : ℝ) ≤ ‖LaurentSeriesExample.t F‖ ^ m *
      ‖LaurentSeriesExample.t F‖ ^ (-(m + 1) : ℤ) := by
    rw [← zpow_natCast (‖LaurentSeriesExample.t F‖) m, ← zpow_add₀ (ne_of_gt ht01)]
    have hexp : (m : ℤ) + (-(m + 1) : ℤ) = -1 := by omega
    rw [hexp]
    rw [zpow_neg, zpow_one]
    rw [le_inv_comm₀ one_pos ht01]
    simpa using (norm_t_lt_one F).le
  exact absurd hmem (not_lt.mpr hcalc)

/-! ### 𝓐 is not noetherian ([FJP] Prop 2.4) -/

/-- The scalars `K⟨W⟩` act on `L` through the norm-preserving embedding. -/
noncomputable instance : Algebra (PowerSeries.Restricted K (1 : ℝ)) (L F) :=
  (ofRestricted (R := K)).toAlgebra

/-- The algebra map is the nonnegative-support embedding, definitionally. -/
theorem algebraMap_L_eq :
    algebraMap (PowerSeries.Restricted K (1 : ℝ)) (L F) = ofRestricted (R := K) := rfl

/-- Multiplying by a norm-one monomial shifts coefficients. -/
theorem coeff_mul_single_one (f : L F) (a m : ℤ) :
    (f * single a (1 : K)).coeff m = f.coeff (m - a) := by
  rw [mul_comm, coeff_mul, tsum_eq_single a (fun x hx => by
    rw [coeff_single, if_neg hx, zero_mul])]
  rw [coeff_single, if_pos rfl, one_mul]

/-- Powers of `W⁻¹` are the monomials at negative exponents. -/
theorem winv_pow_val (i : ℕ) :
    (((Wu (R := K))⁻¹ : (L F)ˣ).val) ^ i = single (-(i : ℤ)) (1 : K) := by
  induction i with
  | zero => rw [pow_zero, Nat.cast_zero, neg_zero, single_zero_one]
  | succ j ih =>
    rw [pow_succ, ih, show (((Wu (R := K))⁻¹ : (L F)ˣ)).val = single (-1 : ℤ) (1 : K)
      from rfl, single_mul_single, mul_one]
    congr 1
    push_cast
    ring

/-- The coefficient of `ofRestricted`, by definition: extension by zero. -/
theorem coeff_ofRestricted' (f : PowerSeries.Restricted K (1 : ℝ)) (a : ℤ) :
    (ofRestricted (R := K) f).coeff a =
      if 0 ≤ a then PowerSeries.coeff a.toNat f.1 else 0 := rfl

/-- `W⁻¹ ∈ L` is not integral over `K⟨W⟩` ([FJP] Prop 2.4: multiplying a monic equation
`(W⁻¹)ⁿ + a_{n-1}(W)(W⁻¹)^{n-1} + ⋯ + a₀(W) = 0` by `Wⁿ` and evaluating at `W = 0`
gives `1 = 0`; here realised as reading off the `W^{-n}`-coefficient). -/
theorem winv_not_integral :
    ¬ IsIntegral (PowerSeries.Restricted K (1 : ℝ)) ((Wu (R := K))⁻¹ : (L F)ˣ).val := by
  rintro ⟨p, hmonic, heval⟩
  rw [← Polynomial.aeval_def] at heval
  set n := p.natDegree with hn
  have hsum : Polynomial.aeval (((Wu (R := K))⁻¹ : (L F)ˣ)).val p =
      ∑ i ∈ Finset.range (n + 1),
        ofRestricted (R := K) (p.coeff i) * single (-(i : ℤ)) (1 : K) := by
    rw [Polynomial.aeval_eq_sum_range]
    exact Finset.sum_congr rfl fun i _ => by
      rw [Algebra.smul_def, algebraMap_L_eq, winv_pow_val]
  have hc := congrArg (coeffHom (R := K) (-(n : ℤ))) (hsum.symm.trans heval)
  rw [map_sum, map_zero] at hc
  have hterm : ∀ i ∈ Finset.range (n + 1),
      coeffHom (R := K) (-(n : ℤ))
        (ofRestricted (R := K) (p.coeff i) * single (-(i : ℤ)) (1 : K)) =
      if i = n then 1 else 0 := by
    intro i hi
    rw [Finset.mem_range] at hi
    show (ofRestricted (R := K) (p.coeff i) * single (-(i : ℤ)) (1 : K)).coeff (-(n : ℤ)) = _
    rw [coeff_mul_single_one, coeff_ofRestricted']
    by_cases hin : i = n
    · rw [if_pos (show (0 : ℤ) ≤ -(n : ℤ) - -(i : ℤ) by omega),
        show (-(n : ℤ) - -(i : ℤ)).toNat = 0 by omega, hin,
        show p.coeff n = 1 from hmonic.coeff_natDegree,
        show ((1 : PowerSeries.Restricted K (1 : ℝ))).1 = 1 from rfl,
        PowerSeries.coeff_zero_one, if_pos rfl]
    · rw [if_neg hin, if_neg (show ¬ (0 : ℤ) ≤ -(n : ℤ) - -(i : ℤ) by omega)]
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq' (Finset.range (n + 1)) n fun _ => (1 : K),
    if_pos (Finset.self_mem_range_succ n)] at hc
  exact one_ne_zero hc

/-- `L` is not module-finite over `K⟨W⟩` ([FJP] Prop 2.4: "It would follow that `L` is a
finite `R_W`-module. A module-finite algebra is integral, so `W⁻¹` would satisfy a monic
equation"). -/
theorem not_moduleFinite_L : ¬ Module.Finite (PowerSeries.Restricted K (1 : ℝ)) (L F) := by
  intro h
  exact winv_not_integral F
    ((Algebra.IsIntegral.of_finite (PowerSeries.Restricted K (1 : ℝ)) (L F)).isIntegral _)

/-- Second-order coefficient of a product in `𝒞`. -/
theorem qCoeff_two_mul (f g : JetC F) :
    qCoeff F 2 (f * g) = qCoeff F 0 f * qCoeff F 2 g +
      (qCoeff F 1 f * qCoeff F 1 g + qCoeff F 2 f * qCoeff F 0 g) := by
  show PowerSeries.coeff 2 (f * g : JetC F).1 = _
  rw [show (f * g : JetC F).1 = f.1 * g.1 from rfl, PowerSeries.coeff_mul,
    show Finset.HasAntidiagonal.antidiagonal (2 : ℕ) = {(0, 2), (1, 1), (2, 0)} from rfl,
    Finset.sum_insert (by simp), Finset.sum_insert (by simp), Finset.sum_singleton]
  rfl

theorem qCoeff_sum {ι : Type*} (s : Finset ι) (f : ι → JetC F) (n : ℕ) :
    qCoeff F n (∑ i ∈ s, f i) = ∑ i ∈ s, qCoeff F n (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [qCoeff_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, qCoeff_add, ih]

/-- The kernel of the 2-jet map consists of the elements with vanishing `Q⁰`- and
`Q¹`-coefficients, i.e. `ker(jB) = Q²𝒞` ([FJP] Prop 2.4: "Let `J = Q²𝒞`"). -/
theorem jB_eq_zero_iff (a : JetA F) :
    jB F a = 0 ↔ qCoeff F 0 (a : JetC F) = 0 ∧ qCoeff F 1 (a : JetC F) = 0 := by
  constructor
  · intro h
    constructor
    · have h0 : (nonnegEquiv (R := K)).symm ⟨qCoeff F 0 (a : JetC F), a.2.1⟩ =
          (0 : PowerSeries.Restricted K (1 : ℝ)) := congrArg TrivSqZeroExt.fst h
      have := congrArg (nonnegEquiv (R := K)) h0
      rw [RingEquiv.apply_symm_apply, map_zero] at this
      exact congrArg Subtype.val this
    · have h1 : (nonnegEquiv (R := K)).symm ⟨qCoeff F 1 (a : JetC F), a.2.2⟩ =
          (0 : PowerSeries.Restricted K (1 : ℝ)) := congrArg TrivSqZeroExt.snd h
      have := congrArg (nonnegEquiv (R := K)) h1
      rw [RingEquiv.apply_symm_apply, map_zero] at this
      exact congrArg Subtype.val this
  · rintro ⟨h0, h1⟩
    refine TrivSqZeroExt.ext ?_ ?_
    · show (nonnegEquiv (R := K)).symm ⟨qCoeff F 0 (a : JetC F), a.2.1⟩ =
        (0 : JetB F).fst
      rw [TrivSqZeroExt.fst_zero,
        show (⟨qCoeff F 0 (a : JetC F), a.2.1⟩ : nonnegSubring K) = 0 from Subtype.ext h0,
        map_zero]
    · show (nonnegEquiv (R := K)).symm ⟨qCoeff F 1 (a : JetC F), a.2.2⟩ =
        (0 : JetB F).snd
      rw [TrivSqZeroExt.snd_zero,
        show (⟨qCoeff F 1 (a : JetC F), a.2.2⟩ : nonnegSubring K) = 0 from Subtype.ext h1,
        map_zero]

/-- The `Q²`-monomial with coefficient `ℓ`: the witness that any `ℓ ∈ L` occurs as a
`Q²`-coefficient of an element of `J = ker(jB)`. -/
noncomputable def q2elt (ℓ : L F) : JetC F :=
  ⟨PowerSeries.mk fun n => if n = 2 then ℓ else 0, by
    show PowerSeries.IsRestricted (1 : ℝ) _
    rw [Restricted.isRestricted_iff_cofinite]
    simp only [PowerSeries.coeff_mk, one_pow, mul_one]
    refine tendsto_nhds_of_eventually_eq ?_
    rw [Filter.eventually_cofinite]
    refine (Set.finite_singleton 2).subset fun n hn => ?_
    rw [Set.mem_setOf_eq] at hn
    by_contra hmem
    rw [Set.mem_singleton_iff] at hmem
    exact hn (by rw [if_neg hmem, norm_zero])⟩

theorem qCoeff_q2elt (ℓ : L F) (n : ℕ) :
    qCoeff F n (q2elt F ℓ) = if n = 2 then ℓ else 0 := by
  show PowerSeries.coeff n (PowerSeries.mk fun m => if m = 2 then ℓ else 0) = _
  rw [PowerSeries.coeff_mk]

theorem q2elt_mem_jetSupport (ℓ : L F) : q2elt F ℓ ∈ jetSupport F := by
  constructor
  · rw [show qCoeff F 0 (q2elt F ℓ) = 0 from by
      rw [qCoeff_q2elt, if_neg (by norm_num)]]
    exact zero_mem _
  · rw [show qCoeff F 1 (q2elt F ℓ) = 0 from by
      rw [qCoeff_q2elt, if_neg (by norm_num)]]
    exact zero_mem _

/-- If the ideal `J = ker(jB) = Q²𝒞` of 𝓐 were finitely generated, `L` would be
module-finite over `K⟨W⟩` ([FJP] Prop 2.4: `KJ = Q³𝒞`, `J/KJ ≅ 𝒞/Q𝒞 = L` as
`𝒜/K ≅ R_W`-modules, and generators of `J` generate `J/KJ`). -/
theorem moduleFinite_of_ker_jB_fg (h : (RingHom.ker (jB F)).FG) :
    Module.Finite (PowerSeries.Restricted K (1 : ℝ)) (L F) := by
  classical
  obtain ⟨T, hT⟩ := h
  refine ⟨⟨T.image (fun x : JetA F => qCoeff F 2 (x : JetC F)), ?_⟩⟩
  rw [Submodule.eq_top_iff']
  intro ℓ
  -- the `Q²ℓ` monomial lies in `J = ker(jB) = span T`
  have hyk : (⟨q2elt F ℓ, q2elt_mem_jetSupport F ℓ⟩ : JetA F) ∈ RingHom.ker (jB F) := by
    rw [RingHom.mem_ker, jB_eq_zero_iff]
    exact ⟨by rw [show qCoeff F 0 (((⟨q2elt F ℓ, q2elt_mem_jetSupport F ℓ⟩ : JetA F)) :
        JetC F) = qCoeff F 0 (q2elt F ℓ) from rfl, qCoeff_q2elt, if_neg (by norm_num)],
      by rw [show qCoeff F 1 (((⟨q2elt F ℓ, q2elt_mem_jetSupport F ℓ⟩ : JetA F)) :
        JetC F) = qCoeff F 1 (q2elt F ℓ) from rfl, qCoeff_q2elt, if_neg (by norm_num)]⟩
  rw [← hT] at hyk
  obtain ⟨coeffs, -, hsum⟩ := Submodule.mem_span_finset.mp hyk
  -- vanishing jets of the generators
  have hgen : ∀ x ∈ T, qCoeff F 0 (x : JetC F) = 0 ∧ qCoeff F 1 (x : JetC F) = 0 :=
    fun x hx => (jB_eq_zero_iff F x).mp (RingHom.mem_ker.mp
      (hT ▸ Ideal.subset_span (Finset.mem_coe.mpr hx)))
  -- read off the `Q²`-coefficient of the span decomposition
  have hcoe : ((∑ x ∈ T, coeffs x • x : JetA F) : JetC F) =
      ∑ x ∈ T, ((coeffs x : JetA F) : JetC F) * (x : JetC F) := by
    rw [show ((∑ x ∈ T, coeffs x • x : JetA F) : JetC F) =
        iotaC F (∑ x ∈ T, coeffs x • x) from rfl, map_sum]
    exact Finset.sum_congr rfl fun x hx => by
      rw [smul_eq_mul]
      exact map_mul (iotaC F) _ _
  have h2 : ℓ = ∑ x ∈ T, qCoeff F 0 ((coeffs x : JetC F)) * qCoeff F 2 (x : JetC F) := by
    have := congrArg (fun z : JetA F => qCoeff F 2 (z : JetC F)) hsum
    simp only [hcoe, qCoeff_sum] at this
    rw [show qCoeff F 2 (((⟨q2elt F ℓ, q2elt_mem_jetSupport F ℓ⟩ : JetA F)) : JetC F) =
      qCoeff F 2 (q2elt F ℓ) from rfl, qCoeff_q2elt, if_pos rfl] at this
    rw [← this]
    exact Finset.sum_congr rfl fun x hx => by
      rw [qCoeff_two_mul, (hgen x hx).1, (hgen x hx).2, mul_zero, mul_zero, add_zero,
        add_zero]
  rw [h2]
  refine Submodule.sum_mem _ fun x hx => ?_
  have hb : ofRestricted (R := K)
      ((nonnegEquiv (R := K)).symm ⟨qCoeff F 0 ((coeffs x : JetC F)), (coeffs x).2.1⟩) =
      qCoeff F 0 ((coeffs x : JetC F)) := by
    show ((nonnegEquiv (R := K)) ((nonnegEquiv (R := K)).symm _) : L F) = _
    rw [RingEquiv.apply_symm_apply]
  rw [← hb, ← algebraMap_L_eq, ← Algebra.smul_def]
  exact Submodule.smul_mem _ _ (Submodule.subset_span
    (Finset.mem_coe.mpr (Finset.mem_image_of_mem _ hx)))

/-- The ideal `Q²𝒞 ⊂ 𝓐` is not finitely generated ([FJP] Prop 2.4). -/
theorem ker_jB_not_fg : ¬ (RingHom.ker (jB F)).FG := fun h =>
  not_moduleFinite_L F (moduleFinite_of_ker_jB_fg F h)

/-- **𝓐 is not noetherian** ([FJP] Prop 2.4: "The underlying ring 𝒜 is not noetherian"). -/
theorem not_isNoetherianRing_JetA : ¬ IsNoetherianRing (JetA F) := fun h =>
  ker_jB_not_fg F (h.noetherian _)

end FiniteJet
