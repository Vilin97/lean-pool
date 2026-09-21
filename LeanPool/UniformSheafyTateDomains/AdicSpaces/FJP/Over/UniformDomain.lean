/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanPool.UniformSheafyTateDomains.AdicSpaces.FJP.FiniteJetUniformDomain
import LeanPool.UniformSheafyTateDomains.AdicSpaces.FJP.Over.JetRings

/-!
# 𝓐 over a general base is a uniform domain and is not noetherian
([FJP] Propositions 2.3, 2.4, and (5.2))

The K8 "uniform + domain + non-noetherian" slice of the CDVF campaign (crosswalk D9): the
content of `FiniteJetUniformDomain.lean` rebuilt over an arbitrary base
`[NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]`, replacing the Laurent
witness field `LaurentSeries F`. Where a statement needs a pseudouniformizer witness it takes
an explicit `ϖ : Uniformizer K` (the K1 layer-1 API of `CDVFBase.lean`) and uses the images
`piA ϖ` / `piB ϖ` of `Over/JetRings.lean`, exactly as the Huber/Tate endpoints there.

* **Prop 2.3**: the Gauss norm on `𝒞 = L⟨Q⟩` is multiplicative (`norm_mul_eq` needs no
  discreteness of the value group); `𝓐° = 𝓐₀` is the unit ball; hence `𝓐` is a complete
  uniform Tate ring (`isUniform_JetA`) and an integral domain.
* **(5.2)**: power-boundedness in the dual-number vertices `𝓑` and `𝓓` depends only on the
  constant-jet component; the square-zero line is power-bounded and unbounded, so `𝓑` is
  **not** uniform (`not_isUniform_JetB` — the witness needs only `0 < ‖ϖ‖ < 1`).
* **Prop 2.4**: `𝓐` is not noetherian: the ideal `J = Q²𝒞 = ker(jB)` is not finitely
  generated, since `J/KJ ≅ L` over `𝓐/K ≅ K⟨W⟩` and `W⁻¹` is not integral over `K⟨W⟩`
  (`not_isNoetherianRing_JetA`).

The generic helper layer of the Laurent file (`norm_restricted_mul`,
`norm_pow_le_of_fst_le`, `isPowerBounded_dualNumber_iff`, `norm_pow_mul_of_scale`) is
already base-field-free and is reused, not re-proved.
-/

open Filter Topology

namespace FiniteJetOver

open FiniteJet
open FiniteJet.RestrictedLaurent
open TopologicalRing

universe u

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-! ### Norm multiplicativity and the domain property ([FJP] Prop 2.3) -/

/-- The Gauss norm on `L = K⟨W,W⁻¹⟩` is multiplicative
(`RestrictedLaurent.norm_mul_eq`, which is generic in the complete nonarchimedean base). -/
theorem norm_L_mul (f g : L K) : ‖f * g‖ = ‖f‖ * ‖g‖ :=
  RestrictedLaurent.norm_mul_eq f g

theorem norm_L_eq_zero {f : L K} (hf : ‖f‖ = 0) : f = 0 :=
  norm_eq_zero.mp hf

/-- The Gauss norm on `𝒞 = L⟨Q⟩` is multiplicative ([FJP] Prop 2.3: "The Laurent Gauss norm
on 𝒞 = L⟨Q⟩ is multiplicative"; generic base). -/
theorem norm_JetC_mul (f g : JetC K) : ‖f * g‖ = ‖f‖ * ‖g‖ :=
  norm_restricted_mul (norm_L_mul K) (fun _ hx => norm_L_eq_zero K hx) f g

omit [CompleteSpace K] in
/-- Multiplicativity of the `K⟨W⟩` Gauss norm (base of `𝓑`). -/
theorem norm_KW_mul (f g : PowerSeries.Restricted K (1 : ℝ)) : ‖f * g‖ = ‖f‖ * ‖g‖ :=
  norm_restricted_mul norm_mul (fun _ hx => norm_eq_zero.mp hx) f g

instance instNontrivialJetC : Nontrivial (JetC K) := by
  refine ⟨⟨0, 1, fun h => ?_⟩⟩
  have := congrArg (norm : JetC K → ℝ) h
  rw [norm_zero, norm_one] at this
  exact zero_ne_one this

instance instNoZeroDivisorsJetC : NoZeroDivisors (JetC K) := by
  refine ⟨fun {f g} hfg => ?_⟩
  by_contra hcon
  push Not at hcon
  obtain ⟨hf, hg⟩ := hcon
  have h := norm_JetC_mul K f g
  rw [hfg, norm_zero] at h
  have hposf : 0 < ‖f‖ := norm_pos_iff.mpr hf
  have hposg : 0 < ‖g‖ := norm_pos_iff.mpr hg
  nlinarith

/-- `𝒞` is an integral domain ([FJP] Prop 2.3: "also that 𝒞 is a domain"; generic base). -/
instance instIsDomainJetC : IsDomain (JetC K) := NoZeroDivisors.to_isDomain _

instance instNontrivialJetA : Nontrivial (JetA K) := by
  refine ⟨⟨0, 1, fun h => ?_⟩⟩
  have := congrArg (norm : JetA K → ℝ) h
  rw [norm_zero, norm_one] at this
  exact zero_ne_one this

instance instNoZeroDivisorsJetA : NoZeroDivisors (JetA K) := by
  refine ⟨fun {a b} hab => ?_⟩
  have h : (a : JetC K) * (b : JetC K) = 0 := by
    rw [show (a : JetC K) * (b : JetC K) = ((a * b : JetA K) : JetC K) from rfl, hab]
    rfl
  rcases mul_eq_zero.mp h with h1 | h1
  · exact Or.inl (Subtype.ext h1)
  · exact Or.inr (Subtype.ext h1)

/-- `𝓐` is an integral domain ([FJP] Prop 2.3: "𝒜 is a domain because it is a subring
of 𝒞"; generic base). -/
instance instIsDomainJetA : IsDomain (JetA K) := NoZeroDivisors.to_isDomain _

/-! ### The power-bounded subring of 𝓐 is the unit ball ([FJP] Prop 2.3) -/

theorem norm_JetA_mul (a b : JetA K) : ‖a * b‖ = ‖a‖ * ‖b‖ := by
  show ‖((a * b : JetA K) : JetC K)‖ = _
  rw [show ((a * b : JetA K) : JetC K) = (a : JetC K) * (b : JetC K) from rfl,
    norm_JetC_mul]
  rfl

theorem norm_JetA_pow (a : JetA K) (n : ℕ) : ‖a ^ n‖ = ‖a‖ ^ n := by
  induction n with
  | zero => simp
  | succ m ih => rw [pow_succ, pow_succ, norm_JetA_mul, ih]

section Uniformizer

variable {K}

/-- Power-boundedness in 𝓐 is having norm at most one ([FJP] Prop 2.3: "If `v(a) < 0` …
`a` is not power-bounded. If `v(a) ≥ 0`, all powers of `a` lie in 𝒜₀. Thus the valuation
formulation gives directly `𝒜° = 𝒜₀`"); the unbounding witness is a power of `piA ϖ`.
(`maxHeartbeats`: subtype-instance whnf, as in the Laurent template.) -/
theorem isPowerBounded_JetA_iff (ϖ : Uniformizer K) (a : JetA K) :
    TopologicalRing.IsPowerBounded a ↔ ‖a‖ ≤ 1 := by
  constructor
  · intro h
    by_contra hlt
    push Not at hlt
    obtain ⟨V, hV, hVsub⟩ := h (Metric.ball 0 1) (Metric.ball_mem_nhds 0 one_pos)
    obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hV
    obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one hδ (norm_piA_lt_one ϖ)
    have hwV : (piA ϖ) ^ m ∈ V := by
      refine hball ?_
      rw [Metric.mem_ball, dist_zero_right, norm_JetA_pow]
      exact hm
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (((‖piA ϖ‖) ^ m)⁻¹) hlt
    have hmem : a ^ n * (piA ϖ) ^ m ∈ Metric.ball (0 : JetA K) 1 :=
      hVsub ⟨a ^ n, ⟨n, rfl⟩, (piA ϖ) ^ m, hwV, rfl⟩
    rw [Metric.mem_ball, dist_zero_right, norm_JetA_mul, norm_JetA_pow, norm_JetA_pow]
      at hmem
    have hge : (1 : ℝ) ≤ ‖a‖ ^ n * ‖piA ϖ‖ ^ m := by
      have hpos : (0 : ℝ) < ‖piA ϖ‖ ^ m := pow_pos (norm_piA_pos ϖ) m
      calc (1 : ℝ) = (‖piA ϖ‖ ^ m)⁻¹ * ‖piA ϖ‖ ^ m := (inv_mul_cancel₀ (ne_of_gt hpos)).symm
        _ ≤ ‖a‖ ^ n * ‖piA ϖ‖ ^ m := by gcongr
    exact absurd hmem (not_lt.mpr hge)
  · intro h U hU
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

/-- The power-bounded subring of 𝓐 is its unit ball 𝓐₀ ([FJP] Theorem 1.1's `A° = A₀`).
The generic-base counterpart of `WeightedParity.powerBoundedSubring_eq_unitBall`. -/
theorem powerBoundedSubring_eq_unitBall (ϖ : Uniformizer K) :
    powerBoundedSubring (JetA K) = (FiniteJet.unitBall (JetA K) : Set (JetA K)) := by
  ext a
  rw [show a ∈ powerBoundedSubring (JetA K) ↔ IsPowerBounded a from Iff.rfl,
    isPowerBounded_JetA_iff ϖ a]
  exact (FiniteJet.mem_unitBall_iff _ a).symm

/-- The power-bounded subring of 𝓐 is bounded — **𝓐 is uniform**
([FJP] Prop 2.3: "The ring 𝒜 is a complete uniform Tate k-algebra"; any base-field
uniformizer witnesses it). -/
theorem isUniform_JetA (ϖ : Uniformizer K) : TopologicalRing.IsUniform (JetA K) := by
  refine ⟨fun U hU => ?_⟩
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hU
  refine ⟨Metric.ball 0 ε, Metric.ball_mem_nhds 0 hε, ?_⟩
  rintro z ⟨s, hs, y, hy, rfl⟩
  rw [Metric.mem_ball, dist_zero_right] at hy
  refine hball ?_
  rw [Metric.mem_ball, dist_zero_right]
  have hs1 : ‖s‖ ≤ 1 := (isPowerBounded_JetA_iff ϖ s).mp hs
  calc ‖s * y‖ ≤ ‖s‖ * ‖y‖ := norm_mul_le _ _
    _ ≤ 1 * ‖y‖ := mul_le_mul_of_nonneg_right hs1 (norm_nonneg _)
    _ = ‖y‖ := one_mul _
    _ < ε := hy

/-! ### The plus rings of the jet vertices ([FJP] (5.2))

The dual-number power-bound lemmas `FiniteJet.norm_pow_le_of_fst_le` and
`FiniteJet.isPowerBounded_dualNumber_iff` are already generic; they are instantiated at the
pseudouniformizers `piB ϖ` and `piD ϖ`. -/

/-- Power-boundedness in `𝓑` depends only on the constant-jet component
([FJP] (5.2): `ℬ° = k°⟨W⟩ ⊕ Qk⟨W⟩`, via `(f+Qg)ⁿ = fⁿ + nf^{n-1}Qg`). -/
theorem isPowerBounded_JetB_iff (ϖ : Uniformizer K) (x : JetB K) :
    TopologicalRing.IsPowerBounded x ↔ ‖x.fst‖ ≤ 1 :=
  isPowerBounded_dualNumber_iff (norm_KW_mul K) (piB ϖ)
    (by rw [norm_piB]; exact ϖ.norm_val_lt_one)
    (by rw [norm_piB]; exact ϖ.norm_val_pos) (norm_piB_mul ϖ) x

/-- Power-boundedness in `𝓓` depends only on the constant-jet component
([FJP] (5.2): `𝒟° = L° + QL`). -/
theorem isPowerBounded_JetD_iff (ϖ : Uniformizer K) (x : JetD K) :
    TopologicalRing.IsPowerBounded x ↔ ‖x.fst‖ ≤ 1 :=
  isPowerBounded_dualNumber_iff (norm_L_mul K) (piD ϖ)
    (by rw [norm_piD]; exact ϖ.norm_val_lt_one)
    (by rw [norm_piD]; exact ϖ.norm_val_pos) (norm_piD_mul ϖ) x

/-- `𝓑` is **not** uniform: the square-zero line `K·ε` is power-bounded and unbounded
([FJP] (2.1d): "the summand `kQ` is an unbounded line"; the witness needs only
`0 < ‖ϖ.val‖ < 1`). -/
theorem not_isUniform_JetB (ϖ : Uniformizer K) : ¬ TopologicalRing.IsUniform (JetB K) := by
  intro h
  obtain ⟨V, hV, hVsub⟩ := h.isBounded_powerBounded (Metric.ball 0 1)
    (Metric.ball_mem_nhds 0 one_pos)
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hV
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one hδ
    (show ‖piB ϖ‖ < 1 by rw [norm_piB]; exact ϖ.norm_val_lt_one)
  have hwV : (piB ϖ) ^ m ∈ V := by
    refine hball ?_
    rw [Metric.mem_ball, dist_zero_right]
    have := norm_pow_mul_of_scale (E := JetB K) (norm_piB_mul ϖ) m 1
    rw [mul_one, norm_one, mul_one] at this
    rw [this]
    exact hm
  -- the square-zero element with huge norm
  set w : K := ϖ.val ^ (m + 1)
  set z : JetB K := TrivSqZeroExt.inr (constHomPS K w⁻¹)
  have hzpb : TopologicalRing.IsPowerBounded z := by
    rw [isPowerBounded_JetB_iff ϖ]
    rw [show z.fst = 0 from rfl, norm_zero]
    exact zero_le_one
  have hmem : z * (piB ϖ) ^ m ∈ Metric.ball (0 : JetB K) 1 :=
    hVsub ⟨z, hzpb, (piB ϖ) ^ m, hwV, rfl⟩
  rw [Metric.mem_ball, dist_zero_right, mul_comm,
    norm_pow_mul_of_scale (E := JetB K) (norm_piB_mul ϖ) m] at hmem
  have hznorm : ‖z‖ = ‖w⁻¹‖ := by
    rw [show z = TrivSqZeroExt.inr (constHomPS K w⁻¹) from rfl, JetNorm.norm_eps_smul]
    exact norm_restrictedC _
  rw [norm_piB, hznorm] at hmem
  have hwnorm : ‖w⁻¹‖ = ‖ϖ.val‖ ^ (-(m + 1) : ℤ) := by
    rw [norm_inv, show w = ϖ.val ^ (m + 1) from rfl, norm_pow,
      ← zpow_natCast, ← zpow_neg]
    congr 1
  rw [hwnorm] at hmem
  have ht01 : 0 < ‖ϖ.val‖ := ϖ.norm_val_pos
  have hcalc : (1 : ℝ) ≤ ‖ϖ.val‖ ^ m * ‖ϖ.val‖ ^ (-(m + 1) : ℤ) := by
    rw [← zpow_natCast (‖ϖ.val‖) m, ← zpow_add₀ (ne_of_gt ht01)]
    have hexp : (m : ℤ) + (-(m + 1) : ℤ) = -1 := by omega
    rw [hexp]
    rw [zpow_neg, zpow_one]
    rw [le_inv_comm₀ one_pos ht01]
    simpa using ϖ.norm_val_lt_one.le
  exact absurd hmem (not_lt.mpr hcalc)

end Uniformizer

/-! ### 𝓐 is not noetherian ([FJP] Prop 2.4) -/

/-- The scalars `K⟨W⟩` act on `L` through the norm-preserving embedding. -/
noncomputable instance instAlgebraRestrictedL :
    Algebra (PowerSeries.Restricted K (1 : ℝ)) (L K) :=
  (ofRestricted (R := K)).toAlgebra

/-- The algebra map is the nonnegative-support embedding, definitionally. -/
theorem algebraMap_L_eq :
    algebraMap (PowerSeries.Restricted K (1 : ℝ)) (L K) = ofRestricted (R := K) := rfl

/-- Multiplying by a norm-one monomial shifts coefficients. -/
theorem coeff_mul_single_one (f : L K) (a m : ℤ) :
    (f * single a (1 : K)).coeff m = f.coeff (m - a) := by
  rw [mul_comm, coeff_mul, tsum_eq_single a (fun x hx => by
    rw [coeff_single, if_neg hx, zero_mul])]
  rw [coeff_single, if_pos rfl, one_mul]

/-- Powers of `W⁻¹` are the monomials at negative exponents. -/
theorem winv_pow_val (i : ℕ) :
    (((Wu (R := K))⁻¹ : (L K)ˣ).val) ^ i = single (-(i : ℤ)) (1 : K) := by
  induction i with
  | zero => rw [pow_zero, Nat.cast_zero, neg_zero, single_zero_one]
  | succ j ih =>
    rw [pow_succ, ih, show (((Wu (R := K))⁻¹ : (L K)ˣ)).val = single (-1 : ℤ) (1 : K)
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
    ¬ IsIntegral (PowerSeries.Restricted K (1 : ℝ)) ((Wu (R := K))⁻¹ : (L K)ˣ).val := by
  rintro ⟨p, hmonic, heval⟩
  rw [← Polynomial.aeval_def] at heval
  set n := p.natDegree with hn
  have hsum : Polynomial.aeval (((Wu (R := K))⁻¹ : (L K)ˣ)).val p =
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
theorem not_moduleFinite_L : ¬ Module.Finite (PowerSeries.Restricted K (1 : ℝ)) (L K) := by
  intro h
  exact winv_not_integral K
    ((Algebra.IsIntegral.of_finite (PowerSeries.Restricted K (1 : ℝ)) (L K)).isIntegral _)

/-- Second-order coefficient of a product in `𝒞`. -/
theorem qCoeff_two_mul (f g : JetC K) :
    qCoeff K 2 (f * g) = qCoeff K 0 f * qCoeff K 2 g +
      (qCoeff K 1 f * qCoeff K 1 g + qCoeff K 2 f * qCoeff K 0 g) := by
  show PowerSeries.coeff 2 (f * g : JetC K).1 = _
  rw [show (f * g : JetC K).1 = f.1 * g.1 from rfl, PowerSeries.coeff_mul,
    show Finset.HasAntidiagonal.antidiagonal (2 : ℕ) = {(0, 2), (1, 1), (2, 0)} from rfl,
    Finset.sum_insert (by simp), Finset.sum_insert (by simp), Finset.sum_singleton]
  rfl

theorem qCoeff_sum {ι : Type*} (s : Finset ι) (f : ι → JetC K) (n : ℕ) :
    qCoeff K n (∑ i ∈ s, f i) = ∑ i ∈ s, qCoeff K n (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [qCoeff_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, qCoeff_add, ih]

/-- The kernel of the 2-jet map consists of the elements with vanishing `Q⁰`- and
`Q¹`-coefficients, i.e. `ker(jB) = Q²𝒞` ([FJP] Prop 2.4: "Let `J = Q²𝒞`"). -/
theorem jB_eq_zero_iff (a : JetA K) :
    jB K a = 0 ↔ qCoeff K 0 (a : JetC K) = 0 ∧ qCoeff K 1 (a : JetC K) = 0 := by
  constructor
  · intro h
    constructor
    · have h0 : (nonnegEquiv (R := K)).symm ⟨qCoeff K 0 (a : JetC K), a.2.1⟩ =
          (0 : PowerSeries.Restricted K (1 : ℝ)) := congrArg TrivSqZeroExt.fst h
      have := congrArg (nonnegEquiv (R := K)) h0
      rw [RingEquiv.apply_symm_apply, map_zero] at this
      exact congrArg Subtype.val this
    · have h1 : (nonnegEquiv (R := K)).symm ⟨qCoeff K 1 (a : JetC K), a.2.2⟩ =
          (0 : PowerSeries.Restricted K (1 : ℝ)) := congrArg TrivSqZeroExt.snd h
      have := congrArg (nonnegEquiv (R := K)) h1
      rw [RingEquiv.apply_symm_apply, map_zero] at this
      exact congrArg Subtype.val this
  · rintro ⟨h0, h1⟩
    refine TrivSqZeroExt.ext ?_ ?_
    · show (nonnegEquiv (R := K)).symm ⟨qCoeff K 0 (a : JetC K), a.2.1⟩ =
        (0 : JetB K).fst
      rw [TrivSqZeroExt.fst_zero,
        show (⟨qCoeff K 0 (a : JetC K), a.2.1⟩ : nonnegSubring K) = 0 from Subtype.ext h0,
        map_zero]
    · show (nonnegEquiv (R := K)).symm ⟨qCoeff K 1 (a : JetC K), a.2.2⟩ =
        (0 : JetB K).snd
      rw [TrivSqZeroExt.snd_zero,
        show (⟨qCoeff K 1 (a : JetC K), a.2.2⟩ : nonnegSubring K) = 0 from Subtype.ext h1,
        map_zero]

/-- The `Q²`-monomial with coefficient `ℓ`: the witness that any `ℓ ∈ L` occurs as a
`Q²`-coefficient of an element of `J = ker(jB)`. -/
noncomputable def q2elt (ℓ : L K) : JetC K :=
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

theorem qCoeff_q2elt (ℓ : L K) (n : ℕ) :
    qCoeff K n (q2elt K ℓ) = if n = 2 then ℓ else 0 := by
  show PowerSeries.coeff n (PowerSeries.mk fun m => if m = 2 then ℓ else 0) = _
  rw [PowerSeries.coeff_mk]

theorem q2elt_mem_jetSupport (ℓ : L K) : q2elt K ℓ ∈ jetSupport K := by
  constructor
  · rw [show qCoeff K 0 (q2elt K ℓ) = 0 from by
      rw [qCoeff_q2elt, if_neg (by norm_num)]]
    exact zero_mem _
  · rw [show qCoeff K 1 (q2elt K ℓ) = 0 from by
      rw [qCoeff_q2elt, if_neg (by norm_num)]]
    exact zero_mem _

/-- If the ideal `J = ker(jB) = Q²𝒞` of 𝓐 were finitely generated, `L` would be
module-finite over `K⟨W⟩` ([FJP] Prop 2.4: `KJ = Q³𝒞`, `J/KJ ≅ 𝒞/Q𝒞 = L` as
`𝒜/K ≅ R_W`-modules, and generators of `J` generate `J/KJ`). -/
theorem moduleFinite_of_ker_jB_fg (h : (RingHom.ker (jB K)).FG) :
    Module.Finite (PowerSeries.Restricted K (1 : ℝ)) (L K) := by
  classical
  obtain ⟨T, hT⟩ := h
  refine ⟨⟨T.image (fun x : JetA K => qCoeff K 2 (x : JetC K)), ?_⟩⟩
  rw [Submodule.eq_top_iff']
  intro ℓ
  -- the `Q²ℓ` monomial lies in `J = ker(jB) = span T`
  have hyk : (⟨q2elt K ℓ, q2elt_mem_jetSupport K ℓ⟩ : JetA K) ∈ RingHom.ker (jB K) := by
    rw [RingHom.mem_ker, jB_eq_zero_iff]
    exact ⟨by rw [show qCoeff K 0 (((⟨q2elt K ℓ, q2elt_mem_jetSupport K ℓ⟩ : JetA K)) :
        JetC K) = qCoeff K 0 (q2elt K ℓ) from rfl, qCoeff_q2elt, if_neg (by norm_num)],
      by rw [show qCoeff K 1 (((⟨q2elt K ℓ, q2elt_mem_jetSupport K ℓ⟩ : JetA K)) :
        JetC K) = qCoeff K 1 (q2elt K ℓ) from rfl, qCoeff_q2elt, if_neg (by norm_num)]⟩
  rw [← hT] at hyk
  obtain ⟨coeffs, -, hsum⟩ := Submodule.mem_span_finset.mp hyk
  -- vanishing jets of the generators
  have hgen : ∀ x ∈ T, qCoeff K 0 (x : JetC K) = 0 ∧ qCoeff K 1 (x : JetC K) = 0 :=
    fun x hx => (jB_eq_zero_iff K x).mp (RingHom.mem_ker.mp
      (hT ▸ Ideal.subset_span (Finset.mem_coe.mpr hx)))
  -- read off the `Q²`-coefficient of the span decomposition
  have hcoe : ((∑ x ∈ T, coeffs x • x : JetA K) : JetC K) =
      ∑ x ∈ T, ((coeffs x : JetA K) : JetC K) * (x : JetC K) := by
    rw [show ((∑ x ∈ T, coeffs x • x : JetA K) : JetC K) =
        iotaC K (∑ x ∈ T, coeffs x • x) from rfl, map_sum]
    exact Finset.sum_congr rfl fun x hx => by
      rw [smul_eq_mul]
      exact map_mul (iotaC K) _ _
  have h2 : ℓ = ∑ x ∈ T, qCoeff K 0 ((coeffs x : JetC K)) * qCoeff K 2 (x : JetC K) := by
    have := congrArg (fun z : JetA K => qCoeff K 2 (z : JetC K)) hsum
    simp only [hcoe, qCoeff_sum] at this
    rw [show qCoeff K 2 (((⟨q2elt K ℓ, q2elt_mem_jetSupport K ℓ⟩ : JetA K)) : JetC K) =
      qCoeff K 2 (q2elt K ℓ) from rfl, qCoeff_q2elt, if_pos rfl] at this
    rw [← this]
    exact Finset.sum_congr rfl fun x hx => by
      rw [qCoeff_two_mul, (hgen x hx).1, (hgen x hx).2, mul_zero, mul_zero, add_zero,
        add_zero]
  rw [h2]
  refine Submodule.sum_mem _ fun x hx => ?_
  have hb : ofRestricted (R := K)
      ((nonnegEquiv (R := K)).symm ⟨qCoeff K 0 ((coeffs x : JetC K)), (coeffs x).2.1⟩) =
      qCoeff K 0 ((coeffs x : JetC K)) := by
    show ((nonnegEquiv (R := K)) ((nonnegEquiv (R := K)).symm _) : L K) = _
    rw [RingEquiv.apply_symm_apply]
  rw [← hb, ← algebraMap_L_eq, ← Algebra.smul_def]
  exact Submodule.smul_mem _ _ (Submodule.subset_span
    (Finset.mem_coe.mpr (Finset.mem_image_of_mem _ hx)))

/-- The ideal `Q²𝒞 ⊂ 𝓐` is not finitely generated ([FJP] Prop 2.4). -/
theorem ker_jB_not_fg : ¬ (RingHom.ker (jB K)).FG := fun h =>
  not_moduleFinite_L K (moduleFinite_of_ker_jB_fg K h)

/-- **𝓐 is not noetherian** ([FJP] Prop 2.4: "The underlying ring 𝒜 is not noetherian";
generic base). -/
theorem not_isNoetherianRing_JetA : ¬ IsNoetherianRing (JetA K) := fun h =>
  ker_jB_not_fg K (h.noetherian _)

end FiniteJetOver
