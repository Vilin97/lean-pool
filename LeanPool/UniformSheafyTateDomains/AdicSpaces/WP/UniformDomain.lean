/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanPool.UniformSheafyTateDomains.AdicSpaces.WP.Algebra
import LeanPool.UniformSheafyTateDomains.AdicSpaces.Uniform

/-!
# `𝒜` is a uniform integral domain with `𝒜° = 𝒜₀` ([WP] prop:parity-uniform-domain)

The route is the `JetA` one (`FJP/Over/UniformDomain.lean`): the Gauss norm of the
ambient countable restricted Tate algebra is **multiplicative** (norms are attained;
reduce mod the top coefficient — packaged in the vendored `MvRestricted.isAbsoluteValue`
via `WP/RestrictedComplete.lean`), the support subring inherits multiplicativity
isometrically, and multiplicativity gives both the domain property and
`power-bounded = unit ball`, i.e. `𝒜° = 𝒜₀` and uniformity.

Source: [WP] prop:parity-uniform-domain (lines 789–811): "The Gauss norm on the
countable restricted Tate algebra `k⟨W,U_1,U_2,…⟩` is multiplicative. … The support
algebra `𝒜` embeds isometrically into this Tate algebra, so its Gauss norm is also
multiplicative and it is a domain.  If `x ∈ 𝒜₀`, all powers of `x` remain in `𝒜₀`.
If `x ∉ 𝒜₀`, multiplicativity gives `‖x^m‖ = ‖x‖^m`, which is unbounded.  Hence
`𝒜° = 𝒜₀`."
-/

@[expose] public section

namespace WeightedParity

open FiniteJetOver TopologicalRing

variable (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable (w : ℕ → ℕ)

/-- Gauss-norm multiplicativity on the ambient `K⟨W,U_1,U_2,…⟩`
([WP] prop:parity-uniform-domain, first paragraph). -/
theorem norm_amb_mul (f g : Amb K) : ‖f * g‖ = ‖f‖ * ‖g‖ :=
  norm_restricted_mul_general (fun a b => norm_mul a b) f g

/-- Gauss-norm multiplicativity on `𝒜` (isometric restriction of the ambient). -/
theorem norm_wpa_mul (a b : WPA K w) : ‖a * b‖ = ‖a‖ * ‖b‖ := by
  show ‖((a * b : WPA K w) : Amb K)‖ = _
  rw [show ((a * b : WPA K w) : Amb K) = (a : Amb K) * (b : Amb K) from rfl,
    norm_amb_mul]
  rfl

theorem norm_wpa_pow (a : WPA K w) (n : ℕ) : ‖a ^ n‖ = ‖a‖ ^ n := by
  induction n with
  | zero => simp
  | succ m ih => rw [pow_succ, pow_succ, norm_wpa_mul, ih]

instance : Nontrivial (WPA K w) := by
  refine ⟨⟨0, 1, fun h => ?_⟩⟩
  have h2 := congrArg (norm : WPA K w → ℝ) h
  rw [norm_zero, norm_one] at h2
  exact zero_ne_one h2

/-- `𝒜` has no zero divisors (norm multiplicativity; the `instNoZeroDivisorsJetA`
pattern, `FJP/Over/UniformDomain.lean:92`). -/
instance : NoZeroDivisors (WPA K w) := by
  refine ⟨fun {a b} hab => ?_⟩
  have h : (a : Amb K) * (b : Amb K) = 0 := by
    rw [show (a : Amb K) * (b : Amb K) = ((a * b : WPA K w) : Amb K) from rfl, hab]
    rfl
  by_contra hne
  push_neg at hne
  obtain ⟨ha, hb⟩ := hne
  have ha' : (a : Amb K) ≠ 0 := fun h0 => ha (Subtype.ext h0)
  have hb' : (b : Amb K) ≠ 0 := fun h0 => hb (Subtype.ext h0)
  have hna : (0 : ℝ) < ‖(a : Amb K)‖ := norm_pos_iff.mpr ha'
  have hnb : (0 : ℝ) < ‖(b : Amb K)‖ := norm_pos_iff.mpr hb'
  have := norm_amb_mul K (a : Amb K) (b : Amb K)
  rw [h, norm_zero] at this
  nlinarith

/-- `𝒜` is an integral domain ([WP] prop:parity-uniform-domain). -/
instance : IsDomain (WPA K w) :=
  NoZeroDivisors.to_isDomain _

variable {K w} in
/-- Power-boundedness in `𝒜` is exactly the unit ball ([WP]
prop:parity-uniform-domain: "`𝒜° = 𝒜₀`"; the `isPowerBounded_JetA_iff` pattern,
`FJP/Over/UniformDomain.lean:127`). -/
theorem isPowerBounded_wpa_iff (ϖ : Uniformizer K) (a : WPA K w) :
    IsPowerBounded a ↔ ‖a‖ ≤ 1 := by
  constructor
  · intro h
    by_contra hlt
    push_neg at hlt
    obtain ⟨V, hV, hVsub⟩ := h (Metric.ball 0 1) (Metric.ball_mem_nhds 0 one_pos)
    obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hV
    obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one hδ (norm_piW_lt_one (w := w) ϖ)
    have hwV : (piW (w := w) ϖ) ^ m ∈ V := by
      refine hball ?_
      rw [Metric.mem_ball, dist_zero_right, norm_wpa_pow]
      exact hm
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (((‖piW (w := w) ϖ‖) ^ m)⁻¹) hlt
    have hmem : a ^ n * (piW (w := w) ϖ) ^ m ∈ Metric.ball (0 : WPA K w) 1 :=
      hVsub ⟨a ^ n, ⟨n, rfl⟩, (piW ϖ) ^ m, hwV, rfl⟩
    rw [Metric.mem_ball, dist_zero_right, norm_wpa_mul, norm_wpa_pow, norm_wpa_pow]
      at hmem
    have hge : (1 : ℝ) ≤ ‖a‖ ^ n * ‖piW (w := w) ϖ‖ ^ m := by
      have hpos : (0 : ℝ) < ‖piW (w := w) ϖ‖ ^ m := pow_pos (norm_piW_pos ϖ) m
      calc (1 : ℝ) = (‖piW (w := w) ϖ‖ ^ m)⁻¹ * ‖piW (w := w) ϖ‖ ^ m :=
            (inv_mul_cancel₀ (ne_of_gt hpos)).symm
        _ ≤ ‖a‖ ^ n * ‖piW (w := w) ϖ‖ ^ m := by gcongr
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
          rw [norm_wpa_pow]
          exact mul_le_mul_of_nonneg_right (pow_le_one₀ (norm_nonneg _) h)
            (norm_nonneg _)
      _ = ‖y‖ := one_mul _
      _ < ε := hy

variable {K w} in
/-- The power-bounded subring of `𝒜` is its unit ball `𝒜₀`
([WP] `𝒜° = 𝒜₀`, prop:parity-uniform-domain). -/
theorem powerBoundedSubring_eq_unitBall (ϖ : Uniformizer K) :
    powerBoundedSubring (WPA K w) = (FiniteJet.unitBall (WPA K w) : Set (WPA K w)) := by
  ext a
  rw [show a ∈ powerBoundedSubring (WPA K w) ↔ IsPowerBounded a from Iff.rfl,
    isPowerBounded_wpa_iff ϖ a]
  exact (FiniteJet.mem_unitBall_iff _ a).symm

variable {K w} in
/-- **`𝒜` is uniform** ([WP] prop:parity-uniform-domain / thm 6.2(1)). -/
theorem isUniform_WPA (ϖ : Uniformizer K) : IsUniform (WPA K w) := by
  refine ⟨fun U hU => ?_⟩
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hU
  refine ⟨Metric.ball 0 ε, Metric.ball_mem_nhds 0 hε, ?_⟩
  rintro z ⟨s, hs, y, hy, rfl⟩
  rw [Metric.mem_ball, dist_zero_right] at hy
  refine hball ?_
  rw [Metric.mem_ball, dist_zero_right]
  have hs1 : ‖s‖ ≤ 1 := (isPowerBounded_wpa_iff ϖ s).mp hs
  calc ‖s * y‖ ≤ ‖s‖ * ‖y‖ := norm_mul_le _ _
    _ ≤ 1 * ‖y‖ := mul_le_mul_of_nonneg_right hs1 (norm_nonneg _)
    _ = ‖y‖ := one_mul _
    _ < ε := hy

end WeightedParity
