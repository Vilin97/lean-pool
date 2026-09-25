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
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.WP.Heads
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.WP.FormalReduced

/-!
# The tail decomposition and the twisted `c₀`-sum ([WP] §6.4)

The isometric Banach-decomposition `𝒜 ≅ ⊕̂^{c₀}_μ 𝒜_N e_μ` ([WP]
eq:tail-decomposition) is carried COEFFICIENTWISE: for each tail index `μ` the
`μ`-th component of `f ∈ 𝒜` is a head element (`tailCoeff`), the `μ = 0` component is
the norm-nonincreasing algebra retraction `ρ_N` ([WP] eq:head-retraction), and
multiplication obeys the twisted rule `e_μ e_λ = W^{ω(μ)+ω(λ)−ω(μ+λ)} e_{μ+λ}`
([WP] eq:tail-multiplication).

The abstract receptacle is `TailC0`: for a normed ultrametric commutative ring `P`
and a "twist element" `ρ` of norm `≤ 1` (the image of `W`), the null families
`TailIdx N → P` with sup norm and `ρ`-twisted convolution.  Instances of `TailC0`
appear as: the model of every rational localization of `𝒜`
([WP] prop:coefficientwise-localization, cor:finite-head-presentation) and the bad
chart `ℬ` itself ([WP] §6.2 — the weighted norm of eq:weighted-chart-norm is exactly
the plain sup norm in the twisted coordinates).

The embedding `Φ : TailC0 → MvPowerSeries` ([WP] eq:formal-embedding,
`x ↦ ∑ ρ^{ω(μ)} x_μ U^μ`) is also defined here; it is multiplicative BECAUSE of the
twist and injective when `ρ` is regular, and serves both the reducedness theorem
([WP] thm:parity-rationally-reduced) and the domain property of the chart
([WP] prop:weighted-chart-domain-nonuniform).
-/

@[expose] public section

@[expose] public section

namespace WeightedParity

open FiniteJetOver Filter Topology

variable (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable (w : ℕ → ℕ) (N : ℕ)

/-! ### Coefficientwise tail decomposition of `𝒜` -/

/-- The `μ`-th tail coefficient of `f ∈ 𝒜`: the head element whose `h`-th coefficient
is the `(h + tailShift μ)`-th coefficient of `f` ([WP] eq:tail-decomposition, read
coefficientwise via the exponent splitting of `WP/Weight.lean`). -/
noncomputable def tailCoeff (μ : TailIdx N) (f : WPA K w) : WPHead K w N := by
  classical
  refine ⟨⟨fun h => if HeadMem w N h then coeffA K w (h + tailShift w μ) f else 0, ?_⟩,
    fun h hh => by
      show (if HeadMem w N h then coeffA K w (h + tailShift w μ) f else 0) = 0
      rw [if_neg hh]⟩
  show MvPowerSeries.IsRestrictedGauss _ _
  have hchar : ∀ ε' : ℝ, 0 < ε' → {h : ℕ →₀ ℕ |
      ε' ≤ ‖(if HeadMem w N h then coeffA K w (h + tailShift w μ) f else 0 : K)‖}.Finite := by
    intro ε' hε'
    have hfin := finite_setOf_le_norm_coeff (f := f.1) hε'
    refine (hfin.preimage
      (Set.injOn_of_injective (add_left_injective (tailShift w μ)))).subset ?_
    intro h hu
    rw [Set.mem_setOf_eq] at hu
    by_cases hmem : HeadMem w N h
    · rw [if_pos hmem] at hu
      exact hu
    · rw [if_neg hmem, norm_zero] at hu
      exact absurd (hε'.trans_le hu) (lt_irrefl 0)
  show Filter.Tendsto _ Filter.cofinite (nhds 0)
  rw [Metric.tendsto_nhds]
  intro ε' hε'
  rw [Filter.eventually_cofinite]
  refine (hchar ε' hε').subset ?_
  intro h hu
  rw [Set.mem_setOf_eq] at hu ⊢
  rw [Real.dist_eq, sub_zero, prod_one_weights, mul_one] at hu
  rw [abs_of_nonneg (norm_nonneg _)] at hu
  exact not_lt.mp hu

open scoped Classical in
variable {K w N} in
/-- The coefficients of a tail coefficient, unconditionally. -/
theorem coeff_tailCoeff (μ : TailIdx N) (f : WPA K w) (h : ℕ →₀ ℕ) :
    MvPowerSeries.coeff h (tailCoeff K w N μ f).1.1 =
      if HeadMem w N h then coeffA K w (h + tailShift w μ) f else 0 := rfl

@[simp] theorem coeffA_tailCoeff (μ : TailIdx N) (f : WPA K w) {h : ℕ →₀ ℕ}
    (hh : HeadMem w N h) :
    MvPowerSeries.coeff h (tailCoeff K w N μ f).1.1 =
      coeffA K w (h + tailShift w μ) f := by
  classical
  rw [coeff_tailCoeff, if_pos hh]

theorem tailCoeff_add (μ : TailIdx N) (f g : WPA K w) :
    tailCoeff K w N μ (f + g) = tailCoeff K w N μ f + tailCoeff K w N μ g := by
  classical
  refine Subtype.ext (Subtype.ext (MvPowerSeries.ext fun h => ?_))
  show MvPowerSeries.coeff h (tailCoeff K w N μ (f + g)).1.1 =
    MvPowerSeries.coeff h ((tailCoeff K w N μ f).1.1 + (tailCoeff K w N μ g).1.1)
  rw [map_add, coeff_tailCoeff, coeff_tailCoeff, coeff_tailCoeff]
  have hadd : coeffA K w (h + tailShift w μ) (f + g) =
      coeffA K w (h + tailShift w μ) f + coeffA K w (h + tailShift w μ) g := by
    show MvPowerSeries.coeff (h + tailShift w μ) ((f + g).1.1) = _
    rw [show ((f + g).1.1 : MvPowerSeries ℕ K) = f.1.1 + g.1.1 from rfl, map_add]
    rfl
  rw [hadd]
  split_ifs <;> simp

theorem norm_tailCoeff_le (μ : TailIdx N) (f : WPA K w) :
    ‖tailCoeff K w N μ f‖ ≤ ‖f‖ := by
  classical
  rw [show ‖tailCoeff K w N μ f‖ = ‖headIncl K w N (tailCoeff K w N μ f)‖ from rfl,
    norm_eq_iSup_coeffA]
  refine ciSup_le fun t => ?_
  show ‖MvPowerSeries.coeff t (tailCoeff K w N μ f).1.1‖ ≤ ‖f‖
  rw [coeff_tailCoeff]
  split_ifs with hmem
  · exact norm_coeffA_le K w _ f
  · simpa using norm_nonneg f

/-- The tail coefficients of a fixed element form a null family ([WP]
eq:tail-decomposition: the decomposition is a `c₀`-sum). -/
theorem tendsto_norm_tailCoeff_cofinite (f : WPA K w) :
    Tendsto (fun μ : TailIdx N => ‖tailCoeff K w N μ f‖) cofinite (𝓝 0) := by
  classical
  rw [Metric.tendsto_nhds]
  intro ε hε
  rw [Filter.eventually_cofinite]
  have hfin := finite_setOf_le_norm_coeff (f := f.1) (half_pos hε)
  refine ((hfin.image fun t => tailPart N t).subset ?_)
  intro μ hμ
  rw [Set.mem_setOf_eq, Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _),
    not_lt] at hμ
  by_contra hcon
  have hall : ∀ h : ℕ →₀ ℕ,
      ‖MvPowerSeries.coeff h (tailCoeff K w N μ f).1.1‖ ≤ ε / 2 := by
    intro h
    rw [coeff_tailCoeff]
    split_ifs with hmem
    · by_contra hgt
      push_neg at hgt
      exact hcon ⟨h + tailShift w μ, hgt.le, tailPart_of_headMem_add hmem μ⟩
    · simpa using (half_pos hε).le
  have hnorm : ‖tailCoeff K w N μ f‖ ≤ ε / 2 := by
    rw [show ‖tailCoeff K w N μ f‖ = ‖headIncl K w N (tailCoeff K w N μ f)‖ from rfl,
      norm_eq_iSup_coeffA]
    exact ciSup_le fun t => hall t
  linarith [hμ.trans hnorm]

theorem norm_eq_iSup_tailCoeff (f : WPA K w) :
    ‖f‖ = ⨆ μ : TailIdx N, ‖tailCoeff K w N μ f‖ := by
  classical
  have hbdd : BddAbove (Set.range fun μ : TailIdx N => ‖tailCoeff K w N μ f‖) :=
    ⟨‖f‖, Set.forall_mem_range.mpr fun μ => norm_tailCoeff_le K w N μ f⟩
  apply le_antisymm
  · rw [norm_eq_iSup_coeffA]
    refine ciSup_le fun t => ?_
    by_cases ht : WPMem w t
    · have hh := headMem_headPart (w := w) (N := N) ht
      have hco : coeffA K w t f =
          MvPowerSeries.coeff (headPart w N t)
            (tailCoeff K w N (tailPart N t) f).1.1 := by
        rw [coeffA_tailCoeff K w N (tailPart N t) f hh,
          headPart_add_tailShift (w := w) (N := N) ht]
      rw [hco]
      exact le_trans
        (norm_coeff_le_one_norm (tailCoeff K w N (tailPart N t) f).1 (headPart w N t))
        (le_ciSup hbdd (tailPart N t))
    · rw [coeffA_of_not_wpMem K w ht f, norm_zero]
      exact le_trans (norm_nonneg (tailCoeff K w N 0 f)) (le_ciSup hbdd 0)
  · exact ciSup_le fun μ => norm_tailCoeff_le K w N μ f

/-- Separation: an element of `𝒜` is determined by its tail coefficients. -/
theorem tailCoeff_injective :
    Function.Injective (fun (f : WPA K w) (μ : TailIdx N) => tailCoeff K w N μ f) := by
  classical
  intro f g hfg
  apply coeffA_injective K w
  funext t
  show coeffA K w t f = coeffA K w t g
  by_cases ht : WPMem w t
  · have hh := headMem_headPart (w := w) (N := N) ht
    have h1 : tailCoeff K w N (tailPart N t) f = tailCoeff K w N (tailPart N t) g :=
      congrFun hfg (tailPart N t)
    rw [← headPart_add_tailShift (w := w) (N := N) ht,
      ← coeffA_tailCoeff K w N (tailPart N t) f hh,
      ← coeffA_tailCoeff K w N (tailPart N t) g hh, h1]
  · rw [coeffA_of_not_wpMem K w ht f, coeffA_of_not_wpMem K w ht g]

/-- The `e_μ` basis element `W^{ω(μ)} U^μ` of `𝒜` ([WP] eq:tail-basis). -/
noncomputable def eTail (μ : TailIdx N) : WPA K w :=
  wpMonomial K w (wpMem_tailShift w μ) 1

@[simp] theorem tailCoeff_headIncl_mul_eTail (μ ν : TailIdx N) (x : WPHead K w N) :
    tailCoeff K w N ν (headIncl K w N x * eTail K w N μ) =
      if ν = μ then x else 0 := by
  classical
  refine Subtype.ext (Subtype.ext (MvPowerSeries.ext fun h => ?_))
  rw [coeff_tailCoeff]
  have hco : coeffA K w (h + tailShift w ν) (headIncl K w N x * eTail K w N μ) =
      MvPowerSeries.coeff (h + tailShift w ν)
        (x.1.1 * MvPowerSeries.monomial (tailShift w μ) (1 : K)) := rfl
  by_cases hνμ : ν = μ
  · subst hνμ
    rw [if_pos rfl]
    by_cases hmem : HeadMem w N h
    · rw [if_pos hmem, hco, MvPowerSeries.coeff_add_mul_monomial, mul_one]
    · rw [if_neg hmem]
      exact (x.2 h hmem).symm
  · rw [if_neg hνμ]
    have h0 : MvPowerSeries.coeff h ((0 : WPHead K w N)).1.1 = 0 := by
      show MvPowerSeries.coeff h (0 : MvPowerSeries ℕ K) = 0
      simp
    rw [h0]
    by_cases hmem : HeadMem w N h
    · rw [if_pos hmem, hco, MvPowerSeries.coeff_mul_monomial]
      split_ifs with hle
      · rw [mul_one]
        refine x.2 _ fun hE => hνμ (Subtype.ext (Finsupp.ext fun n => ?_))
        by_cases hn : N < n
        · have hh0 : h n = 0 := hmem.2 n hn
          have hE0 := hE.2 n hn
          have hlen : (tailShift w μ) n ≤ (h + tailShift w ν) n :=
            Finsupp.le_def.mp hle n
          have hsμ : (tailShift w μ) n = μ.1 n := by
            show (Finsupp.single 0 (wpWeight w μ.1) + μ.1 : ℕ →₀ ℕ) n = μ.1 n
            rw [Finsupp.add_apply, Finsupp.single_apply,
              if_neg (by omega : ¬ (0 = n)), zero_add]
          have hsν : (tailShift w ν) n = ν.1 n := by
            show (Finsupp.single 0 (wpWeight w ν.1) + ν.1 : ℕ →₀ ℕ) n = ν.1 n
            rw [Finsupp.add_apply, Finsupp.single_apply,
              if_neg (by omega : ¬ (0 = n)), zero_add]
          rw [Finsupp.tsub_apply, Finsupp.add_apply, hsμ, hsν, hh0] at hE0
          rw [Finsupp.add_apply, hsμ, hsν, hh0] at hlen
          omega
        · rw [μ.prop n (by omega), ν.prop n (by omega)]
      · rfl
    · rw [if_neg hmem]

variable {w N} in
@[simp] theorem tailShift_zero : tailShift w (0 : TailIdx N) = 0 := by
  show Finsupp.single 0 (wpWeight w (0 : TailIdx N).1) + (0 : TailIdx N).1 = 0
  rw [TailIdx.zero_val, wpWeight_zero, Finsupp.single_zero, add_zero]

open scoped Classical in
variable {K w N} in
/-- The `μ = 0` tail coefficient reads the head coefficients in place. -/
theorem coeff_tailCoeff_zero (f : WPA K w) (h : ℕ →₀ ℕ) :
    MvPowerSeries.coeff h (tailCoeff K w N 0 f).1.1 =
      if HeadMem w N h then coeffA K w h f else 0 := by
  rw [coeff_tailCoeff, tailShift_zero, add_zero]

theorem tailCoeff_zero_map (μ : TailIdx N) :
    tailCoeff K w N μ (0 : WPA K w) = 0 := by
  classical
  refine Subtype.ext (Subtype.ext (MvPowerSeries.ext fun h => ?_))
  rw [coeff_tailCoeff]
  show _ = MvPowerSeries.coeff h (0 : MvPowerSeries ℕ K)
  have hz : coeffA K w (h + tailShift w μ) (0 : WPA K w) = 0 := by
    show MvPowerSeries.coeff (h + tailShift w μ) (0 : MvPowerSeries ℕ K) = 0
    simp
  rw [hz]
  split_ifs <;> simp

theorem tailCoeff_zero_one : tailCoeff K w N 0 (1 : WPA K w) = 1 := by
  classical
  refine Subtype.ext (Subtype.ext (MvPowerSeries.ext fun h => ?_))
  rw [coeff_tailCoeff_zero]
  show _ = MvPowerSeries.coeff h (1 : MvPowerSeries ℕ K)
  by_cases hmem : HeadMem w N h
  · rw [if_pos hmem]
    rfl
  · rw [if_neg hmem, MvPowerSeries.coeff_one, if_neg]
    intro h0
    subst h0
    exact hmem ⟨wpMem_zero w, fun n _ => rfl⟩

theorem tailCoeff_zero_mul (f g : WPA K w) :
    tailCoeff K w N 0 (f * g) = tailCoeff K w N 0 f * tailCoeff K w N 0 g := by
  classical
  refine Subtype.ext (Subtype.ext (MvPowerSeries.ext fun h => ?_))
  rw [coeff_tailCoeff_zero]
  show _ = MvPowerSeries.coeff h ((tailCoeff K w N 0 f).1.1 * (tailCoeff K w N 0 g).1.1)
  by_cases hmem : HeadMem w N h
  · rw [if_pos hmem]
    show MvPowerSeries.coeff h (f.1.1 * g.1.1) = _
    rw [MvPowerSeries.coeff_mul, MvPowerSeries.coeff_mul]
    refine Finset.sum_congr rfl fun p hp => ?_
    have hsum : p.1 + p.2 = h := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
    have htails1 : ∀ n, N < n → p.1 n = 0 := by
      intro n hn
      have hhn : h n = 0 := hmem.2 n hn
      have hpn : p.1 n + p.2 n = h n := by rw [← hsum, Finsupp.add_apply]
      omega
    have htails2 : ∀ n, N < n → p.2 n = 0 := by
      intro n hn
      have hhn : h n = 0 := hmem.2 n hn
      have hpn : p.1 n + p.2 n = h n := by rw [← hsum, Finsupp.add_apply]
      omega
    rw [coeff_tailCoeff_zero, coeff_tailCoeff_zero]
    by_cases h1 : HeadMem w N p.1
    · by_cases h2 : HeadMem w N p.2
      · rw [if_pos h1, if_pos h2]
        rfl
      · rw [if_pos h1, if_neg h2]
        have hz : MvPowerSeries.coeff p.2 g.1.1 = 0 :=
          g.2 p.2 fun hwp => h2 ⟨hwp, htails2⟩
        show MvPowerSeries.coeff p.1 f.1.1 * MvPowerSeries.coeff p.2 g.1.1 = _
        rw [hz, mul_zero, mul_zero]
    · rw [if_neg h1]
      have hz : MvPowerSeries.coeff p.1 f.1.1 = 0 :=
        f.2 p.1 fun hwp => h1 ⟨hwp, htails1⟩
      show MvPowerSeries.coeff p.1 f.1.1 * MvPowerSeries.coeff p.2 g.1.1 = _
      rw [hz, zero_mul, zero_mul]
  · rw [if_neg hmem]
    exact ((tailCoeff K w N 0 f * tailCoeff K w N 0 g).2 h hmem).symm

/-- The head retraction `ρ_N` — the `μ = 0` tail coefficient — is a ring homomorphism
([WP] eq:head-retraction: "Projection to the coefficient of `e_0` is a
norm-nonincreasing algebra retraction"). -/
noncomputable def rhoHead : WPA K w →+* WPHead K w N where
  toFun := tailCoeff K w N 0
  map_one' := tailCoeff_zero_one K w N
  map_mul' := tailCoeff_zero_mul K w N
  map_zero' := tailCoeff_zero_map K w N 0
  map_add' := tailCoeff_add K w N 0

@[simp] theorem rhoHead_apply (f : WPA K w) :
    rhoHead K w N f = tailCoeff K w N 0 f := rfl

@[simp] theorem rhoHead_headIncl (x : WPHead K w N) :
    rhoHead K w N (headIncl K w N x) = x := by
  classical
  refine Subtype.ext (Subtype.ext (MvPowerSeries.ext fun h => ?_))
  show MvPowerSeries.coeff h (tailCoeff K w N 0 (headIncl K w N x)).1.1 = _
  rw [coeff_tailCoeff_zero]
  by_cases hmem : HeadMem w N h
  · rw [if_pos hmem]
    rfl
  · rw [if_neg hmem]
    exact (x.2 h hmem).symm

theorem norm_rhoHead_le (f : WPA K w) : ‖rhoHead K w N f‖ ≤ ‖f‖ :=
  norm_tailCoeff_le K w N 0 f

/-- The variable `W` as a head element. -/
noncomputable def WaHead : WPHead K w N :=
  ⟨⟨MvPowerSeries.monomial (Finsupp.single 0 1) (1 : K),
      MvPowerSeries.isRestrictedGauss_monomial _ _ _⟩, fun s hs => by
    show MvPowerSeries.coeff s
      (MvPowerSeries.monomial (Finsupp.single 0 1) (1 : K)) = 0
    classical
    rw [MvPowerSeries.coeff_monomial, if_neg]
    intro h0
    subst h0
    refine hs ⟨wpMem_single_zero w 1, fun n hn => ?_⟩
    rw [Finsupp.single_apply, if_neg (by omega : ¬ (0 = n))]⟩

@[simp] theorem headIncl_WaHead : headIncl K w N (WaHead K w N) = Wa K w := rfl

/-- **The twisted multiplication rule** ([WP] eq:tail-multiplication:
`e_μ e_λ = W^{ω(μ)+ω(λ)−ω(μ+λ)} e_{μ+λ}`; the excess exponent is `≥ 0` by
subadditivity of `ω`). -/
theorem eTail_mul (μ ν : TailIdx N) :
    eTail K w N μ * eTail K w N ν =
      headIncl K w N (WaHead K w N ^
          (wpWeight w μ.1 + wpWeight w ν.1 - wpWeight w (μ + ν).1)) *
        eTail K w N (μ + ν) := by
  classical
  refine Subtype.ext (Subtype.ext ?_)
  let V : WPHead K w N →+* MvPowerSeries ℕ K :=
    ((MvPowerSeries.isSubring (fun _ : ℕ => (1 : ℝ))).subtype).comp
      (wpHeadSupport K w N).subtype
  have hV : ∀ g : WPHead K w N, V g = g.1.1 := fun _ => rfl
  have hpow : (WaHead K w N ^
      (wpWeight w μ.1 + wpWeight w ν.1 - wpWeight w (μ + ν).1)).1.1 =
      MvPowerSeries.monomial
        (Finsupp.single 0
          (wpWeight w μ.1 + wpWeight w ν.1 - wpWeight w (μ + ν).1)) (1 : K) := by
    rw [← hV, map_pow]
    have hX : V (WaHead K w N) = MvPowerSeries.X 0 := rfl
    rw [hX, MvPowerSeries.X_pow_eq]
  have hexp : tailShift w μ + tailShift w ν =
      Finsupp.single 0
          (wpWeight w μ.1 + wpWeight w ν.1 - wpWeight w (μ + ν).1) +
        tailShift w (μ + ν) := by
    have hsub : wpWeight w (μ.1 + ν.1) ≤ wpWeight w μ.1 + wpWeight w ν.1 :=
      wpWeight_add_le w μ.1 ν.1
    ext n
    simp only [tailShift, TailIdx.add_val, Finsupp.add_apply, Finsupp.single_apply]
    by_cases h0 : 0 = n
    · subst h0
      have hμ0 : μ.1 0 = 0 := μ.prop 0 (Nat.zero_le N)
      have hν0 : ν.1 0 = 0 := ν.prop 0 (Nat.zero_le N)
      simp only [if_true, hμ0, hν0]
      omega
    · simp only [if_neg h0]
      omega
  show MvPowerSeries.monomial (tailShift w μ) (1 : K) *
      MvPowerSeries.monomial (tailShift w ν) 1 =
      (WaHead K w N ^
        (wpWeight w μ.1 + wpWeight w ν.1 - wpWeight w (μ + ν).1)).1.1 *
      MvPowerSeries.monomial (tailShift w (μ + ν)) 1
  rw [hpow, MvPowerSeries.monomial_mul_monomial, MvPowerSeries.monomial_mul_monomial,
    one_mul, hexp]

/-! ### The twisted `c₀`-sum `TailC0` -/

/-- A twist element: a norm-`≤ 1` element of a normed ring (the image of `W`).
Norm `≤ 1` is what keeps the twisted convolution submultiplicative and `c₀`-valued. -/
structure TwistElem (P : Type*) [NormedCommRing P] where
  /-- The underlying element. -/
  val : P
  /-- The twist element lies in the unit ball. -/
  norm_le_one : ‖val‖ ≤ 1

/-- Tail indices have finite addition fibers: the antidiagonal is pulled back from
the ambient exponent antidiagonal (both components of an ambient splitting of a
tail index are automatically tail indices). -/
noncomputable instance (N : ℕ) : Finset.HasAntidiagonal (TailIdx N) where
  antidiagonal τ :=
    (Finset.HasAntidiagonal.antidiagonal τ.1).attach.map
      ⟨fun p =>
        (⟨p.1.1, fun n hn => by
            have hpt : p.1.1 + p.1.2 = τ.1 :=
              Finset.HasAntidiagonal.mem_antidiagonal.mp p.2
            have hτ0 : τ.1 n = 0 := τ.prop n hn
            have hsum : p.1.1 n + p.1.2 n = τ.1 n := by
              rw [← Finsupp.add_apply, hpt]
            omega⟩,
          ⟨p.1.2, fun n hn => by
            have hpt : p.1.1 + p.1.2 = τ.1 :=
              Finset.HasAntidiagonal.mem_antidiagonal.mp p.2
            have hτ0 : τ.1 n = 0 := τ.prop n hn
            have hsum : p.1.1 n + p.1.2 n = τ.1 n := by
              rw [← Finsupp.add_apply, hpt]
            omega⟩),
        fun p q hpq => by
          have h1 : p.1.1 = q.1.1 := congrArg (fun z => z.1.1) hpq
          have h2 : p.1.2 = q.1.2 := congrArg (fun z => z.2.1) hpq
          exact Subtype.ext (Prod.ext h1 h2)⟩
  mem_antidiagonal {τ} {p} := by
    rw [Finset.mem_map]
    constructor
    · rintro ⟨q, -, rfl⟩
      have hqt : q.1.1 + q.1.2 = τ.1 :=
        Finset.HasAntidiagonal.mem_antidiagonal.mp q.2
      exact Subtype.ext (by rw [TailIdx.add_val]; exact hqt)
    · intro hp
      refine ⟨⟨(p.1.1, p.2.1), ?_⟩, Finset.mem_attach _ _, ?_⟩
      · rw [Finset.HasAntidiagonal.mem_antidiagonal]
        have h := congrArg Subtype.val hp
        rw [TailIdx.add_val] at h
        exact h
      · refine Prod.ext ?_ ?_ <;> exact Subtype.ext rfl

instance (N : ℕ) : Nonempty (TailIdx N) := ⟨0⟩

/-- Swap symmetry of the tail antidiagonal. -/
theorem sum_antidiagonal_swap {N : ℕ} {M : Type*} [AddCommMonoid M] (τ : TailIdx N)
    (f : TailIdx N → TailIdx N → M) :
    ∑ p ∈ Finset.HasAntidiagonal.antidiagonal τ, f p.1 p.2 =
      ∑ p ∈ Finset.HasAntidiagonal.antidiagonal τ, f p.2 p.1 :=
  Finset.sum_equiv (Equiv.prodComm _ _)
    (fun p => by
      simp only [Finset.HasAntidiagonal.mem_antidiagonal, Equiv.prodComm_apply,
        Prod.fst_swap, Prod.snd_swap]
      constructor <;> intro h <;> rw [← h] <;> exact add_comm _ _)
    (fun p _ => rfl)

/-- The twisted `c₀`-sum `⊕̂^{c₀}_μ P e_μ` ([WP] eq:tail-decomposition's receptacle):
null families `TailIdx N → P` with sup norm and `ρ`-twisted convolution
`(x*y)_τ = ∑_{μ+λ=τ} ρ^{ω(μ)+ω(λ)−ω(τ)} x_μ y_λ` (the weight `w` enters through the
twist exponents, so it is a genuine parameter of the ring structure). -/
def TailC0 (w : ℕ → ℕ) (N : ℕ) (P : Type*) [NormedCommRing P] [IsUltrametricDist P]
    (ρ : TwistElem P) : Type _ :=
  have _ := w
  have _ := ρ
  {x : TailIdx N → P // Tendsto (fun μ => ‖x μ‖) cofinite (𝓝 0)}

namespace TailC0

variable {w : ℕ → ℕ} {N : ℕ} {P : Type*} [NormedCommRing P] [IsUltrametricDist P]
  {ρ : TwistElem P}

variable (N P) in
/-- The additive subgroup of null families underlying `TailC0`. -/
noncomputable def addSubgroup : AddSubgroup (TailIdx N → P) where
  carrier := {x | Tendsto (fun μ => ‖x μ‖) cofinite (𝓝 0)}
  zero_mem' := by
    simpa using tendsto_const_nhds
  add_mem' {x y} hx hy := by
    refine .squeeze tendsto_const_nhds (by simpa using hx.add hy)
      (fun μ => norm_nonneg _) fun μ => norm_add_le _ _
  neg_mem' {x} hx := by simpa using hx

noncomputable instance : AddCommGroup (TailC0 w N P ρ) :=
  inferInstanceAs (AddCommGroup ↥(addSubgroup N P))

noncomputable instance : One (TailC0 w N P ρ) :=
  ⟨⟨fun ν => if ν = 0 then 1 else 0, by
    rw [Metric.tendsto_nhds]
    intro ε hε
    rw [Filter.eventually_cofinite]
    refine (Set.finite_singleton (0 : TailIdx N)).subset fun ν hν => ?_
    rw [Set.mem_setOf_eq] at hν
    rw [Set.mem_singleton_iff]
    by_contra hne
    apply hν
    show dist ‖if ν = (0 : TailIdx N) then (1 : P) else 0‖ 0 < ε
    rw [if_neg hne, norm_zero, dist_self]
    exact hε⟩⟩

noncomputable instance : Mul (TailC0 w N P ρ) :=
  ⟨fun x y =>
    ⟨fun τ => ∑ p ∈ Finset.HasAntidiagonal.antidiagonal τ,
        ρ.val ^ (wpWeight w p.1.1 + wpWeight w p.2.1 - wpWeight w τ.1) *
          (x.1 p.1 * y.1 p.2), by
      refine .squeeze tendsto_const_nhds
        (MvPowerSeries.tendsto_sup'_antidiagonal_cofinite
          (f := fun p : TailIdx N × TailIdx N => ‖x.1 p.1‖ * ‖y.1 p.2‖)
          (tendsto_mul_cofinite_nhds_zero x.2 y.2))
        (fun τ => norm_nonneg _) (fun τ => ?_)
      refine le_trans ((Finset.nonempty_antidiagonal τ).norm_sum_le_sup'_norm _) ?_
      refine Finset.sup'_mono_fun fun p hp => ?_
      rcases Nat.eq_zero_or_pos
        (wpWeight w p.1.1 + wpWeight w p.2.1 - wpWeight w τ.1) with he | he
      · rw [he, pow_zero, one_mul]
        exact norm_mul_le _ _
      · refine le_trans (norm_mul_le _ _) ?_
        refine le_trans (mul_le_mul_of_nonneg_right
          (le_trans (norm_pow_le' _ he)
            (pow_le_one₀ (norm_nonneg _) ρ.norm_le_one)) (norm_nonneg _)) ?_
        rw [one_mul]
        exact norm_mul_le _ _⟩⟩

theorem mul_val (x y : TailC0 w N P ρ) (τ : TailIdx N) :
    (x * y).1 τ = ∑ p ∈ Finset.HasAntidiagonal.antidiagonal τ,
      ρ.val ^ (wpWeight w p.1.1 + wpWeight w p.2.1 - wpWeight w τ.1) *
        (x.1 p.1 * y.1 p.2) := rfl

theorem one_val (τ : TailIdx N) :
    (1 : TailC0 w N P ρ).1 τ = if τ = 0 then 1 else 0 := rfl

theorem mul_comm_aux (x y : TailC0 w N P ρ) : x * y = y * x := by
  refine Subtype.ext (funext fun τ => ?_)
  rw [mul_val, mul_val]
  have hswap := sum_antidiagonal_swap τ (fun a b =>
    ρ.val ^ (wpWeight w a.1 + wpWeight w b.1 - wpWeight w τ.1) * (y.1 a * x.1 b))
  rw [hswap]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [add_comm (wpWeight w p.1.1) (wpWeight w p.2.1), mul_comm (x.1 p.1) (y.1 p.2)]

theorem one_mul_aux (x : TailC0 w N P ρ) : 1 * x = x := by
  refine Subtype.ext (funext fun τ => ?_)
  rw [mul_val]
  refine (Finset.sum_eq_single_of_mem ((0 : TailIdx N), τ)
    (Finset.HasAntidiagonal.mem_antidiagonal.mpr (zero_add τ)) ?_).trans ?_
  · intro p hp hne
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    by_cases h1 : p.1 = 0
    · exact absurd (Prod.ext h1 (by rw [h1, zero_add] at hp; exact hp)) hne
    · rw [one_val, if_neg h1, zero_mul, mul_zero]
  · rw [one_val, if_pos rfl, one_mul, TailIdx.zero_val, wpWeight_zero, zero_add,
      Nat.sub_self, pow_zero, one_mul]

theorem mul_one_aux (x : TailC0 w N P ρ) : x * 1 = x := by
  rw [mul_comm_aux, one_mul_aux]

theorem zero_mul_aux (x : TailC0 w N P ρ) : 0 * x = 0 := by
  refine Subtype.ext (funext fun τ => ?_)
  show (0 * x : TailC0 w N P ρ).1 τ = (0 : P)
  rw [mul_val]
  exact Finset.sum_eq_zero fun p _ => by
    rw [show ((0 : TailC0 w N P ρ)).1 p.1 = 0 from rfl, zero_mul, mul_zero]

theorem mul_zero_aux (x : TailC0 w N P ρ) : x * 0 = 0 := by
  rw [mul_comm_aux, zero_mul_aux]

theorem left_distrib_aux (x y z : TailC0 w N P ρ) : x * (y + z) = x * y + x * z := by
  refine Subtype.ext (funext fun τ => ?_)
  show (x * (y + z)).1 τ = (x * y).1 τ + (x * z).1 τ
  rw [mul_val, mul_val, mul_val, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [show ((y + z) : TailC0 w N P ρ).1 p.2 = y.1 p.2 + z.1 p.2 from rfl, mul_add,
    mul_add]

theorem mul_assoc_aux (x y z : TailC0 w N P ρ) : x * y * z = x * (y * z) := by
  classical
  have key : ∀ (a b c d : ℕ) (u v s : P), a + b = c + d →
      ρ.val ^ a * ((ρ.val ^ b * (u * v)) * s) =
        ρ.val ^ c * (u * (ρ.val ^ d * (v * s))) := by
    intro a b c d u v s h
    rw [show ρ.val ^ a * ((ρ.val ^ b * (u * v)) * s) =
        ρ.val ^ (a + b) * (u * (v * s)) by rw [pow_add]; ring,
      show ρ.val ^ c * (u * (ρ.val ^ d * (v * s))) =
        ρ.val ^ (c + d) * (u * (v * s)) by rw [pow_add]; ring, h]
  refine Subtype.ext (funext fun τ => ?_)
  show (x * y * z).1 τ = (x * (y * z)).1 τ
  rw [mul_val (x * y) z, mul_val x (y * z)]
  have hL : ∀ p : TailIdx N × TailIdx N,
      ρ.val ^ (wpWeight w p.1.1 + wpWeight w p.2.1 - wpWeight w τ.1) *
        ((x * y).1 p.1 * z.1 p.2) =
      ∑ q ∈ Finset.HasAntidiagonal.antidiagonal p.1,
        ρ.val ^ (wpWeight w p.1.1 + wpWeight w p.2.1 - wpWeight w τ.1) *
          ((ρ.val ^ (wpWeight w q.1.1 + wpWeight w q.2.1 - wpWeight w p.1.1) *
            (x.1 q.1 * y.1 q.2)) * z.1 p.2) := by
    intro p
    rw [mul_val, Finset.sum_mul, Finset.mul_sum]
  have hR : ∀ p : TailIdx N × TailIdx N,
      ρ.val ^ (wpWeight w p.1.1 + wpWeight w p.2.1 - wpWeight w τ.1) *
        (x.1 p.1 * (y * z).1 p.2) =
      ∑ q ∈ Finset.HasAntidiagonal.antidiagonal p.2,
        ρ.val ^ (wpWeight w p.1.1 + wpWeight w p.2.1 - wpWeight w τ.1) *
          (x.1 p.1 *
            (ρ.val ^ (wpWeight w q.1.1 + wpWeight w q.2.1 - wpWeight w p.2.1) *
              (y.1 q.1 * z.1 q.2))) := by
    intro p
    rw [mul_val, Finset.mul_sum, Finset.mul_sum]
  rw [Finset.sum_congr rfl fun p _ => hL p, Finset.sum_congr rfl fun p _ => hR p,
    Finset.sum_sigma', Finset.sum_sigma']
  refine Finset.sum_nbij' (fun r => ⟨(r.2.1, r.2.2 + r.1.2), (r.2.2, r.1.2)⟩)
    (fun r => ⟨(r.1.1 + r.2.1, r.2.2), (r.1.1, r.2.1)⟩) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨⟨i, j⟩, ⟨k, l⟩⟩ hr
    rw [Finset.mem_sigma] at hr ⊢
    have h1 : i + j = τ := Finset.HasAntidiagonal.mem_antidiagonal.mp hr.1
    have h2 : k + l = i := Finset.HasAntidiagonal.mem_antidiagonal.mp hr.2
    constructor
    · rw [Finset.HasAntidiagonal.mem_antidiagonal, ← h1, ← h2, add_assoc]
    · rw [Finset.HasAntidiagonal.mem_antidiagonal]
  · rintro ⟨⟨a, b⟩, ⟨c, d⟩⟩ hr
    rw [Finset.mem_sigma] at hr ⊢
    have h1 : a + b = τ := Finset.HasAntidiagonal.mem_antidiagonal.mp hr.1
    have h2 : c + d = b := Finset.HasAntidiagonal.mem_antidiagonal.mp hr.2
    constructor
    · rw [Finset.HasAntidiagonal.mem_antidiagonal, add_assoc, h2, h1]
    · rw [Finset.HasAntidiagonal.mem_antidiagonal]
  · rintro ⟨⟨i, j⟩, ⟨k, l⟩⟩ hr
    rw [Finset.mem_sigma] at hr
    have h2 : k + l = i := Finset.HasAntidiagonal.mem_antidiagonal.mp hr.2
    show (⟨(k + l, j), (k, l)⟩ : (_ : TailIdx N × TailIdx N) × TailIdx N × TailIdx N) =
      ⟨(i, j), (k, l)⟩
    rw [h2]
  · rintro ⟨⟨a, b⟩, ⟨c, d⟩⟩ hr
    rw [Finset.mem_sigma] at hr
    have h2 : c + d = b := Finset.HasAntidiagonal.mem_antidiagonal.mp hr.2
    show (⟨(a, c + d), (c, d)⟩ : (_ : TailIdx N × TailIdx N) × TailIdx N × TailIdx N) =
      ⟨(a, b), (c, d)⟩
    rw [h2]
  · rintro ⟨⟨i, j⟩, ⟨k, l⟩⟩ hr
    rw [Finset.mem_sigma] at hr
    have h1 : i + j = τ := Finset.HasAntidiagonal.mem_antidiagonal.mp hr.1
    have h2 : k + l = i := Finset.HasAntidiagonal.mem_antidiagonal.mp hr.2
    have hij : wpWeight w τ.1 ≤ wpWeight w i.1 + wpWeight w j.1 := by
      have hval : τ.1 = i.1 + j.1 := by rw [← h1, TailIdx.add_val]
      rw [hval]
      exact wpWeight_add_le w i.1 j.1
    have hkl : wpWeight w i.1 ≤ wpWeight w k.1 + wpWeight w l.1 := by
      have hval : i.1 = k.1 + l.1 := by rw [← h2, TailIdx.add_val]
      rw [hval]
      exact wpWeight_add_le w k.1 l.1
    have hlj : wpWeight w (l + j).1 ≤ wpWeight w l.1 + wpWeight w j.1 := by
      rw [TailIdx.add_val]
      exact wpWeight_add_le w l.1 j.1
    have hτlj : wpWeight w τ.1 ≤ wpWeight w k.1 + wpWeight w (l + j).1 := by
      have hval : τ.1 = k.1 + (l + j).1 := by
        rw [TailIdx.add_val, ← h1, ← h2, TailIdx.add_val, TailIdx.add_val, add_assoc]
      rw [hval]
      exact wpWeight_add_le w k.1 (l + j).1
    exact key (wpWeight w i.1 + wpWeight w j.1 - wpWeight w τ.1)
      (wpWeight w k.1 + wpWeight w l.1 - wpWeight w i.1)
      (wpWeight w k.1 + wpWeight w (l + j).1 - wpWeight w τ.1)
      (wpWeight w l.1 + wpWeight w j.1 - wpWeight w (l + j).1)
      (x.1 k) (y.1 l) (z.1 j) (by omega)

noncomputable instance : CommRing (TailC0 w N P ρ) :=
  letI G : AddCommGroup (TailC0 w N P ρ) := inferInstance
  { G with
    mul := (· * ·)
    one := 1
    mul_assoc := mul_assoc_aux
    one_mul := one_mul_aux
    mul_one := mul_one_aux
    left_distrib := left_distrib_aux
    right_distrib := fun a b c => by
      rw [mul_comm_aux, left_distrib_aux, mul_comm_aux c a, mul_comm_aux c b]
    zero_mul := zero_mul_aux
    mul_zero := mul_zero_aux
    mul_comm := mul_comm_aux }

noncomputable instance : Norm (TailC0 w N P ρ) :=
  ⟨fun x => ⨆ μ, ‖x.1 μ‖⟩

theorem norm_def (x : TailC0 w N P ρ) : ‖x‖ = ⨆ μ, ‖x.1 μ‖ := rfl

theorem bddAbove_range_norm (x : TailC0 w N P ρ) :
    BddAbove (Set.range fun μ => ‖x.1 μ‖) := by
  have h := x.2
  rw [Metric.tendsto_nhds] at h
  have h1 := h 1 one_pos
  rw [Filter.eventually_cofinite] at h1
  have hsub : (Set.range fun μ => ‖x.1 μ‖) ⊆
      ((fun μ => ‖x.1 μ‖) '' {μ | ¬ dist ‖x.1 μ‖ 0 < 1}) ∪ Set.Iic 1 := by
    rintro r ⟨μ, rfl⟩
    by_cases hμ : dist ‖x.1 μ‖ 0 < 1
    · refine Or.inr ?_
      rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)] at hμ
      exact hμ.le
    · exact Or.inl ⟨μ, hμ, rfl⟩
  exact ((h1.image _).bddAbove.union bddAbove_Iic).mono hsub

theorem norm_coeff_le (x : TailC0 w N P ρ) (μ : TailIdx N) : ‖x.1 μ‖ ≤ ‖x‖ :=
  le_ciSup (bddAbove_range_norm x) μ

noncomputable instance : NormedAddCommGroup (TailC0 w N P ρ) :=
  AddGroupNorm.toNormedAddCommGroup
    { toFun := norm
      map_zero' := by
        rw [norm_def]
        have hz : ∀ μ : TailIdx N, ‖((0 : TailC0 w N P ρ)).1 μ‖ = 0 := fun μ => by
          rw [show ((0 : TailC0 w N P ρ)).1 μ = 0 from rfl, norm_zero]
        simp only [hz, ciSup_const]
      add_le' := fun x y => by
        rw [norm_def]
        refine ciSup_le fun μ => ?_
        refine le_trans (norm_add_le (x.1 μ) (y.1 μ)) ?_
        exact add_le_add (norm_coeff_le x μ) (norm_coeff_le y μ)
      neg' := fun x => by
        rw [norm_def, norm_def]
        refine iSup_congr fun μ => ?_
        rw [show ((-x : TailC0 w N P ρ)).1 μ = -(x.1 μ) from rfl, norm_neg]
      eq_zero_of_map_eq_zero' := fun x hx => by
        refine Subtype.ext (funext fun μ => ?_)
        have h1 : ‖x.1 μ‖ ≤ 0 := le_of_le_of_eq (norm_coeff_le x μ) hx
        show x.1 μ = (0 : P)
        exact norm_eq_zero.mp (le_antisymm h1 (norm_nonneg _)) }

noncomputable instance : NormedCommRing (TailC0 w N P ρ) :=
  { (inferInstance : NormedAddCommGroup (TailC0 w N P ρ)),
    (inferInstance : CommRing (TailC0 w N P ρ)) with
    norm_mul_le := fun x y => by
      rw [norm_def]
      refine ciSup_le fun τ => ?_
      rw [mul_val]
      refine le_trans ((Finset.nonempty_antidiagonal τ).norm_sum_le_sup'_norm _) ?_
      refine Finset.sup'_le _ _ fun p hp => ?_
      have hterm : ‖ρ.val ^ (wpWeight w p.1.1 + wpWeight w p.2.1 - wpWeight w τ.1) *
          (x.1 p.1 * y.1 p.2)‖ ≤ ‖x.1 p.1‖ * ‖y.1 p.2‖ := by
        rcases Nat.eq_zero_or_pos
          (wpWeight w p.1.1 + wpWeight w p.2.1 - wpWeight w τ.1) with he | he
        · rw [he, pow_zero, one_mul]
          exact norm_mul_le _ _
        · refine le_trans (norm_mul_le _ _) ?_
          refine le_trans (mul_le_mul_of_nonneg_right
            (le_trans (norm_pow_le' _ he)
              (pow_le_one₀ (norm_nonneg _) ρ.norm_le_one)) (norm_nonneg _)) ?_
          rw [one_mul]
          exact norm_mul_le _ _
      refine le_trans hterm ?_
      exact mul_le_mul (norm_coeff_le x p.1) (norm_coeff_le y p.2) (norm_nonneg _)
        (le_trans (norm_nonneg _) (norm_coeff_le x p.1)) }

instance : IsUltrametricDist (TailC0 w N P ρ) := by
  refine IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm
    fun x y => ?_
  rw [norm_def]
  refine ciSup_le fun μ => ?_
  refine le_trans (IsUltrametricDist.norm_add_le_max (x.1 μ) (y.1 μ)) ?_
  exact max_le_max (norm_coeff_le x μ) (norm_coeff_le y μ)

instance [CompleteSpace P] : CompleteSpace (TailC0 w N P ρ) := by
  refine Metric.complete_of_cauchySeq_tendsto fun u hu => ?_
  have coeff_le : ∀ (f g : TailC0 w N P ρ) (μ : TailIdx N),
      ‖f.1 μ - g.1 μ‖ ≤ ‖f - g‖ := fun f g μ => by
    have h := norm_coeff_le (f - g) μ
    rwa [show ((f - g) : TailC0 w N P ρ).1 μ = f.1 μ - g.1 μ from rfl] at h
  have coeff_cauchy : ∀ μ : TailIdx N, CauchySeq (fun i => (u i).1 μ) := fun μ => by
    refine Metric.cauchySeq_iff.mpr fun ε hε => ?_
    obtain ⟨n₀, hn₀⟩ := Metric.cauchySeq_iff.mp hu ε hε
    refine ⟨n₀, fun i hi j hj => ?_⟩
    rw [dist_eq_norm]
    have h_uij : ‖u i - u j‖ < ε := by
      have h := hn₀ i hi j hj
      rwa [dist_eq_norm] at h
    exact lt_of_le_of_lt (coeff_le (u i) (u j) μ) h_uij
  choose a ha using fun μ => cauchySeq_tendsto_of_complete (coeff_cauchy μ)
  have unif_conv : ∀ ε > (0 : ℝ), ∃ n₀, ∀ i ≥ n₀, ∀ μ : TailIdx N,
      ‖(u i).1 μ - a μ‖ ≤ ε := by
    intro ε hε
    obtain ⟨n₀, hn₀⟩ := Metric.cauchySeq_iff.mp hu ε hε
    refine ⟨n₀, fun i hi μ => ?_⟩
    have h_lim : Tendsto (fun j => ‖(u i).1 μ - (u j).1 μ‖) atTop
        (𝓝 (‖(u i).1 μ - a μ‖)) := (tendsto_const_nhds.sub (ha μ)).norm
    refine le_of_tendsto h_lim ?_
    filter_upwards [Filter.eventually_ge_atTop n₀] with j hj
    have h_dist := hn₀ i hi j hj
    rw [dist_eq_norm] at h_dist
    exact (lt_of_le_of_lt (coeff_le (u i) (u j) μ) h_dist).le
  have ha_null : Tendsto (fun μ => ‖a μ‖) cofinite (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨n₁, hn₁⟩ := unif_conv (ε / 2) (by linarith)
    have h_u := (u n₁).2
    rw [Metric.tendsto_nhds] at h_u
    have h_u' := h_u (ε / 2) (by linarith)
    rw [Filter.eventually_cofinite] at h_u' ⊢
    refine h_u'.subset fun μ hμ => ?_
    simp only [Set.mem_setOf_eq, Real.dist_eq, sub_zero, not_lt] at hμ ⊢
    rw [abs_of_nonneg (norm_nonneg _)] at hμ ⊢
    have h1 : ‖(u n₁).1 μ - a μ‖ ≤ ε / 2 := hn₁ n₁ le_rfl μ
    have h_ultra : ‖a μ‖ ≤ max ‖(u n₁).1 μ - a μ‖ ‖(u n₁).1 μ‖ := by
      have h2 := IsUltrametricDist.norm_add_le_max (a μ - (u n₁).1 μ) ((u n₁).1 μ)
      rw [sub_add_cancel] at h2
      rwa [norm_sub_rev] at h2
    rcases le_max_iff.mp h_ultra with h | h
    · linarith
    · linarith
  set z : TailC0 w N P ρ := ⟨a, ha_null⟩ with hz
  refine ⟨z, ?_⟩
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨n₀, hn₀⟩ := unif_conv (ε / 2) (by linarith)
  refine ⟨n₀, fun i hi => ?_⟩
  rw [dist_eq_norm]
  have hbd : ∀ μ : TailIdx N, ‖((u i - z) : TailC0 w N P ρ).1 μ‖ ≤ ε / 2 := fun μ => by
    rw [show ((u i - z) : TailC0 w N P ρ).1 μ = (u i).1 μ - a μ from rfl]
    exact hn₀ i hi μ
  have hle : ‖u i - z‖ ≤ ε / 2 := by
    rw [norm_def]
    exact ciSup_le hbd
  linarith

instance [NormOneClass P] [Nontrivial P] : NormOneClass (TailC0 w N P ρ) := by
  refine ⟨?_⟩
  rw [norm_def]
  apply le_antisymm
  · refine ciSup_le fun μ => ?_
    rw [one_val]
    split_ifs with h
    · exact le_of_eq norm_one
    · rw [norm_zero]
      exact zero_le_one
  · have h := norm_coeff_le (1 : TailC0 w N P ρ) 0
    rw [one_val, if_pos rfl, norm_one] at h
    exact h

/-- The coefficient of a twisted `c₀`-family. -/
def coeff (μ : TailIdx N) (x : TailC0 w N P ρ) : P := x.1 μ

/-- The single-index family `p·e_μ`. -/
noncomputable def single (μ : TailIdx N) (p : P) : TailC0 w N P ρ :=
  ⟨fun ν => if ν = μ then p else 0, by
    rw [Metric.tendsto_nhds]
    intro ε hε
    rw [Filter.eventually_cofinite]
    refine (Set.finite_singleton μ).subset fun ν hν => ?_
    rw [Set.mem_setOf_eq] at hν
    rw [Set.mem_singleton_iff]
    by_contra hne
    apply hν
    show dist ‖if ν = μ then p else 0‖ 0 < ε
    rw [if_neg hne, norm_zero, dist_self]
    exact hε⟩

theorem single_val (μ : TailIdx N) (p : P) (ν : TailIdx N) :
    (single (w := w) (ρ := ρ) μ p).1 ν = if ν = μ then p else 0 := rfl

/-- The norm of a single-index family. -/
theorem norm_single (μ : TailIdx N) (p : P) :
    ‖single (w := w) (ρ := ρ) μ p‖ = ‖p‖ := by
  rw [norm_def]
  apply le_antisymm
  · refine ciSup_le fun ν => ?_
    rw [single_val]
    split_ifs
    · exact le_refl _
    · rw [norm_zero]
      exact norm_nonneg p
  · have h := norm_coeff_le (single (w := w) (ρ := ρ) μ p) μ
    rw [single_val, if_pos rfl] at h
    exact h

@[simp] theorem coeff_single (μ ν : TailIdx N) (p : P) :
    coeff ν (single (w := w) (ρ := ρ) μ p) = if ν = μ then p else 0 := rfl

/-- The twisted product of single families ([WP] eq:tail-multiplication in the
abstract model): `(p·e_μ)(q·e_ν) = ρ^{ω(μ)+ω(ν)−ω(μ+ν)}·pq·e_{μ+ν}`. -/
theorem single_mul_single (μ ν : TailIdx N) (p q : P) :
    single (w := w) (ρ := ρ) μ p * single (w := w) (ρ := ρ) ν q =
      single (w := w) (ρ := ρ) (μ + ν)
        (ρ.val ^ (wpWeight w μ.1 + wpWeight w ν.1 - wpWeight w (μ + ν).1) * (p * q)) := by
  refine Subtype.ext (funext fun τ => ?_)
  rw [mul_val, single_val (μ + ν)]
  by_cases hτ : τ = μ + ν
  · rw [if_pos hτ]
    subst hτ
    refine (Finset.sum_eq_single_of_mem (μ, ν)
      (Finset.HasAntidiagonal.mem_antidiagonal.mpr rfl) ?_).trans ?_
    · intro b hb hne
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hb
      by_cases h1 : b.1 = μ
      · exfalso
        apply hne
        refine Prod.ext h1 (Subtype.ext ?_)
        have hval := congrArg Subtype.val hb
        rw [TailIdx.add_val, TailIdx.add_val] at hval
        rw [h1] at hval
        exact add_left_cancel hval
      · rw [single_val, if_neg h1, zero_mul, mul_zero]
    · rw [single_val, if_pos rfl, single_val, if_pos rfl]
  · rw [if_neg hτ]
    refine Finset.sum_eq_zero fun b hb => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hb
    by_cases h1 : b.1 = μ
    · by_cases h2 : b.2 = ν
      · exfalso
        apply hτ
        rw [← hb, h1, h2]
      · rw [single_val ν, if_neg h2, mul_zero, mul_zero]
    · rw [single_val μ, if_neg h1, zero_mul, mul_zero]

theorem norm_eq_iSup_coeff (x : TailC0 w N P ρ) :
    ‖x‖ = ⨆ μ : TailIdx N, ‖coeff μ x‖ := rfl

/-- The head inclusion `P → TailC0` at `μ = 0` is an isometric ring homomorphism. -/
noncomputable def ofHead : P →+* TailC0 w N P ρ where
  toFun p := single (w := w) (ρ := ρ) 0 p
  map_one' := by
    refine Subtype.ext (funext fun ν => ?_)
    rw [single_val, one_val]
  map_mul' p q := by
    rw [single_mul_single 0 0 p q]
    simp only [add_zero, TailIdx.zero_val, wpWeight_zero, Nat.sub_self, pow_zero,
      one_mul]
  map_zero' := by
    refine Subtype.ext (funext fun ν => ?_)
    rw [single_val, show ((0 : TailC0 w N P ρ)).1 ν = (0 : P) from rfl]
    split_ifs <;> rfl
  map_add' p q := by
    refine Subtype.ext (funext fun ν => ?_)
    rw [show ((single (w := w) (ρ := ρ) 0 p + single (w := w) (ρ := ρ) 0 q :
        TailC0 w N P ρ)).1 ν =
      (single (w := w) (ρ := ρ) 0 p).1 ν + (single (w := w) (ρ := ρ) 0 q).1 ν
      from rfl, single_val, single_val, single_val]
    split_ifs <;> simp

@[simp] theorem norm_ofHead (p : P) :
    ‖ofHead (w := w) (N := N) (ρ := ρ) p‖ = ‖p‖ :=
  norm_single 0 p

/-- The head projection `TailC0 → P` at `μ = 0` is a norm-nonincreasing ring
homomorphism splitting `ofHead`. -/
noncomputable def toHead : TailC0 w N P ρ →+* P where
  toFun x := x.1 0
  map_one' := by
    show (1 : TailC0 w N P ρ).1 0 = 1
    rw [one_val, if_pos rfl]
  map_mul' x y := by
    show (x * y).1 0 = x.1 0 * y.1 0
    rw [mul_val]
    refine (Finset.sum_eq_single_of_mem ((0 : TailIdx N), (0 : TailIdx N))
      (Finset.HasAntidiagonal.mem_antidiagonal.mpr (add_zero 0)) ?_).trans ?_
    · intro b hb hne
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hb
      exfalso
      apply hne
      have hval := congrArg Subtype.val hb
      rw [TailIdx.add_val, TailIdx.zero_val] at hval
      obtain ⟨h1, h2⟩ := add_eq_zero.mp hval
      exact Prod.ext (Subtype.ext h1) (Subtype.ext h2)
    · simp only [TailIdx.zero_val, wpWeight_zero, Nat.sub_zero, add_zero, pow_zero,
        one_mul]
  map_zero' := rfl
  map_add' x y := rfl

@[simp] theorem toHead_ofHead (p : P) :
    toHead (ofHead (w := w) (N := N) (ρ := ρ) p) = p := by
  show (single (w := w) (ρ := ρ) 0 p).1 0 = p
  rw [single_val, if_pos rfl]

end TailC0

/-! ### The formal-series embedding `Φ` ([WP] eq:formal-embedding) -/

/-- The tail variable type `{n : ℕ // N < n}` — the `U_n`, `n > N`. -/
def TailVar (N : ℕ) : Type := {n : ℕ // N < n}

/-- Tail indices are finitely supported exponent vectors on the tail variables. -/
noncomputable def tailIdxEquivFinsupp : TailIdx N ≃ (TailVar N →₀ ℕ) where
  toFun μ := Finsupp.subtypeDomain (fun n => N < n) μ.1
  invFun e := ⟨Finsupp.extendDomain e, fun n hn => by
    by_contra h
    have hmem : n ∈ (Finsupp.extendDomain e).support := Finsupp.mem_support_iff.mpr h
    have hlt := Finsupp.support_extendDomain_subset e hmem
    rw [Set.mem_setOf_eq] at hlt
    omega⟩
  left_inv μ := Subtype.ext (Finsupp.extendDomain_subtypeDomain μ.1 fun a ha => by
    by_contra h
    exact (Finsupp.mem_support_iff.mp ha) (μ.prop a (by omega)))
  right_inv e := Finsupp.subtypeDomain_extendDomain e

theorem tailIdxEquivFinsupp_zero : tailIdxEquivFinsupp N 0 = 0 := by
  show Finsupp.subtypeDomain (fun n => N < n) (0 : TailIdx N).1 = 0
  rw [TailIdx.zero_val]
  exact Finsupp.subtypeDomain_zero

theorem tailIdxEquivFinsupp_symm_zero : (tailIdxEquivFinsupp N).symm 0 = 0 := by
  rw [← tailIdxEquivFinsupp_zero, Equiv.symm_apply_apply]

theorem tailIdxEquivFinsupp_add (μ ν : TailIdx N) :
    tailIdxEquivFinsupp N (μ + ν) =
      tailIdxEquivFinsupp N μ + tailIdxEquivFinsupp N ν := by
  show Finsupp.subtypeDomain (fun n => N < n) (μ + ν).1 = _
  rw [TailIdx.add_val]
  exact Finsupp.subtypeDomain_add

theorem tailIdxEquivFinsupp_symm_add (e e' : TailVar N →₀ ℕ) :
    (tailIdxEquivFinsupp N).symm (e + e') =
      (tailIdxEquivFinsupp N).symm e + (tailIdxEquivFinsupp N).symm e' := by
  apply (tailIdxEquivFinsupp N).injective
  rw [Equiv.apply_symm_apply, tailIdxEquivFinsupp_add, Equiv.apply_symm_apply,
    Equiv.apply_symm_apply]

variable {P : Type*} [NormedCommRing P] [IsUltrametricDist P]

noncomputable def tailC0ToFormalFun (w : ℕ → ℕ) (N : ℕ) (ρ : TwistElem P)
    (x : TailC0 w N P ρ) : MvPowerSeries (TailVar N) P :=
  fun e => ρ.val ^ wpWeight w ((tailIdxEquivFinsupp N).symm e).1 *
    x.1 ((tailIdxEquivFinsupp N).symm e)

theorem coeff_tailC0ToFormalFun (w : ℕ → ℕ) (N : ℕ) (ρ : TwistElem P)
    (x : TailC0 w N P ρ) (e : TailVar N →₀ ℕ) :
    MvPowerSeries.coeff e (tailC0ToFormalFun w N ρ x) =
      ρ.val ^ wpWeight w ((tailIdxEquivFinsupp N).symm e).1 *
        x.1 ((tailIdxEquivFinsupp N).symm e) := rfl

theorem tailC0ToFormalFun_zero (w : ℕ → ℕ) (N : ℕ) (ρ : TwistElem P) :
    tailC0ToFormalFun w N ρ 0 = 0 := by
  refine MvPowerSeries.ext fun e => ?_
  rw [coeff_tailC0ToFormalFun,
    show ((0 : TailC0 w N P ρ)).1 ((tailIdxEquivFinsupp N).symm e) = 0 from rfl,
    mul_zero]
  simp

theorem tailC0ToFormalFun_one (w : ℕ → ℕ) (N : ℕ) (ρ : TwistElem P) :
    tailC0ToFormalFun w N ρ 1 = 1 := by
  classical
  refine MvPowerSeries.ext fun e => ?_
  rw [coeff_tailC0ToFormalFun, TailC0.one_val, MvPowerSeries.coeff_one]
  by_cases he : e = 0
  · subst he
    rw [if_pos (tailIdxEquivFinsupp_symm_zero N), if_pos rfl,
      tailIdxEquivFinsupp_symm_zero, TailIdx.zero_val, wpWeight_zero, pow_zero,
      one_mul]
  · rw [if_neg (fun h => he ((Equiv.apply_symm_apply (tailIdxEquivFinsupp N)
        e).symm.trans (by rw [h, tailIdxEquivFinsupp_zero]))),
      if_neg he, mul_zero]

theorem tailC0ToFormalFun_add (w : ℕ → ℕ) (N : ℕ) (ρ : TwistElem P)
    (x y : TailC0 w N P ρ) :
    tailC0ToFormalFun w N ρ (x + y) =
      tailC0ToFormalFun w N ρ x + tailC0ToFormalFun w N ρ y := by
  refine MvPowerSeries.ext fun e => ?_
  rw [map_add, coeff_tailC0ToFormalFun, coeff_tailC0ToFormalFun,
    coeff_tailC0ToFormalFun,
    show ((x + y) : TailC0 w N P ρ).1 ((tailIdxEquivFinsupp N).symm e) =
      x.1 ((tailIdxEquivFinsupp N).symm e) + y.1 ((tailIdxEquivFinsupp N).symm e)
      from rfl, mul_add]

theorem tailC0ToFormalFun_mul (w : ℕ → ℕ) (N : ℕ) (ρ : TwistElem P)
    (x y : TailC0 w N P ρ) :
    tailC0ToFormalFun w N ρ (x * y) =
      tailC0ToFormalFun w N ρ x * tailC0ToFormalFun w N ρ y := by
  classical
  refine MvPowerSeries.ext fun e => ?_
  rw [MvPowerSeries.coeff_mul, coeff_tailC0ToFormalFun, TailC0.mul_val,
    Finset.mul_sum]
  refine Finset.sum_nbij'
    (fun p => (tailIdxEquivFinsupp N p.1, tailIdxEquivFinsupp N p.2))
    (fun q => ((tailIdxEquivFinsupp N).symm q.1, (tailIdxEquivFinsupp N).symm q.2))
    ?_ ?_ ?_ ?_ ?_
  · rintro ⟨p₁, p₂⟩ hp
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp ⊢
    have hp' : p₁ + p₂ = (tailIdxEquivFinsupp N).symm e := hp
    rw [← tailIdxEquivFinsupp_add, hp']
    exact Equiv.apply_symm_apply _ e
  · rintro ⟨q₁, q₂⟩ hq
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hq ⊢
    rw [← tailIdxEquivFinsupp_symm_add, hq]
  · rintro ⟨p₁, p₂⟩ _
    rw [Prod.ext_iff]
    exact ⟨Equiv.symm_apply_apply _ _, Equiv.symm_apply_apply _ _⟩
  · rintro ⟨q₁, q₂⟩ _
    rw [Prod.ext_iff]
    exact ⟨Equiv.apply_symm_apply _ _, Equiv.apply_symm_apply _ _⟩
  · rintro ⟨p₁, p₂⟩ hp
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    rw [coeff_tailC0ToFormalFun, coeff_tailC0ToFormalFun,
      Equiv.symm_apply_apply, Equiv.symm_apply_apply]
    have hval : ((tailIdxEquivFinsupp N).symm e).1 = p₁.1 + p₂.1 := by
      rw [← hp, TailIdx.add_val]
    have hle : wpWeight w ((tailIdxEquivFinsupp N).symm e).1 ≤
        wpWeight w p₁.1 + wpWeight w p₂.1 := by
      rw [hval]
      exact wpWeight_add_le w p₁.1 p₂.1
    rw [show ρ.val ^ wpWeight w ((tailIdxEquivFinsupp N).symm e).1 *
        (ρ.val ^ (wpWeight w p₁.1 + wpWeight w p₂.1 -
          wpWeight w ((tailIdxEquivFinsupp N).symm e).1) * (x.1 p₁ * y.1 p₂)) =
      ρ.val ^ (wpWeight w ((tailIdxEquivFinsupp N).symm e).1 +
        (wpWeight w p₁.1 + wpWeight w p₂.1 -
          wpWeight w ((tailIdxEquivFinsupp N).symm e).1)) * (x.1 p₁ * y.1 p₂) by
        rw [pow_add]; ring,
      Nat.add_sub_cancel' hle, pow_add]
    ring

/-- **The formal-series embedding** `Φ : TailC0 → ℱ_J(P) = MvPowerSeries J P`,
`Φ(∑ x_μ e_μ) = ∑ ρ^{ω(μ)} x_μ U^μ` ([WP] eq:formal-embedding).  Multiplicative
because the `ρ`-powers absorb the twist (eq:tail-multiplication); it forgets the
topology (the target is the full formal product). -/
noncomputable def tailC0ToMvPowerSeries (w : ℕ → ℕ) (N : ℕ) (ρ : TwistElem P) :
    TailC0 w N P ρ →+* MvPowerSeries (TailVar N) P where
  toFun := tailC0ToFormalFun w N ρ
  map_one' := tailC0ToFormalFun_one w N ρ
  map_mul' := tailC0ToFormalFun_mul w N ρ
  map_zero' := tailC0ToFormalFun_zero w N ρ
  map_add' := tailC0ToFormalFun_add w N ρ

theorem coeff_tailC0ToMvPowerSeries (w : ℕ → ℕ) (N : ℕ) (ρ : TwistElem P)
    (x : TailC0 w N P ρ) (e : TailVar N →₀ ℕ) :
    MvPowerSeries.coeff e (tailC0ToMvPowerSeries w N ρ x) =
      ρ.val ^ wpWeight w ((tailIdxEquivFinsupp N).symm e).1 *
        x.1 ((tailIdxEquivFinsupp N).symm e) := rfl

/-- `Φ` is injective when the twist element is regular
([WP] thm:parity-rationally-reduced: "The `W`-regularity of `P` then gives
`x_μ = 0`"). -/
theorem tailC0ToMvPowerSeries_injective (ρ : TwistElem P)
    (hρ : ∀ x : P, ρ.val * x = 0 → x = 0) :
    Function.Injective (tailC0ToMvPowerSeries w N ρ) := by
  have hreg : ∀ (k : ℕ) (a : P), ρ.val ^ k * a = 0 → a = 0 := by
    intro k
    induction k with
    | zero => intro a ha; rwa [pow_zero, one_mul] at ha
    | succ n ih =>
      intro a ha
      exact hρ a (ih (ρ.val * a) (by rwa [pow_succ, mul_assoc] at ha))
  rw [injective_iff_map_eq_zero]
  intro x hx
  refine Subtype.ext (funext fun μ => ?_)
  have he := congrArg (MvPowerSeries.coeff (tailIdxEquivFinsupp N μ)) hx
  rw [coeff_tailC0ToMvPowerSeries, Equiv.symm_apply_apply, map_zero] at he
  show x.1 μ = (0 : P)
  exact hreg _ _ he

/-- Reducedness descends through `Φ` ([WP] thm:parity-rationally-reduced, final
step; with `WP/Reduced.lean`'s `IsReduced (MvPowerSeries J P)`). -/
theorem isReduced_tailC0 (ρ : TwistElem P) [IsReduced P]
    (hρ : ∀ x : P, ρ.val * x = 0 → x = 0) :
    IsReduced (TailC0 w N P ρ) := by
  haveI : IsReduced (MvPowerSeries (TailVar N) P) := isReduced_mvPowerSeries _ _
  exact isReduced_of_injective (tailC0ToMvPowerSeries w N ρ)
    (tailC0ToMvPowerSeries_injective w N ρ hρ)

/-- Domain-ness descends through `Φ` (used for the bad chart ℬ,
[WP] prop:weighted-chart-domain-nonuniform; with mathlib's
`NoZeroDivisors (MvPowerSeries σ R)`). -/
theorem isDomain_tailC0 (ρ : TwistElem P) [IsDomain P]
    (hρ : ∀ x : P, ρ.val * x = 0 → x = 0) :
    IsDomain (TailC0 w N P ρ) := by
  haveI : Nontrivial (MvPowerSeries (TailVar N) P) :=
    ⟨⟨0, 1, fun h => by
      have h0 := congrArg (MvPowerSeries.coeff (0 : TailVar N →₀ ℕ)) h
      rw [map_zero, MvPowerSeries.coeff_zero_one] at h0
      exact zero_ne_one h0⟩⟩
  haveI : IsDomain (MvPowerSeries (TailVar N) P) := NoZeroDivisors.to_isDomain _
  exact Function.Injective.isDomain (tailC0ToMvPowerSeries w N ρ)
    (tailC0ToMvPowerSeries_injective w N ρ hρ)

end WeightedParity
