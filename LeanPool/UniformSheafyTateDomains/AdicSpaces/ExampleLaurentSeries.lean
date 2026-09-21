/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.RingTheory.LaurentSeries
import Mathlib.RingTheory.Valuation.Integral
import Mathlib.RingTheory.PowerSeries.Ideal
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Topology.Algebra.Valued.WithZeroMulInt
import LeanPool.UniformSheafyTateDomains.AdicSpaces.RestrictedPowerSeries
import LeanPool.UniformSheafyTateDomains.AdicSpaces.HuberRings
import LeanPool.UniformSheafyTateDomains.AdicSpaces.AffinoidRings
import LeanPool.UniformSheafyTateDomains.AdicSpaces.WedhornCechAcyclicity

/-!
# A non-trivial instance of Theorem 8.28(b): the Laurent series field `F⸨X⸩`

For any field `F`, the Laurent series field `K := F⸨X⸩` with its `X`-adic (valued)
topology is a **complete, strongly noetherian Tate ring**, and `(K, 𝒪)` with
`𝒪 := Valued.v.integer = F⟦X⟧` is an affinoid ring in Wedhorn's sense (Def 7.14).
Hence `IsSheafy K` by `isSheafy_of_stronglyNoetherian_828b` — witnessing that the
headline theorem's hypotheses are satisfiable by a genuinely topologized
(non-discrete) example.

* **Tate**: `X` is a topologically nilpotent unit (`valuation_X_pow` decays).
* **Pair of definition**: `(𝒪, (X))`, with the `X`-adic subspace topology
  (`Valuation.Integers.dvd_iff_le` converts balls to ideal powers).
* **Strongly noetherian** (the crux — no Weierstrass theory needed in equal
  characteristic): restricted power series over `K` in `k` variables with integral
  coefficients are exactly power series in `X` with `MvPolynomial (Fin k) F`
  coefficients, via the *transpose* ring homomorphism
  `τ : (MvPolynomial (Fin k) F)⟦X⟧ →+* MvPowerSeries (Fin k) F⟦X⟧` (restrictedness of
  the image ⟺ polynomiality of the `X`-layers). `(MvPolynomial (Fin k) F)⟦X⟧` is
  noetherian (Hilbert basis + power series), and the full restricted ring is reached
  from the integral part by inverting the unit `X`, so every ideal is finitely
  generated.
* **Complete**: mathlib's `instLaurentSeriesComplete`, transported to the canonical
  right uniformity via `IsUniformAddGroup.rightUniformSpace_eq`.
-/

noncomputable section

open scoped LaurentSeries PowerSeries
open WithZero ValuationSpectrum Filter

namespace LaurentSeriesExample

variable (F : Type*) [Field F]

local notation "K" => LaurentSeries F

/-! ### The valuation, the integer ring, and basic estimates -/

/-- The image of the Laurent variable in `K`. -/
def t : K := ((PowerSeries.X : F⟦X⟧) : K)

theorem valuation_t_pow (n : ℕ) : Valued.v ((t F) ^ n) = exp (-(n : ℤ)) :=
  LaurentSeries.valuation_X_pow F n

theorem valuation_t : Valued.v (t F) = exp (-(1 : ℤ)) := by
  simpa using valuation_t_pow F 1

theorem t_ne_zero : t F ≠ 0 := by
  intro h
  have h2 := valuation_t F
  rw [h, map_zero] at h2
  exact exp_pos.ne' h2.symm

theorem isUnit_t : IsUnit (t F) := (t_ne_zero F).isUnit

/-- Powers of `exp (-1)` are cofinal below any nonzero `γ` in `ℤᵐ⁰`. -/
theorem exists_exp_neg_lt (γ : ℤᵐ⁰) (hγ : γ ≠ 0) : ∃ n : ℕ, exp (-(n : ℤ)) < γ := by
  refine ⟨(1 - log γ).toNat, ?_⟩
  rw [← lt_log_iff_exp_lt hγ]
  omega

/-- The strict ball of radius `exp (-n)` around `x` is a neighborhood of `x`. -/
theorem ball_mem_nhds (x : K) (n : ℕ) :
    {y : K | Valued.v (y - x) < exp (-(n : ℤ))} ∈ nhds x := by
  have htn : Valued.v.restrict ((t F) ^ n) ≠ 0 := by
    rw [ne_eq, Valuation.restrict_eq_zero_iff, valuation_t_pow]
    exact exp_pos.ne'
  rw [Valued.mem_nhds]
  refine ⟨Units.mk0 _ htn, fun y hy => ?_⟩
  rw [Set.mem_setOf_eq, Units.val_mk0, Valuation.restrict_lt_iff] at hy
  rw [Set.mem_setOf_eq, ← valuation_t_pow F n]
  exact hy

/-- Neighborhoods of `x` in `K` are exactly supersets of the `exp (-n)`-balls. -/
theorem mem_nhds_iff_ball {x : K} {s : Set K} :
    s ∈ nhds x ↔ ∃ n : ℕ, {y : K | Valued.v (y - x) < exp (-(n : ℤ))} ⊆ s := by
  constructor
  · intro hs
    obtain ⟨γ, hγ⟩ := Valued.mem_nhds.mp hs
    obtain ⟨n, hn⟩ := exists_exp_neg_lt (MonoidWithZeroHom.ValueGroup₀.embedding γ.1)
      (MonoidWithZeroHom.ValueGroup₀.embedding_unit_ne_zero γ)
    refine ⟨n, fun y hy => hγ ?_⟩
    rw [Set.mem_setOf_eq] at hy ⊢
    rw [Valuation.restrict_lt_iff_lt_embedding]
    exact lt_trans hy hn
  · rintro ⟨n, hn⟩
    exact Filter.mem_of_superset (ball_mem_nhds F x n) hn

/-- `t` is topologically nilpotent in `K`. -/
theorem isTopologicallyNilpotent_t : IsTopologicallyNilpotent (t F) :=
  Valued.tendsto_zero_pow_of_le_exp_neg_one (le_of_eq (valuation_t F))

/-- The integer subring `𝒪 = {v ≤ 1} = F⟦X⟧`. -/
abbrev O : Subring K := (Valued.v).integer

theorem mem_O_iff (x : K) : x ∈ O F ↔ Valued.v x ≤ 1 := Iff.rfl

theorem t_mem_O : t F ∈ O F := by
  rw [mem_O_iff, valuation_t, ← exp_zero, exp_le_exp]
  omega

/-- The closed unit ball `𝒪` is open (nonarchimedean triangle inequality). -/
theorem isOpen_O : IsOpen ((O F : Set K)) := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  rw [mem_nhds_iff_ball]
  refine ⟨0, fun y hy => ?_⟩
  rw [Set.mem_setOf_eq] at hy
  have hyx : y = (y - x) + x := by ring
  rw [SetLike.mem_coe, mem_O_iff, hyx]
  refine le_trans (Valuation.map_add _ _ _) (max_le (le_of_lt ?_) hx)
  simpa using hy

/-- `t` as an element of `𝒪`. -/
def t₀ : O F := ⟨t F, t_mem_O F⟩

/-- Divisibility in `𝒪` is valuation comparison (`v.integer` is a valuation ring). -/
theorem t₀_pow_dvd_iff (n : ℕ) (x : O F) :
    (t₀ F) ^ n ∣ x ↔ Valued.v ((x : K)) ≤ Valued.v ((t F) ^ n) := by
  have hcoe : ((((t₀ F) ^ n : O F)) : K) = (t F) ^ n := by push_cast; rfl
  have halg : ∀ y : O F, (algebraMap (↥(O F)) K) y = (y : K) := fun _ => rfl
  rw [Valuation.Integers.dvd_iff_le (Valuation.integer.integers _), halg, halg, hcoe]

/-- Membership in `(t)ⁿ ⊆ 𝒪` is the valuation bound `v ≤ v(tⁿ)`. -/
theorem mem_span_t₀_pow_iff (n : ℕ) (x : O F) :
    x ∈ (Ideal.span {t₀ F} ^ n : Ideal (O F)) ↔
      Valued.v ((x : K)) ≤ Valued.v ((t F) ^ n) := by
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton, t₀_pow_dvd_iff]

/-! ### The pair of definition and the Huber/Tate instances -/

/-- The pair of definition `(𝒪, (t))` for `K`. -/
def pod : PairOfDefinition K where
  A₀ := O F
  I := Ideal.span {t₀ F}
  isOpen := isOpen_O F
  fg := ⟨{t₀ F}, by simp⟩
  isAdic := by
    rw [isAdic_iff]
    refine ⟨fun n => ?_, fun s hs => ?_⟩
    · -- `(t)ⁿ` is open in `𝒪`: around each point the strict `exp (-n)`-ball stays inside.
      rw [isOpen_iff_mem_nhds]
      intro x hx
      rw [SetLike.mem_coe, mem_span_t₀_pow_iff, valuation_t_pow] at hx
      rw [mem_nhds_subtype]
      refine ⟨{y : K | Valued.v (y - (x : K)) < exp (-(n : ℤ))},
        ball_mem_nhds F (x : K) n, ?_⟩
      intro y hy
      rw [Set.mem_preimage, Set.mem_setOf_eq] at hy
      rw [SetLike.mem_coe, mem_span_t₀_pow_iff, valuation_t_pow]
      have hdecomp : ((y : K)) = (((y : K)) - ((x : K))) + ((x : K)) := by ring
      rw [hdecomp]
      exact le_trans (Valuation.map_add _ _ _) (max_le (le_of_lt hy) hx)
    · -- the `(t)ⁿ` shrink below any neighborhood of `0`.
      rw [mem_nhds_subtype] at hs
      obtain ⟨U, hU, hUs⟩ := hs
      obtain ⟨n, hn⟩ := (mem_nhds_iff_ball F).mp (by simpa using hU)
      refine ⟨n + 1, fun x hx => hUs ?_⟩
      rw [SetLike.mem_coe, mem_span_t₀_pow_iff, valuation_t_pow] at hx
      rw [Set.mem_preimage]
      refine hn ?_
      rw [Set.mem_setOf_eq, sub_zero]
      refine lt_of_le_of_lt hx ?_
      rw [exp_lt_exp]
      omega

instance : IsHuberRing K := ⟨⟨pod F⟩⟩

instance : IsTateRing K :=
  ⟨⟨(isUnit_t F).unit, by simpa using isTopologicallyNilpotent_t F⟩⟩

/-! ### `(K, 𝒪)` is an affinoid ring (Wedhorn Def 7.14) -/

/-- `𝒪` is integrally closed in `K` (`Valuation.Integers.mem_of_integral`). -/
theorem O_isIntegrallyClosed (a : K) (ha : IsIntegral (O F) a) : a ∈ O F :=
  Valuation.Integers.mem_of_integral (Valuation.integer.integers _) ha

/-- The closed unit ball is a bounded subset of `K` (`v(s·y) ≤ v(y)` for `s ∈ 𝒪`). -/
theorem isBounded_O : TopologicalRing.IsBounded ((O F : Subring K) : Set K) := by
  intro U hU
  obtain ⟨n, hn⟩ := (mem_nhds_iff_ball F).mp hU
  refine ⟨{y : K | Valued.v (y - 0) < exp (-(n : ℤ))},
    by simpa using ball_mem_nhds F 0 n, ?_⟩
  rintro z ⟨s, hs, y, hy, rfl⟩
  refine hn ?_
  rw [Set.mem_setOf_eq, sub_zero] at hy ⊢
  rw [Valuation.map_mul]
  calc Valued.v s * Valued.v y ≤ 1 * Valued.v y := by
        gcongr
        exact hs
    _ = Valued.v y := one_mul _
    _ < exp (-(n : ℤ)) := hy

/-- The power-bounded subring of `K` contains `𝒪` (in fact equals it). -/
theorem O_subset_powerBounded :
    ((O F : Subring K) : Set K) ⊆ TopologicalRing.powerBoundedSubring K := by
  intro x hx
  refine (isBounded_O F).subset ?_
  rintro - ⟨k, rfl⟩
  rw [SetLike.mem_coe, mem_O_iff, map_pow]
  exact pow_le_one₀ zero_le' hx

instance : ValuationSpectrum.PlusSubring K := ⟨O F⟩

instance : IsRingOfIntegralElements ((ValuationSpectrum.ringPlus K : Subring K)) where
  isOpen := isOpen_O F
  isIntegrallyClosed := O_isIntegrallyClosed F
  subset_powerBounded := O_subset_powerBounded F

/-! ### Completeness -/

instance : @CompleteSpace K (IsTopologicalAddGroup.rightUniformSpace K) := by
  rw [IsUniformAddGroup.rightUniformSpace_eq]
  infer_instance

/-! ### Strongly noetherian (the layer transpose) -/

section StronglyNoetherianProof

variable (k : ℕ)

/-- The transpose, as a raw function. -/
def tauFun (g : PowerSeries (MvPolynomial (Fin k) F)) :
    MvPowerSeries (Fin k) F⟦X⟧ :=
  fun s => PowerSeries.mk fun m => MvPolynomial.coeff s (PowerSeries.coeff m g)

theorem coeff_tauFun (g : PowerSeries (MvPolynomial (Fin k) F)) (s : Fin k →₀ ℕ) (m : ℕ) :
    PowerSeries.coeff m (MvPowerSeries.coeff s (tauFun F k g)) =
      MvPolynomial.coeff s (PowerSeries.coeff m g) := by
  -- v4.33: unfolding `tauFun` into the goal by `rw [show … from rfl]` leaves a bare lambda
  -- at the (defeq-only-at-default) `MvPowerSeries` carrier, which `kabstract` rejects on
  -- the follow-up rewrites; `change` to the (well-typed) `PowerSeries.mk` form instead.
  change PowerSeries.coeff m (PowerSeries.mk fun n =>
    MvPolynomial.coeff s (PowerSeries.coeff n g)) = _
  exact PowerSeries.coeff_mk m _

/-- The **transpose** ring homomorphism: a power series in `X` whose coefficients are
`k`-variable polynomials becomes a `k`-variable power series whose coefficients are
power series in `X` (swap the two gradings). -/
def tau : PowerSeries (MvPolynomial (Fin k) F) →+* MvPowerSeries (Fin k) F⟦X⟧ where
  toFun := tauFun F k
  map_zero' := by
    refine MvPowerSeries.ext fun s => ?_
    refine PowerSeries.ext fun m => ?_
    rw [coeff_tauFun]
    simp
  map_one' := by
    refine MvPowerSeries.ext fun s => ?_
    refine PowerSeries.ext fun m => ?_
    rw [coeff_tauFun, PowerSeries.coeff_one, MvPowerSeries.coeff_one]
    by_cases hm : m = 0 <;> by_cases hs : s = 0 <;>
      simp [hm, hs, MvPolynomial.coeff_one, PowerSeries.coeff_one, eq_comm]
  map_add' g h := by
    refine MvPowerSeries.ext fun s => ?_
    refine PowerSeries.ext fun m => ?_
    simp [coeff_tauFun]
  map_mul' g h := by
    refine MvPowerSeries.ext fun s => ?_
    refine PowerSeries.ext fun m => ?_
    rw [coeff_tauFun, PowerSeries.coeff_mul, MvPolynomial.coeff_sum,
      MvPowerSeries.coeff_mul, map_sum]
    simp only [MvPolynomial.coeff_mul, PowerSeries.coeff_mul, coeff_tauFun]
    rw [Finset.sum_comm]

theorem coeff_tau (g : PowerSeries (MvPolynomial (Fin k) F)) (s : Fin k →₀ ℕ) (m : ℕ) :
    PowerSeries.coeff m (MvPowerSeries.coeff s (tau F k g)) =
      MvPolynomial.coeff s (PowerSeries.coeff m g) :=
  coeff_tauFun F k g s m

/-- The transpose landed in `K`-coefficients. -/
def Psi : PowerSeries (MvPolynomial (Fin k) F) →+* MvPowerSeries (Fin k) K :=
  (MvPowerSeries.map (HahnSeries.ofPowerSeries ℤ F : F⟦X⟧ →+* K)).comp (tau F k)

theorem coeff_Psi (g : PowerSeries (MvPolynomial (Fin k) F)) (s : Fin k →₀ ℕ) :
    MvPowerSeries.coeff s (Psi F k g) =
      ((MvPowerSeries.coeff s (tau F k g) : F⟦X⟧) : K) := by
  rw [Psi, RingHom.comp_apply, MvPowerSeries.coeff_map]

/-- Valuation bound from vanishing low layers. -/
theorem psi_coeff_v_le (g : PowerSeries (MvPolynomial (Fin k) F)) (s : Fin k →₀ ℕ) (n : ℕ)
    (h : ∀ m < n, MvPolynomial.coeff s (PowerSeries.coeff m g) = 0) :
    Valued.v (MvPowerSeries.coeff s (Psi F k g)) ≤ exp (-(n : ℤ)) := by
  rw [coeff_Psi, LaurentSeries.intValuation_le_iff_coeff_lt_eq_zero]
  intro m hm
  rw [coeff_tau]
  exact h m hm

/-- The transpose image is a restricted power series (its `X`-layers are polynomials). -/
theorem psi_mem_restricted (g : PowerSeries (MvPolynomial (Fin k) F)) :
    Psi F k g ∈ restrictedMvPowerSeriesSubring k K := by
  show MvPowerSeries.IsRestricted _
  refine Filter.tendsto_def.mpr fun U hU => ?_
  obtain ⟨n, hn⟩ := (mem_nhds_iff_ball F).mp hU
  rw [Filter.mem_cofinite]
  refine Set.Finite.subset
    (((Finset.range (n + 1)).biUnion fun m =>
      (PowerSeries.coeff m g).support).finite_toSet) ?_
  intro s hs
  rw [Set.mem_compl_iff, Set.mem_preimage] at hs
  by_contra hs0
  refine hs (hn ?_)
  rw [Set.mem_setOf_eq, sub_zero]
  refine lt_of_le_of_lt (psi_coeff_v_le F k g s (n + 1) fun m hm => ?_) ?_
  · by_contra hc
    exact hs0 (Finset.mem_coe.mpr (Finset.mem_biUnion.mpr
      ⟨m, Finset.mem_range.mpr hm, MvPolynomial.mem_support_iff.mpr hc⟩))
  · rw [exp_lt_exp]
    omega

/-- **Surjectivity onto the integral part**: every restricted power series over `K` with
integral coefficients is a transpose image. -/
theorem exists_psi_eq (f : MvPowerSeries (Fin k) K)
    (hres : MvPowerSeries.IsRestricted f)
    (hint : ∀ s, Valued.v (MvPowerSeries.coeff s f) ≤ 1) :
    ∃ g, Psi F k g = f := by
  classical
  have hPs : ∀ s, ∃ P : F⟦X⟧, ((P : F⟦X⟧) : K) = MvPowerSeries.coeff s f := fun s => by
    obtain ⟨Q, hQ⟩ :=
      (LaurentSeries.val_le_one_iff_eq_coe F (MvPowerSeries.coeff s f)).mp (hint s)
    exact ⟨Q, hQ⟩
  choose P hP using hPs
  -- each `X`-layer has finite support (restrictedness below radius `exp (-(m+1))`)
  have hlayer : ∀ m : ℕ, {s : Fin k →₀ ℕ | PowerSeries.coeff m (P s) ≠ 0}.Finite := by
    intro m
    have hball := Filter.tendsto_def.mp hres _
      (ball_mem_nhds F (0 : K) (m + 1))
    rw [Filter.mem_cofinite] at hball
    refine hball.subset fun s hs => ?_
    rw [Set.mem_compl_iff, Set.mem_preimage, Set.mem_setOf_eq, sub_zero]
    intro hlt
    refine hs (LaurentSeries.coeff_zero_of_lt_intValuation F (n := m) (d := m + 1)
      ?_ (by omega))
    rw [hP s]
    exact le_of_lt hlt
  set g : PowerSeries (MvPolynomial (Fin k) F) := PowerSeries.mk fun m =>
    ∑ s ∈ (hlayer m).toFinset,
      MvPolynomial.monomial s (PowerSeries.coeff m (P s)) with hg_def
  refine ⟨g, ?_⟩
  refine MvPowerSeries.ext fun s => ?_
  rw [coeff_Psi, ← hP s]
  congr 1
  refine PowerSeries.ext fun m => ?_
  rw [coeff_tau, hg_def, PowerSeries.coeff_mk, MvPolynomial.coeff_sum]
  by_cases hs : s ∈ (hlayer m).toFinset
  · rw [Finset.sum_eq_single s (fun b _ hb => by
      rw [MvPolynomial.coeff_monomial, if_neg hb]) (fun h => absurd hs h)]
    rw [MvPolynomial.coeff_monomial, if_pos rfl]
  · rw [Finset.sum_eq_zero fun b hb => ?_, eq_comm]
    · rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_not] at hs
      exact hs
    · rw [MvPolynomial.coeff_monomial, if_neg]
      intro hbs
      exact hs (hbs ▸ hb)

/-- The constant `t` inside the restricted subring, as a unit. -/
theorem c_t_mem_restricted (a : K) :
    MvPowerSeries.C (σ := Fin k) a ∈ restrictedMvPowerSeriesSubring k K := by
  classical
  show MvPowerSeries.IsRestricted _
  refine Filter.tendsto_def.mpr fun U hU => ?_
  rw [Filter.mem_cofinite]
  refine Set.Finite.subset (Set.finite_singleton (0 : Fin k →₀ ℕ)) ?_
  intro s hs
  rw [Set.mem_compl_iff, Set.mem_preimage] at hs
  rw [Set.mem_singleton_iff]
  by_contra hs0
  refine hs ?_
  rw [MvPowerSeries.coeff_C, if_neg hs0]
  exact mem_of_mem_nhds hU

/-- Uniform integralization: some `tⁿ` multiple of a restricted series has all
coefficients integral. -/
theorem exists_t_pow_mul_integral (f : MvPowerSeries (Fin k) K)
    (hres : MvPowerSeries.IsRestricted f) :
    ∃ n : ℕ, ∀ s, Valued.v ((t F) ^ n * MvPowerSeries.coeff s f) ≤ 1 := by
  classical
  have hball := Filter.tendsto_def.mp hres _ (ball_mem_nhds F (0 : K) 0)
  rw [Filter.mem_cofinite] at hball
  set S₀ := hball.toFinset with hS₀
  refine ⟨S₀.sup fun s => (log (Valued.v (MvPowerSeries.coeff s f))).toNat, fun s => ?_⟩
  rw [Valuation.map_mul, valuation_t_pow]
  by_cases hs : s ∈ S₀
  · -- exceptional coefficient: absorb its size into the sup
    have hle : Valued.v (MvPowerSeries.coeff s f) ≤
        exp ((S₀.sup fun s => (log (Valued.v (MvPowerSeries.coeff s f))).toNat : ℕ) : ℤ) := by
      refine le_trans le_exp_log ?_
      rw [exp_le_exp]
      have := Finset.le_sup (f := fun s => (log (Valued.v (MvPowerSeries.coeff s f))).toNat) hs
      omega
    calc exp (-((S₀.sup fun s => (log (Valued.v (MvPowerSeries.coeff s f))).toNat : ℕ) : ℤ)) *
          Valued.v (MvPowerSeries.coeff s f)
        ≤ exp (-((S₀.sup fun s => (log (Valued.v (MvPowerSeries.coeff s f))).toNat : ℕ) : ℤ)) *
          exp ((S₀.sup fun s => (log (Valued.v (MvPowerSeries.coeff s f))).toNat : ℕ) : ℤ) := by
          gcongr
      _ = exp 0 := by rw [← exp_add]; ring_nf
      _ = 1 := exp_zero
  · -- generic coefficient: already strictly inside the unit ball
    have hlt : Valued.v (MvPowerSeries.coeff s f) < 1 := by
      have := fun h => hs (Set.Finite.mem_toFinset _ |>.mpr h)
      by_contra hge
      push_neg at hge
      refine this ?_
      rw [Set.mem_compl_iff, Set.mem_preimage, Set.mem_setOf_eq, sub_zero]
      intro hlt1
      have h1 : (exp (-(0 : ℕ) : ℤ) : ℤᵐ⁰) = 1 := by
        rw [show (-(0:ℕ) : ℤ) = 0 by omega, exp_zero]
      rw [h1] at hlt1
      exact absurd hge (not_le.mpr hlt1)
    calc exp (-((S₀.sup fun s => (log (Valued.v (MvPowerSeries.coeff s f))).toNat : ℕ) : ℤ)) *
          Valued.v (MvPowerSeries.coeff s f)
        ≤ 1 * Valued.v (MvPowerSeries.coeff s f) := by
          gcongr
          rw [← exp_zero, exp_le_exp]
          omega
      _ = Valued.v (MvPowerSeries.coeff s f) := one_mul _
      _ ≤ 1 := le_of_lt hlt

/-- The transpose corestricted to the restricted subring. -/
def psiR : PowerSeries (MvPolynomial (Fin k) F) →+*
    ↥(restrictedMvPowerSeriesSubring k K) :=
  RingHom.codRestrict (Psi F k) _ (psi_mem_restricted F k)

theorem psiR_val (g : PowerSeries (MvPolynomial (Fin k) F)) :
    ((psiR F k g : ↥(restrictedMvPowerSeriesSubring k K)) :
      MvPowerSeries (Fin k) K) = Psi F k g := rfl

/-- The constant `t` in the restricted subring. -/
def tC : ↥(restrictedMvPowerSeriesSubring k K) :=
  ⟨MvPowerSeries.C (t F), c_t_mem_restricted F k (t F)⟩

/-- The constant `t⁻¹` in the restricted subring. -/
def tCinv : ↥(restrictedMvPowerSeriesSubring k K) :=
  ⟨MvPowerSeries.C ((t F)⁻¹), c_t_mem_restricted F k ((t F)⁻¹)⟩

theorem tCinv_mul_tC : tCinv F k * tC F k = 1 := by
  refine Subtype.ext ?_
  show MvPowerSeries.C ((t F)⁻¹) * MvPowerSeries.C (t F) = 1
  rw [← map_mul, inv_mul_cancel₀ (t_ne_zero F), map_one]

theorem tC_pow_mul_val (n : ℕ) (x : ↥(restrictedMvPowerSeriesSubring k K)) :
    (((tC F k) ^ n * x : ↥(restrictedMvPowerSeriesSubring k K)) :
      MvPowerSeries (Fin k) K) =
      MvPowerSeries.C ((t F) ^ n) * (x : MvPowerSeries (Fin k) K) := by
  push_cast
  rw [show ((tC F k : ↥(restrictedMvPowerSeriesSubring k K)) :
    MvPowerSeries (Fin k) K) = MvPowerSeries.C (t F) from rfl, ← map_pow]

/-- **`F⸨X⸩` is strongly noetherian.** Every ideal of the restricted power series ring
pulls back to a finitely generated ideal of the noetherian
`(MvPolynomial (Fin k) F)⟦X⟧` along the transpose, and the generators recover the ideal
after clearing denominators by the unit `t`. -/
instance : IsStronglyNoetherian K := by
  constructor
  intro k
  classical
  rw [isNoetherianRing_iff_ideal_fg]
  intro J
  obtain ⟨G, hG⟩ := (isNoetherianRing_iff_ideal_fg
    (PowerSeries (MvPolynomial (Fin k) F))).mp inferInstance (J.comap (psiR F k))
  refine ⟨G.image (psiR F k), le_antisymm ?_ ?_⟩
  · rw [Ideal.span_le]
    rintro y hy
    rw [Finset.coe_image] at hy
    obtain ⟨g, hgG, rfl⟩ := hy
    have hg' : g ∈ J.comap (psiR F k) := by
      rw [← hG]
      exact Ideal.subset_span hgG
    exact Ideal.mem_comap.mp hg'
  · intro x hx
    obtain ⟨n, hn⟩ := exists_t_pow_mul_integral F k (x : MvPowerSeries (Fin k) K) x.2
    have hcoeff : ∀ s, Valued.v (MvPowerSeries.coeff s
        ((((tC F k) ^ n * x : ↥(restrictedMvPowerSeriesSubring k K))) :
          MvPowerSeries (Fin k) K)) ≤ 1 := by
      intro s
      rw [tC_pow_mul_val, MvPowerSeries.coeff_C_mul]
      exact hn s
    obtain ⟨g, hg⟩ := exists_psi_eq F k
      (((tC F k) ^ n * x : ↥(restrictedMvPowerSeriesSubring k K)) :
        MvPowerSeries (Fin k) K)
      ((tC F k) ^ n * x : ↥(restrictedMvPowerSeriesSubring k K)).2 hcoeff
    have hψg : psiR F k g = (tC F k) ^ n * x := Subtype.ext (by rw [psiR_val]; exact hg)
    have hgJ : g ∈ J.comap (psiR F k) := by
      rw [Ideal.mem_comap, hψg]
      exact Ideal.mul_mem_left _ _ hx
    have hmem : psiR F k g ∈ Ideal.span ((G.image (psiR F k) :
        Finset ↥(restrictedMvPowerSeriesSubring k K)) : Set _) := by
      rw [Finset.coe_image, ← Ideal.map_span, hG]
      exact Ideal.mem_map_of_mem (psiR F k) hgJ
    have hxeq : x = (tCinv F k) ^ n * psiR F k g := by
      rw [hψg, ← mul_assoc, ← mul_pow, tCinv_mul_tC, one_pow, one_mul]
    rw [hxeq]
    exact Ideal.mul_mem_left _ _ hmem

end StronglyNoetherianProof

/-! ### The payoff -/

/-- **The Laurent series field `(F⸨X⸩, F⟦X⟧)` is sheafy** — a genuinely topologized,
non-discrete instance of Wedhorn Theorem 8.28(b). -/
theorem isSheafy_laurentSeries : IsSheafy K :=
  isSheafy_of_stronglyNoetherian_828b

end LaurentSeriesExample
