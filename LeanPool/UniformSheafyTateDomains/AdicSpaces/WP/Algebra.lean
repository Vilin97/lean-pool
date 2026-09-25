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
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.WP.Weight
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.WP.RestrictedComplete
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.FJP.CDVFBase
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.FJP.FiniteJetRings

/-!
# The weighted-parity algebra `𝒜` ([WP] §6.1)

For a CDVF-style base `K` (the FJP-CDVF conventions: nontrivially normed ultrametric
complete field, uniformizers via `FiniteJetOver.Uniformizer`) and a weight `w : ℕ → ℕ`,
this file constructs the weighted-parity algebra as the **support subring**
(rem:formalization convention)

  `𝒜 = {∑_{(a,ν) ∈ S} c_{a,ν} W^a U^ν : c_{a,ν} → 0}`   ([WP] eq:parity-algebra)

inside the ambient radius-one restricted power-series ring `Amb K` over the variable
index `ℕ` (index `0` = `W`, index `n ≥ 1` = `U_n`), together with its instance stack
(complete normed commutative ring; Huber/Tate via the uniformizer scaling bundle,
following `FJP/Over/JetRings.lean`) and the coefficient / monomial API.

The paper's example is `w = id`; general `w` uniformly covers the Tate extensions
`𝒜⟨V_1,…,V_s⟩` (shifted weight, [WP] §6.5) — see `WP/Weight.lean`.
-/

@[expose] public section

@[expose] public section

namespace WeightedParity

open MvPowerSeries Filter FiniteJetOver

variable (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable (w : ℕ → ℕ)

/-- The ambient ring `K⟨W, U_1, U_2, …⟩`: radius-one restricted power series in
countably many variables ([WP] prop:parity-uniform-domain's "countable restricted Tate
algebra").  Index `0` is `W`; index `n ≥ 1` is `U_n`. -/
abbrev Amb : Type _ :=
  MvPowerSeries.Restricted K (fun _ : ℕ => (1 : ℝ))

/-- The weighted-parity support subring `𝒜 ⊂ K⟨W,U⟩` ([WP] eq:parity-algebra as a
support condition, per the rem:formalization support-subring convention): restricted
series whose coefficients are supported on the monoid `S`. -/
noncomputable def wpSupport : Subring (Amb K) where
  carrier := {f | ∀ t : ℕ →₀ ℕ, ¬ WPMem w t → MvPowerSeries.coeff t f.1 = 0}
  zero_mem' := fun t _ => by
    show MvPowerSeries.coeff t (0 : MvPowerSeries ℕ K) = 0
    simp
  one_mem' := fun t ht => by
    show MvPowerSeries.coeff t (1 : MvPowerSeries ℕ K) = 0
    classical
    rcases eq_or_ne t 0 with rfl | h0
    · exact absurd (wpMem_zero w) ht
    · rw [MvPowerSeries.coeff_one, if_neg h0]
  add_mem' := fun {f} {g} hf hg t ht => by
    show MvPowerSeries.coeff t (f.1 + g.1) = 0
    rw [map_add, hf t ht, hg t ht, add_zero]
  neg_mem' := fun {f} hf t ht => by
    show MvPowerSeries.coeff t (-f.1) = 0
    rw [map_neg, hf t ht, neg_zero]
  mul_mem' := fun {f} {g} hf hg t ht => by
    show MvPowerSeries.coeff t (f.1 * g.1) = 0
    classical
    rw [MvPowerSeries.coeff_mul]
    refine Finset.sum_eq_zero fun p hp => ?_
    have hpt : p.1 + p.2 = t := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
    subst hpt
    by_cases h1 : WPMem w p.1
    · by_cases h2 : WPMem w p.2
      · exact absurd (h1.add h2) ht
      · rw [hg p.2 h2, mul_zero]
    · rw [hf p.1 h1, zero_mul]

/-- The weighted-parity algebra `𝒜` ([WP] eq:parity-algebra), as the coerced support
subring — all normed-ring structure is inherited from the ambient via the mathlib
`SubringClass` instances (the `JetA` pattern, `FJP/Over/JetRings.lean:294`). -/
abbrev WPA : Type _ := ↥(wpSupport K w)

/-- The support subring is closed in the ambient (each membership condition is the
kernel of a continuous coefficient functional). -/
theorem isClosed_wpSupport : IsClosed ((wpSupport K w : Set (Amb K))) := by
  have h := isClosed_setOf_coeff_eq_zero (R := K) (σ := ℕ) {t | WPMem w t}
  convert h using 1
  ext g
  exact Iff.rfl

instance : CompleteSpace (WPA K w) :=
  (isClosed_wpSupport K w).completeSpace_coe

instance : NormOneClass (WPA K w) :=
  ⟨by rw [show ‖(1 : WPA K w)‖ = ‖((1 : WPA K w) : Amb K)‖ from rfl]; exact norm_one⟩

/-! ### Coefficients and monomials -/

/-- The `t`-th coefficient of an element of `𝒜`. -/
noncomputable def coeffA (t : ℕ →₀ ℕ) (f : WPA K w) : K :=
  MvPowerSeries.coeff t f.1.1

@[simp] theorem coeffA_of_not_wpMem {t : ℕ →₀ ℕ} (ht : ¬ WPMem w t) (f : WPA K w) :
    coeffA K w t f = 0 :=
  f.2 t ht

theorem norm_coeffA_le (t : ℕ →₀ ℕ) (f : WPA K w) : ‖coeffA K w t f‖ ≤ ‖f‖ :=
  norm_coeff_le_one_norm f.1 t

theorem norm_eq_iSup_coeffA (f : WPA K w) :
    ‖f‖ = ⨆ t : ℕ →₀ ℕ, ‖coeffA K w t f‖ := by
  rw [show ‖f‖ = MvPowerSeries.gaussNorm (norm : K → ℝ) (fun _ : ℕ => (1 : ℝ)) f.1.1
      from rfl, MvPowerSeries.gaussNorm]
  exact iSup_congr fun t => by rw [prod_one_weights, mul_one]; rfl

theorem coeffA_injective :
    Function.Injective (fun f (t : ℕ →₀ ℕ) => coeffA K w t f) := fun f g h =>
  Subtype.ext (Subtype.ext (MvPowerSeries.ext fun t => congrFun h t))

/-- The monomial `c·W^{t 0}·U^{t'}` of `𝒜`, for an allowed exponent `t ∈ S`. -/
noncomputable def wpMonomial {t : ℕ →₀ ℕ} (ht : WPMem w t) (c : K) : WPA K w :=
  ⟨⟨MvPowerSeries.monomial t c, MvPowerSeries.isRestrictedGauss_monomial _ _ _⟩,
    fun s hs => by
      show MvPowerSeries.coeff s (MvPowerSeries.monomial t c) = 0
      classical
      rw [MvPowerSeries.coeff_monomial, if_neg (by intro h; subst h; exact hs ht)]⟩

@[simp] theorem coeffA_wpMonomial {t : ℕ →₀ ℕ} (ht : WPMem w t) (c : K) (s : ℕ →₀ ℕ) :
    coeffA K w s (wpMonomial K w ht c) = if s = t then c else 0 := by
  classical
  exact MvPowerSeries.coeff_monomial s t c

theorem norm_wpMonomial {t : ℕ →₀ ℕ} (ht : WPMem w t) (c : K) :
    ‖wpMonomial K w ht c‖ = ‖c‖ := by
  classical
  rw [norm_eq_iSup_coeffA]
  have hbdd : ∀ s : ℕ →₀ ℕ, ‖coeffA K w s (wpMonomial K w ht c)‖ ≤ ‖c‖ := fun s => by
    rw [coeffA_wpMonomial]
    split_ifs <;> simp
  apply le_antisymm (ciSup_le hbdd)
  have hle := le_ciSup (f := fun s : ℕ →₀ ℕ => ‖coeffA K w s (wpMonomial K w ht c)‖)
    ⟨‖c‖, Set.forall_mem_range.mpr hbdd⟩ t
  rwa [coeffA_wpMonomial, if_pos rfl] at hle

/-- The variable `W` ([WP] §6.1). -/
noncomputable def Wa : WPA K w := wpMonomial K w (wpMem_single_zero w 1) 1

/-- The allowed generator `Y_n = W^{w n} U_n` ([WP] eq:finite-stage-substitution at
general weight). -/
noncomputable def Ya (n : ℕ) : WPA K w := wpMonomial K w (wpMem_single_add_single w n) 1

/-- The even generator `Z_n = U_n²` ([WP] eq:finite-stage-substitution). -/
noncomputable def Za (n : ℕ) : WPA K w := wpMonomial K w (wpMem_two_nsmul_single w n 1) 1

/-! ### Scalars and the uniformizer bundle -/

/-- The constant embedding `K →+* 𝒜` (the `constA` pattern of
`FJP/Over/JetRings.lean:521`). -/
noncomputable def constA : K →+* WPA K w where
  toFun x :=
    ⟨⟨MvPowerSeries.C x, MvPowerSeries.isRestrictedGauss_C _ _⟩, fun s hs => by
      show MvPowerSeries.coeff s (MvPowerSeries.C (σ := ℕ) x) = 0
      classical
      rw [MvPowerSeries.coeff_C, if_neg (by
        intro h; subst h; exact hs (wpMem_zero w))]⟩
  map_one' := Subtype.ext (Subtype.ext (map_one (MvPowerSeries.C (σ := ℕ) (R := K))))
  map_mul' x y := Subtype.ext (Subtype.ext (map_mul (MvPowerSeries.C (σ := ℕ)) x y))
  map_zero' := Subtype.ext (Subtype.ext (map_zero (MvPowerSeries.C (σ := ℕ) (R := K))))
  map_add' x y := Subtype.ext (Subtype.ext (map_add (MvPowerSeries.C (σ := ℕ)) x y))

@[simp] theorem norm_constA (x : K) : ‖constA K w x‖ = ‖x‖ := by
  classical
  rw [norm_eq_iSup_coeffA]
  have hco : ∀ s : ℕ →₀ ℕ, coeffA K w s (constA K w x) = if s = 0 then x else 0 :=
    fun s => MvPowerSeries.coeff_C s x
  have hbdd : ∀ s : ℕ →₀ ℕ, ‖coeffA K w s (constA K w x)‖ ≤ ‖x‖ := fun s => by
    rw [hco]
    split_ifs <;> simp
  apply le_antisymm (ciSup_le hbdd)
  have hle := le_ciSup (f := fun s : ℕ →₀ ℕ => ‖coeffA K w s (constA K w x)‖)
    ⟨‖x‖, Set.forall_mem_range.mpr hbdd⟩ 0
  rwa [hco, if_pos rfl] at hle

/-- Constants scale the Gauss norm exactly (the `norm_constC_mul` pattern,
`FJP/Over/JetRings.lean:535`; coefficientwise from `norm_mul` of the field). -/
theorem norm_constA_mul (x : K) (f : WPA K w) :
    ‖constA K w x * f‖ = ‖x‖ * ‖f‖ := by
  classical
  rw [norm_eq_iSup_coeffA, norm_eq_iSup_coeffA]
  have hco : ∀ t : ℕ →₀ ℕ, coeffA K w t (constA K w x * f) = x * coeffA K w t f :=
    fun t => by
      show MvPowerSeries.coeff t (MvPowerSeries.C x * f.1.1) = _
      exact MvPowerSeries.coeff_C_mul t f.1.1 x
  have h1 : (⨆ t : ℕ →₀ ℕ, ‖coeffA K w t (constA K w x * f)‖) =
      ⨆ t : ℕ →₀ ℕ, ‖x‖ * ‖coeffA K w t f‖ :=
    iSup_congr fun t => by rw [hco, norm_mul]
  rw [h1, ← Real.mul_iSup_of_nonneg (norm_nonneg x)]

variable {K w} in
/-- The pseudouniformizer of `𝒜` attached to a uniformizer of `K`
(`piA` pattern, `FJP/Over/JetRings.lean:563`). -/
noncomputable def piW (ϖ : Uniformizer K) : WPA K w := constA K w ϖ.val

variable {K w} in
@[simp] theorem norm_piW (ϖ : Uniformizer K) : ‖piW (w := w) ϖ‖ = ‖ϖ.val‖ :=
  norm_constA K w ϖ.val

variable {K w} in
theorem norm_piW_lt_one (ϖ : Uniformizer K) : ‖piW (w := w) ϖ‖ < 1 := by
  rw [norm_piW]; exact ϖ.norm_val_lt_one

variable {K w} in
theorem norm_piW_pos (ϖ : Uniformizer K) : 0 < ‖piW (w := w) ϖ‖ := by
  rw [norm_piW]; exact ϖ.norm_val_pos

variable {K w} in
theorem isUnit_piW (ϖ : Uniformizer K) : IsUnit (piW (w := w) ϖ) :=
  ϖ.isUnit_val.map (constA K w)

variable {K w} in
theorem norm_piW_mul (ϖ : Uniformizer K) (f : WPA K w) :
    ‖piW ϖ * f‖ = ‖piW (w := w) ϖ‖ * ‖f‖ := by
  rw [norm_piW]
  exact norm_constA_mul K w ϖ.val f

variable {K w} in
/-- `𝒜` is a Huber ring (via the scaling bundle,
`FiniteJet.isHuberRing_of_scale`; the `isHuberRing_JetA` pattern,
`FJP/Over/JetRings.lean:656`). -/
theorem isHuberRing_WPA (ϖ : Uniformizer K) : IsHuberRing (WPA K w) :=
  FiniteJet.isHuberRing_of_scale (piW ϖ) (isUnit_piW ϖ) (norm_piW_lt_one ϖ)
    (norm_piW_pos ϖ) (norm_piW_mul ϖ)

variable {K w} in
/-- `𝒜` is a Tate ring ([WP] prop:parity-uniform-domain: "the Tate property follows
from (eq:parity-algebra) and the topologically nilpotent unit ϖ"). -/
theorem isTateRing_WPA (ϖ : Uniformizer K) : IsTateRing (WPA K w) :=
  FiniteJet.isTateRing_of_scale (piW ϖ) (isUnit_piW ϖ) (norm_piW_lt_one ϖ)
    (norm_piW_pos ϖ) (norm_piW_mul ϖ)

/-! ### The plus subring and completeness for the right uniformity
(the `JetA` instance block, `FJP/Over/JetRings.lean:711-755`) -/

/-- A norm-window scaling constant of the base field (inlined
`FiniteJetOver.exists_norm_window`, `FJP/Over/Functoriality.lean:94`). -/
theorem exists_norm_window' : ∃ c : K, IsUnit c ∧ ‖c‖ < 1 ∧ 0 < ‖c‖ := by
  obtain ⟨x, hx⟩ := NormedField.exists_one_lt_norm K
  have hx0 : x ≠ 0 := by
    intro h
    rw [h, norm_zero] at hx
    linarith
  exact ⟨x⁻¹, isUnit_iff_ne_zero.mpr (inv_ne_zero hx0),
    by rw [norm_inv]; exact inv_lt_one_of_one_lt₀ hx,
    by rw [norm_inv]; exact inv_pos.mpr (lt_trans one_pos hx)⟩

/-- Unconditional Huber instance via a norm-window element (the
`FJP/Over/Functoriality.lean:160` pattern — no uniformizer needed). -/
instance : IsHuberRing (WPA K w) := by
  obtain ⟨c, hcu, hc1, hc0⟩ := exists_norm_window' K
  exact FiniteJet.isHuberRing_of_scale (constA K w c) (hcu.map (constA K w))
    (by rw [norm_constA]; exact hc1) (by rw [norm_constA]; exact hc0)
    (fun f => by rw [norm_constA_mul, norm_constA])

instance : IsTateRing (WPA K w) := by
  obtain ⟨c, hcu, hc1, hc0⟩ := exists_norm_window' K
  exact FiniteJet.isTateRing_of_scale (constA K w c) (hcu.map (constA K w))
    (by rw [norm_constA]; exact hc1) (by rw [norm_constA]; exact hc0)
    (fun f => by rw [norm_constA_mul, norm_constA])

noncomputable instance : ValuationSpectrum.PlusSubring (WPA K w) :=
  ⟨TopologicalRing.powerBoundedSubring.toSubring (WPA K w)⟩

instance : ValuationSpectrum.IsRingOfIntegralElements
    ((ValuationSpectrum.ringPlus (WPA K w) : Subring (WPA K w))) :=
  FiniteJet.isRingOfIntegralElements_powerBounded

instance : IsUniformAddGroup (WPA K w) :=
  SeminormedAddCommGroup.to_isUniformAddGroup

instance : @CompleteSpace (WPA K w) (IsTopologicalAddGroup.rightUniformSpace (WPA K w)) := by
  rw [IsUniformAddGroup.rightUniformSpace_eq]
  infer_instance

/-! ### The unit ball ([WP] eq:parity-ring-of-definition) -/

/-- The ring of definition `𝒜₀` is the unit ball of the Gauss norm
([WP] eq:parity-ring-of-definition: coefficients in `k°`). -/
theorem mem_unitBall_iff_forall_coeffA (f : WPA K w) :
    f ∈ FiniteJet.unitBall (WPA K w) ↔ ∀ t, ‖coeffA K w t f‖ ≤ 1 := by
  rw [FiniteJet.mem_unitBall_iff]
  constructor
  · exact fun h t => (norm_coeffA_le K w t f).trans h
  · intro h
    rw [norm_eq_iSup_coeffA]
    exact ciSup_le h

end WeightedParity
