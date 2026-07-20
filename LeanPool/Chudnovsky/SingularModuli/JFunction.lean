/-
Copyright (c) 2026 Xuanji Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuanji Li
-/

import Mathlib.NumberTheory.ModularForms.Discriminant
import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.QExpansion
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import LeanPool.Chudnovsky.Ramanujan

/-!
# The `j`-function: definition, invariance, analyticity, q-expansion (Phase C, chunk B1)

This is the first file of Track 1 of Phase C (see `Playground/Pi/PhaseC-PLAN.md`, §3.1,
sub-lemma `(B1)`). It packages the elementary function-theoretic facts about the modular
`j`-invariant `j = 1728·J = E₄³/Δ` that the modular-polynomial pipeline
(`CosetOrbit.lean`, `ModularPolynomialQ.lean`, `CMRelations.lean`) consumes:

* `Chudnovsky.j` : the normalization `j τ = 1728 · J τ` (kept definitionally equal to the
  `1728 * J τ` that `SingularModuli.lean`'s pinned statements refer to);
* `j_eq`, `j_mul_discriminant` : the algebraic backbone `j = E₄³/Δ`, `j·Δ = E₄³`;
* modular invariance `j (γ • τ) = j τ` for `γ ∈ SL(2,ℤ)`, plus the `S`/`T` generator
  specializations;
* analyticity `MDifferentiable … j` on `ℍ` (from `E₄`, `E₆` holomorphic and `Δ ≠ 0`);
* integrality of the `E₄` and `E₄³` q-expansion coefficients (the ℤ-side building blocks
  of `(B1)`, feeding the ℤ-refinement of `ModularPolynomialZ.lean`);
* **the `(B1)` headline**: `j·q ∈ 1 + q·ℤ⟦q⟧`, delivered as
  - `Chudnovsky.jqInt : PowerSeries ℤ` with `constantCoeff_jqInt : constantCoeff jqInt = 1`,
  - `qExpansion_j_mul_q : qExpansion 1 (fun τ ↦ j τ * q τ) = jqInt.map (Int.castRingHom ℂ)`,
  - `hasSum_j_mul_q : HasSum (fun n ↦ (jqInt.coeff n : ℂ) * q τ ^ n) (j τ * q τ)` for every
    `τ : ℍ` (so `j = q⁻¹·(1 + 744q + …)` with integer coefficients — the pole-order-1
    structure at the cusp),
  together with the same package for `Δ` itself (`deltaInt`, `qExpansion_discriminant_int`,
  `deltaInt_coeff_zero/one`) which `CosetOrbit.lean`/`ModularPolynomialZ.lean` can reuse.

## Deviation from the plan's decision point 4

The plan recommends the η-product route (option (a)) for the ℤ-integrality of the `Δ`
q-expansion. Here we instead use option (b), the `1728`-congruence: Mathlib gives the exact
q-expansions of `E₄`, `E₆` with coefficients `240·σ₃(n)`, `-504·σ₅(n)`, and the coefficientwise
divisibility `1728 ∣ (E₄³ - E₆²)-coefficients` reduces (via `σ₅(n) ≡ σ₃(n) mod 24`, i.e.
`d⁵ ≡ d³ mod 24` for every `d`, a `decide` on `ZMod 24`) to finite arithmetic. Reason for the
deviation: option (a) needs "Taylor coefficients of a locally uniform limit of the partial
η-products", an analytic limit-interchange with no direct Mathlib support, while option (b) is
pure `PowerSeries ℤ` algebra glued to Mathlib's `qExpansion` API by `qExpansion_mul/sub/smul`
and `qExpansion_coeff_unique` — no analytic estimate at all. (The η-product still appears once,
harmlessly, in the *boundedness* of `j·q` at the cusp, via
`tendsto_atImInfty_tprod_one_sub_eta_q_pow`.)
-/

noncomputable section

namespace Chudnovsky

open UpperHalfPlane Complex ModularForm EisensteinSeries
open scoped Real ComplexOrder Manifold MatrixGroups

/-! ## Definition and the algebraic backbone `j = E₄³/Δ` -/

/-- The modular `j`-invariant in this project's normalization, `j = 1728·J = E₄³/Δ`.
Kept definitionally equal to the `1728 * J τ` appearing in `SingularModuli.lean`'s pinned
statements. -/
def j (τ : ℍ) : ℂ := 1728 * J τ

@[simp] lemma j_def (τ : ℍ) : j τ = 1728 * J τ := rfl

/-- `j = E₄³/Δ`. -/
lemma j_eq (τ : ℍ) : j τ = E₄ τ ^ 3 / discriminant τ := by
  rw [j_def, mul_J_eq]

/-- The algebraic backbone `j·Δ = E₄³`. -/
lemma j_mul_discriminant (τ : ℍ) : j τ * discriminant τ = E₄ τ ^ 3 := by
  rw [j_eq, div_mul_cancel₀ _ (discriminant_ne_zero τ)]

/-! ## Modular invariance -/

/-- The `SL(2,ℤ)` transformation law of a level-one modular form of weight `k`:
`f (γ • τ) = (denom γ τ)ᵏ · f τ`. (General `γ` version of `Ramanujan.modularForm_S_smul`.) -/
lemma modularForm_SL_smul {k : ℤ} (f : ModularForm 𝒮ℒ k) (γ : SL(2, ℤ)) (τ : ℍ) :
    f (γ • τ) = (denom γ τ) ^ k * f τ := by
  have h0 : (⇑f) ∣[k] γ = ⇑f :=
    f.slash_action_eq' _ (MonoidHom.mem_range.mpr ⟨γ, rfl⟩)
  have h := congr_fun h0 τ
  rw [SL_slash_apply, zpow_neg, ← div_eq_mul_inv,
    div_eq_iff (zpow_ne_zero k (denom_ne_zero γ τ))] at h
  rw [h, mul_comm]

/-- Klein's `J` is `SL(2,ℤ)`-invariant. -/
theorem J_smul (γ : SL(2, ℤ)) (τ : ℍ) : J (γ • τ) = J τ := by
  have hd : denom γ τ ≠ 0 := denom_ne_zero γ τ
  have hE₄ : E₄ (γ • τ) = denom γ τ ^ 4 * E₄ τ := by
    have h := modularForm_SL_smul E₄ γ τ
    rwa [zpow_ofNat] at h
  have hE₆ : E₆ (γ • τ) = denom γ τ ^ 6 * E₆ τ := by
    have h := modularForm_SL_smul E₆ γ τ
    rwa [zpow_ofNat] at h
  have h1 : (denom γ τ ^ 4 * E₄ τ) ^ 3 = denom γ τ ^ 12 * E₄ τ ^ 3 := by ring
  have h2 : (denom γ τ ^ 6 * E₆ τ) ^ 2 = denom γ τ ^ 12 * E₆ τ ^ 2 := by ring
  rw [J, J, hE₄, hE₆, h1, h2, ← mul_sub,
    mul_div_mul_left _ _ (pow_ne_zero 12 hd)]

/-- The `j`-invariant is `SL(2,ℤ)`-invariant: `j (γ • τ) = j τ`. -/
theorem j_smul (γ : SL(2, ℤ)) (τ : ℍ) : j (γ • τ) = j τ := by
  rw [j_def, j_def, J_smul]

/-- `T`-invariance: `j (τ + 1) = j τ`. -/
theorem j_vadd_one (τ : ℍ) : j ((1 : ℝ) +ᵥ τ) = j τ := by
  rw [j_def, j_def]
  congr 1
  rw [J, J]
  have hE₄ : E₄ ((1 : ℝ) +ᵥ τ) = E₄ τ :=
    SlashInvariantForm.vAdd_apply_of_mem_strictPeriods E₄ τ one_mem_strictPeriods_SL
  have hE₆ : E₆ ((1 : ℝ) +ᵥ τ) = E₆ τ :=
    SlashInvariantForm.vAdd_apply_of_mem_strictPeriods E₆ τ one_mem_strictPeriods_SL
  rw [hE₄, hE₆]

/-- `S`-invariance: `j (-1/τ) = j τ`. -/
theorem j_S_smul (τ : ℍ) : j (ModularGroup.S • τ) = j τ := j_smul ModularGroup.S τ

/-! ## Analyticity -/

/-- Klein's `J` is holomorphic on `ℍ`. -/
lemma mdifferentiable_J : MDiff (fun τ : ℍ ↦ J τ) := by
  have hnum : MDiff (fun τ : ℍ ↦ E₄ τ ^ 3) := (ModularFormClass.holo E₄).pow 3
  have hden : MDiff (fun τ : ℍ ↦ E₄ τ ^ 3 - E₆ τ ^ 2) :=
    ((ModularFormClass.holo E₄).pow 3).sub ((ModularFormClass.holo E₆).pow 2)
  exact hnum.div hden (fun τ ↦ E₄_cube_sub_E₆_sq_ne_zero τ)

/-- The `j`-invariant is holomorphic on `ℍ`. -/
lemma mdifferentiable_j : MDiff (fun τ : ℍ ↦ j τ) :=
  (mdifferentiable_const).mul mdifferentiable_J

/-! ## Integrality of the Eisenstein q-expansion coefficients

The ℤ-side building blocks of `(B1)`: `E₄` (hence `E₄³`) has integer q-expansion
coefficients. These feed the ℤ-refinement `ModularPolynomialZ.lean` downstream. -/

/-- Every q-expansion coefficient of `E₄` is an integer (`1` at `n = 0`, `240·σ₃(n)` else). -/
lemma E₄_qExpansion_coeff_int (n : ℕ) :
    ∃ c : ℤ, (qExpansion 1 E₄).coeff n = (c : ℂ) := by
  have h := EisensteinSeries.E_qExpansion_coeff (k := 4) (by norm_num) (by decide) n
  have hb : bernoulli 4 = -1 / 30 := by rw [bernoulli, bernoulli'_four]; norm_num
  rw [hb, show (4 : ℕ) - 1 = 3 from rfl] at h
  by_cases hn : n = 0
  · exact ⟨1, by rw [h, if_pos hn]; norm_num⟩
  · refine ⟨240 * ArithmeticFunction.sigma 3 n, ?_⟩
    rw [h, if_neg hn]
    push_cast
    norm_num

/-- Every q-expansion coefficient of the cube `(qExpansion E₄)³` — i.e. of `E₄³` — is an
integer. This is the numerator side of `j = E₄³/Δ`. -/
lemma E₄_qExpansion_pow_three_coeff_int (n : ℕ) :
    ∃ c : ℤ, ((qExpansion 1 E₄) ^ 3).coeff n = (c : ℂ) := by
  choose c hc using E₄_qExpansion_coeff_int
  have hmap : qExpansion 1 E₄ = (PowerSeries.mk c).map (Int.castRingHom ℂ) := by
    ext m
    simp [PowerSeries.coeff_map, PowerSeries.coeff_mk, hc m]
  refine ⟨((PowerSeries.mk c) ^ 3).coeff n, ?_⟩
  rw [hmap, ← map_pow, PowerSeries.coeff_map]
  rfl

/-! ## The formal ℤ-side: `E₄`, `E₆`, `Δ` as integer power series

We build the integer q-expansions formally in `PowerSeries ℤ` and identify them with
Mathlib's analytic `qExpansion`s. The only arithmetic input is the classical congruence
`1728 ∣ (E₄³ - E₆²)`-coefficients, which reduces to `d⁵ ≡ d³ (mod 24)`. -/

section IntegerQExpansion

/-- The formal power series `∑_{n ≥ 1} σ_k(n) Xⁿ` over `ℤ`. -/
private def sigmaPS (k : ℕ) : PowerSeries ℤ :=
  PowerSeries.mk fun n ↦ if n = 0 then 0 else (ArithmeticFunction.sigma k n : ℤ)

/-- The integer q-expansion `1 + 240·∑ σ₃(n) qⁿ` of `E₄`. -/
private def E4Z : PowerSeries ℤ := 1 + 240 * sigmaPS 3

/-- The integer q-expansion `1 - 504·∑ σ₅(n) qⁿ` of `E₆`. -/
private def E6Z : PowerSeries ℤ := 1 - 504 * sigmaPS 5

/-- Extract a numeral factor out of a power-series coefficient. -/
private lemma coeff_ofNat_mul {a : ℕ} [a.AtLeastTwo] (φ : PowerSeries ℤ) (n : ℕ) :
    PowerSeries.coeff n ((OfNat.ofNat a : PowerSeries ℤ) * φ)
      = OfNat.ofNat a * PowerSeries.coeff n φ := by
  rw [← map_ofNat (PowerSeries.C : ℤ →+* PowerSeries ℤ) a, PowerSeries.coeff_C_mul]

private lemma coeff_E4Z (n : ℕ) :
    PowerSeries.coeff n E4Z
      = if n = 0 then 1 else 240 * (ArithmeticFunction.sigma 3 n : ℤ) := by
  rw [E4Z, map_add, coeff_ofNat_mul, PowerSeries.coeff_one, sigmaPS, PowerSeries.coeff_mk]
  split <;> simp

private lemma coeff_E6Z (n : ℕ) :
    PowerSeries.coeff n E6Z
      = if n = 0 then 1 else -504 * (ArithmeticFunction.sigma 5 n : ℤ) := by
  rw [E6Z, map_sub, coeff_ofNat_mul, PowerSeries.coeff_one, sigmaPS, PowerSeries.coeff_mk]
  split <;> ring

/-- The Bernoulli number `B₆ = 1/42` (not in Mathlib as a literal). -/
private lemma bernoulli_six : bernoulli 6 = 1 / 42 := by
  have h5 : bernoulli' 5 = 0 := bernoulli'_eq_zero_of_odd ⟨2, rfl⟩ (by norm_num)
  have h6 : bernoulli' 6 = 1 / 42 := by
    rw [bernoulli'_def]
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_zero, bernoulli'_zero, bernoulli'_one, bernoulli'_two,
      bernoulli'_three, bernoulli'_four, h5]
    norm_num [Nat.choose]
  rw [bernoulli, h6]
  norm_num

/-- Analytic identification: Mathlib's q-expansion of `E₄` is the formal series `E4Z`. -/
private lemma qExpansion_E₄_eq :
    qExpansion 1 ⇑E₄ = PowerSeries.map (Int.castRingHom ℂ) E4Z := by
  ext n
  have h := EisensteinSeries.E_qExpansion_coeff (k := 4) (by norm_num) (by decide) n
  have hb : bernoulli 4 = -1 / 30 := by rw [bernoulli, bernoulli'_four]; norm_num
  rw [hb, show (4 : ℕ) - 1 = 3 from rfl] at h
  rw [PowerSeries.coeff_map, coeff_E4Z, h]
  split_ifs
  · norm_num
  · push_cast
    norm_num

/-- Analytic identification: Mathlib's q-expansion of `E₆` is the formal series `E6Z`. -/
private lemma qExpansion_E₆_eq :
    qExpansion 1 ⇑E₆ = PowerSeries.map (Int.castRingHom ℂ) E6Z := by
  ext n
  have h := EisensteinSeries.E_qExpansion_coeff (k := 6) (by norm_num) (by decide) n
  rw [bernoulli_six, show (6 : ℕ) - 1 = 5 from rfl] at h
  rw [PowerSeries.coeff_map, coeff_E6Z, h]
  split_ifs
  · norm_num
  · push_cast
    norm_num

/-- `d⁵ = d³` in `ZMod 24` — the arithmetic kernel of the `1728`-congruence. -/
private lemma zmod24_pow_five : ∀ x : ZMod 24, x ^ 5 = x ^ 3 := by decide

/-- `24 ∣ σ₅(n) - σ₃(n)`, coefficientwise input to the `1728`-divisibility. -/
private lemma dvd_sigma_sub (n : ℕ) :
    (24 : ℤ) ∣ (ArithmeticFunction.sigma 5 n : ℤ) - (ArithmeticFunction.sigma 3 n : ℤ) := by
  rw [ArithmeticFunction.sigma_apply, ArithmeticFunction.sigma_apply]
  push_cast
  rw [← Finset.sum_sub_distrib]
  refine Finset.dvd_sum fun d _ ↦ ?_
  refine (ZMod.intCast_zmod_eq_zero_iff_dvd ((d : ℤ) ^ 5 - (d : ℤ) ^ 3) 24).mp ?_
  push_cast
  rw [sub_eq_zero]
  exact zmod24_pow_five _

/-- Kronecker's normalization: every coefficient of `E₄³ - E₆²` is divisible by `1728`. -/
private lemma dvd_1728_coeff (m : ℕ) :
    (1728 : ℤ) ∣ PowerSeries.coeff m (E4Z ^ 3 - E6Z ^ 2) := by
  have hring : E4Z ^ 3 - E6Z ^ 2 =
      1728 * (sigmaPS 3 + 100 * sigmaPS 3 ^ 2 + 8000 * sigmaPS 3 ^ 3 - 147 * sigmaPS 5 ^ 2)
        + 1008 * (sigmaPS 5 - sigmaPS 3) := by
    rw [E4Z, E6Z]; ring
  rw [hring, map_add, coeff_ofNat_mul, coeff_ofNat_mul]
  refine dvd_add (dvd_mul_right 1728 _) ?_
  have h24 : (24 : ℤ) ∣ PowerSeries.coeff m (sigmaPS 5 - sigmaPS 3) := by
    rw [map_sub, sigmaPS, sigmaPS, PowerSeries.coeff_mk, PowerSeries.coeff_mk]
    split_ifs
    · simp
    · exact dvd_sigma_sub m
  obtain ⟨c, hc⟩ := h24
  exact ⟨14 * c, by rw [hc]; ring⟩

private lemma exists_delta_coeff (m : ℕ) :
    ∃ t : ℤ, PowerSeries.coeff m (E4Z ^ 3 - E6Z ^ 2) = 1728 * t := dvd_1728_coeff m

/-- The integer q-expansion of the discriminant `Δ = q·∏(1-qⁿ)²⁴ = ∑ τ(n) qⁿ`
(Ramanujan-τ coefficients), obtained as `(E₄³ - E₆²)/1728` in `ℤ⟦q⟧`. -/
def deltaInt : PowerSeries ℤ := PowerSeries.mk fun m ↦ (exists_delta_coeff m).choose

private lemma deltaInt_spec (m : ℕ) :
    PowerSeries.coeff m (E4Z ^ 3 - E6Z ^ 2) = 1728 * PowerSeries.coeff m deltaInt := by
  rw [deltaInt, PowerSeries.coeff_mk]
  exact (exists_delta_coeff m).choose_spec

/-! ### Analytic identification of `deltaInt` -/

private lemma analyticAt_E₄pow : AnalyticAt ℂ (cuspFunction 1 ⇑(E₄.pow 3)) 0 :=
  ModularFormClass.analyticAt_cuspFunction_zero (E₄.pow 3) one_pos one_mem_strictPeriods_SL

private lemma analyticAt_E₆pow : AnalyticAt ℂ (cuspFunction 1 ⇑(E₆.pow 2)) 0 :=
  ModularFormClass.analyticAt_cuspFunction_zero (E₆.pow 2) one_pos one_mem_strictPeriods_SL

private lemma analyticAt_discriminant : AnalyticAt ℂ (cuspFunction 1 discriminant) 0 :=
  ModularFormClass.analyticAt_cuspFunction_zero CuspForm.discriminant one_pos
    one_mem_strictPeriods_SL

private lemma qExpansion_E₄pow_eq :
    qExpansion 1 ⇑(E₄.pow 3) = PowerSeries.map (Int.castRingHom ℂ) (E4Z ^ 3) := by
  rw [ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL E₄ 3, qExpansion_E₄_eq,
    map_pow]

private lemma qExpansion_E₆pow_eq :
    qExpansion 1 ⇑(E₆.pow 2) = PowerSeries.map (Int.castRingHom ℂ) (E6Z ^ 2) := by
  rw [ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL E₆ 2, qExpansion_E₆_eq,
    map_pow]

/-- **`Δ` has integer q-expansion coefficients**: Mathlib's `qExpansion 1 Δ` is the
`ℤ`-power-series `deltaInt`, cast to `ℂ`. -/
theorem qExpansion_discriminant_int :
    qExpansion 1 discriminant = PowerSeries.map (Int.castRingHom ℂ) deltaInt := by
  have hfun : (⇑(E₄.pow 3) : ℍ → ℂ) - ⇑(E₆.pow 2) = (1728 : ℂ) • discriminant := by
    funext τ
    simp only [Pi.sub_apply, ModularForm.coe_pow, Pi.pow_apply, Pi.smul_apply, smul_eq_mul]
    exact E₄_cube_sub_E₆_sq_eq_discriminant τ
  have hsub := qExpansion_sub analyticAt_E₄pow analyticAt_E₆pow
  rw [hfun, qExpansion_smul analyticAt_discriminant, qExpansion_E₄pow_eq, qExpansion_E₆pow_eq,
    ← map_sub] at hsub
  ext m
  have h1 := congrArg (PowerSeries.coeff m) hsub
  rw [map_smul, smul_eq_mul, PowerSeries.coeff_map, deltaInt_spec, map_mul, map_ofNat] at h1
  rw [PowerSeries.coeff_map]
  exact mul_left_cancel₀ (by norm_num : (1728 : ℂ) ≠ 0) h1

/-- `Δ` vanishes at the cusp: constant q-expansion coefficient `0`. -/
theorem deltaInt_coeff_zero : PowerSeries.coeff 0 deltaInt = 0 := by
  have h := deltaInt_spec 0
  have h0 : PowerSeries.coeff 0 (E4Z ^ 3 - E6Z ^ 2) = 0 := by
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply]
    simp [E4Z, E6Z, sigmaPS, PowerSeries.constantCoeff_mk]
  rw [h0] at h
  omega

/-- `Δ = q + O(q²)`: the leading q-expansion coefficient of `Δ` is `1`. -/
theorem deltaInt_coeff_one : PowerSeries.coeff 1 deltaInt = 1 := by
  have h := congrArg (PowerSeries.coeff 1) qExpansion_discriminant_int
  rw [ModularForm.discriminant_qExpansion_coeff_one, PowerSeries.coeff_map, eq_intCast] at h
  exact_mod_cast h.symm

/-- The unit part `Δ/q ∈ ℤ⟦q⟧`: `deltaInt = X · deltaTail` with `deltaTail(0) = 1`. -/
def deltaTail : PowerSeries ℤ := PowerSeries.mk fun n ↦ PowerSeries.coeff (n + 1) deltaInt

theorem deltaInt_eq_X_mul_deltaTail : deltaInt = PowerSeries.X * deltaTail := by
  ext m
  cases m with
  | zero =>
    rw [deltaInt_coeff_zero, PowerSeries.coeff_zero_eq_constantCoeff_apply, map_mul,
      PowerSeries.constantCoeff_X, zero_mul]
  | succ n => rw [PowerSeries.coeff_succ_X_mul, deltaTail, PowerSeries.coeff_mk]

theorem constantCoeff_deltaTail : PowerSeries.constantCoeff deltaTail = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, deltaTail, PowerSeries.coeff_mk]
  exact deltaInt_coeff_one

/-- **The integer q-expansion of `j·q`**: `E₄³·(Δ/q)⁻¹` computed in `ℤ⟦q⟧` — the formal
series `1 + 744q + 196884q² + …`. -/
def jqInt : PowerSeries ℤ := E4Z ^ 3 * deltaTail.invOfUnit 1

/-- `j·q ∈ 1 + q·ℤ⟦q⟧`, formal part: the constant coefficient of `jqInt` is `1`. -/
theorem constantCoeff_jqInt : PowerSeries.constantCoeff jqInt = 1 := by
  rw [jqInt, map_mul, map_pow, PowerSeries.constantCoeff_invOfUnit]
  have h4 : PowerSeries.constantCoeff E4Z = 1 := by
    simp [E4Z, sigmaPS, PowerSeries.constantCoeff_mk]
  rw [h4]
  simp

/-! ### The analytic side: `τ ↦ q τ` and `τ ↦ j τ · q τ` -/

/-- The nome is `1`-periodic on `ℍ`. -/
lemma q_vadd_one (τ : ℍ) : q ((1 : ℝ) +ᵥ τ) = q τ := by
  rw [q_eq, q_eq]
  have hcoe : ((((1 : ℝ) +ᵥ τ) : ℍ) : ℂ) = 1 + (τ : ℂ) := by
    rw [UpperHalfPlane.coe_vadd]; norm_num
  rw [hcoe, mul_add, Complex.exp_add, mul_one, Complex.exp_two_pi_mul_I, one_mul]

private lemma periodic_qfun : Function.Periodic ((fun τ : ℍ ↦ q τ) ∘ ofComplex) 1 :=
  periodic_comp_ofComplex_of_vadd q_vadd_one

/-- The nome `q : ℍ → ℂ` is holomorphic. -/
lemma mdifferentiable_q : MDiff (fun τ : ℍ ↦ q τ) := by
  have heq : (fun τ : ℍ ↦ q τ)
      = (fun z : ℂ ↦ Complex.exp (2 * ↑π * Complex.I * z)) ∘ (fun τ : ℍ ↦ (τ : ℂ)) := by
    funext τ
    simp [q_eq, Function.comp]
  rw [heq]
  exact Differentiable.comp_mdifferentiable (by fun_prop) mdifferentiable_coe

private lemma isBoundedAtImInfty_qfun : IsBoundedAtImInfty (fun τ : ℍ ↦ q τ) := by
  have h : Filter.Tendsto (fun τ : ℍ ↦ q τ) atImInfty (nhds 0) :=
    qParam_tendsto_atImInfty one_pos
  change (fun τ : ℍ ↦ q τ) =O[atImInfty] (1 : ℍ → ℝ)
  exact h.isBigO_one ℝ

private lemma analyticAt_cuspFunction_qfun :
    AnalyticAt ℂ (cuspFunction 1 (fun τ : ℍ ↦ q τ)) 0 :=
  analyticAt_cuspFunction_zero one_pos periodic_qfun mdifferentiable_q isBoundedAtImInfty_qfun

private lemma isZeroAtImInfty_qfun : IsZeroAtImInfty (fun τ : ℍ ↦ q τ) :=
  qParam_tendsto_atImInfty one_pos

/-- The cusp function of the nome is the identity on the open unit disc. -/
private lemma cuspFunction_qfun_eqOn :
    Set.EqOn (cuspFunction 1 (fun τ : ℍ ↦ q τ)) id (Metric.ball 0 1) := by
  intro z hz
  by_cases hz0 : z = 0
  · subst hz0
    simpa using isZeroAtImInfty_qfun.cuspFunction_apply_zero one_pos
  · have him := Function.Periodic.im_invQParam_pos_of_norm_lt_one one_pos
      (by simpa [dist_zero_right] using hz) hz0
    simp [cuspFunction, Function.Periodic.cuspFunction_eq_of_nonzero 1 _ hz0,
      ofComplex_apply_of_im_pos him, q,
      Function.Periodic.qParam_right_inv one_ne_zero hz0]

/-- The q-expansion of the nome itself is the series `X`. -/
private lemma qExpansion_qfun_eq : qExpansion 1 (fun τ : ℍ ↦ q τ) = PowerSeries.X := by
  have heq : cuspFunction 1 (fun τ : ℍ ↦ q τ) =ᶠ[nhds 0] id :=
    Filter.eventuallyEq_of_mem (Metric.ball_mem_nhds 0 one_pos) cuspFunction_qfun_eqOn
  ext m
  rw [qExpansion_coeff, PowerSeries.coeff_X, Filter.EventuallyEq.iteratedDeriv_eq m heq]
  match m with
  | 0 => simp
  | 1 => simp
  | (k + 2) =>
    have hconst : iteratedDeriv (k + 2) (id : ℂ → ℂ) 0 = 0 := by
      rw [iteratedDeriv_succ', deriv_id']
      simp [iteratedDeriv_const]
    rw [hconst]
    simp

/-- `j·q` is invariant under `τ ↦ τ + 1`. -/
private lemma jq_vadd_one (τ : ℍ) : j ((1 : ℝ) +ᵥ τ) * q ((1 : ℝ) +ᵥ τ) = j τ * q τ := by
  rw [j_vadd_one, q_vadd_one]

private lemma periodic_jq : Function.Periodic ((fun τ : ℍ ↦ j τ * q τ) ∘ ofComplex) 1 :=
  periodic_comp_ofComplex_of_vadd jq_vadd_one

/-- `j·q` is holomorphic on `ℍ`. -/
lemma mdifferentiable_j_mul_q : MDiff (fun τ : ℍ ↦ j τ * q τ) :=
  mdifferentiable_j.mul mdifferentiable_q

/-- `j·q = E₄³/∏(1-qⁿ)²⁴` — the pole of `j` is exactly cancelled by the zero of `q`. -/
private lemma jq_eq_inv (τ : ℍ) :
    j τ * q τ = E₄ τ ^ 3 * (∏' n : ℕ, (1 - eta_q n ↑τ) ^ 24)⁻¹ := by
  have hΔ : discriminant τ = q τ * ∏' n : ℕ, (1 - eta_q n ↑τ) ^ 24 :=
    discriminant_eq_q_prod τ
  have hP0 : (∏' n : ℕ, (1 - eta_q n ↑τ) ^ 24) ≠ 0 := fun h0 ↦
    discriminant_ne_zero τ (by rw [hΔ, h0, mul_zero])
  rw [eq_mul_inv_iff_mul_eq₀ hP0, mul_assoc, ← hΔ]
  exact j_mul_discriminant τ

/-- `j·q` is bounded at the cusp (it tends to `1`). -/
private lemma isBoundedAtImInfty_jq : IsBoundedAtImInfty (fun τ : ℍ ↦ j τ * q τ) := by
  have heq : (fun τ : ℍ ↦ j τ * q τ)
      = ⇑E₄ * (⇑E₄ * (⇑E₄ * fun τ : ℍ ↦ (∏' n : ℕ, (1 - eta_q n ↑τ) ^ 24)⁻¹)) := by
    funext τ
    simp only [Pi.mul_apply]
    rw [jq_eq_inv τ]
    ring
  rw [heq]
  have hE : IsBoundedAtImInfty ⇑E₄ := ModularFormClass.bdd_at_infty E₄
  have hPinv : Filter.Tendsto (fun τ : ℍ ↦ (∏' n : ℕ, (1 - eta_q n ↑τ) ^ 24)⁻¹)
      atImInfty (nhds 1) := by
    simpa using tendsto_atImInfty_tprod_one_sub_eta_q_pow.inv₀ one_ne_zero
  have hPb : IsBoundedAtImInfty (fun τ : ℍ ↦ (∏' n : ℕ, (1 - eta_q n ↑τ) ^ 24)⁻¹) :=
    hPinv.isBigO_one ℝ
  exact Filter.BoundedAtFilter.mul hE (Filter.BoundedAtFilter.mul hE
    (Filter.BoundedAtFilter.mul hE hPb))

private lemma analyticAt_cuspFunction_jq :
    AnalyticAt ℂ (cuspFunction 1 (fun τ : ℍ ↦ j τ * q τ)) 0 :=
  analyticAt_cuspFunction_zero one_pos periodic_jq mdifferentiable_j_mul_q
    isBoundedAtImInfty_jq

/-! ### The keystone: `qExpansion (j·q) = jqInt` -/

private lemma qExpansion_jq_mul_discriminant :
    qExpansion 1 (fun τ : ℍ ↦ j τ * q τ) * qExpansion 1 discriminant
      = PowerSeries.map (Int.castRingHom ℂ) (E4Z ^ 3) * PowerSeries.X := by
  have hfun : (fun τ : ℍ ↦ j τ * q τ) * discriminant
      = ⇑(E₄.pow 3) * fun τ : ℍ ↦ q τ := by
    funext τ
    simp only [Pi.mul_apply, ModularForm.coe_pow, Pi.pow_apply]
    rw [mul_right_comm, j_mul_discriminant]
  calc qExpansion 1 (fun τ : ℍ ↦ j τ * q τ) * qExpansion 1 discriminant
      = qExpansion 1 ((fun τ : ℍ ↦ j τ * q τ) * discriminant) :=
        (qExpansion_mul analyticAt_cuspFunction_jq analyticAt_discriminant).symm
    _ = qExpansion 1 (⇑(E₄.pow 3) * fun τ : ℍ ↦ q τ) := by rw [hfun]
    _ = qExpansion 1 ⇑(E₄.pow 3) * qExpansion 1 (fun τ : ℍ ↦ q τ) :=
        qExpansion_mul analyticAt_E₄pow analyticAt_cuspFunction_qfun
    _ = _ := by rw [qExpansion_E₄pow_eq, qExpansion_qfun_eq]

/-- **(B1) headline, q-expansion form**: the q-expansion of `j·q` is the integer power
series `jqInt` (so `j·q ∈ 1 + q·ℤ⟦q⟧`, and `j` has a simple pole with residue-coefficient
`1` at the cusp). -/
theorem qExpansion_j_mul_q :
    qExpansion 1 (fun τ : ℍ ↦ j τ * q τ) = PowerSeries.map (Int.castRingHom ℂ) jqInt := by
  have hkey := qExpansion_jq_mul_discriminant
  rw [qExpansion_discriminant_int, deltaInt_eq_X_mul_deltaTail, map_mul,
    PowerSeries.map_X] at hkey
  -- cancel the factor `X`
  have hX : (PowerSeries.X : PowerSeries ℂ)
        * (qExpansion 1 (fun τ : ℍ ↦ j τ * q τ)
            * PowerSeries.map (Int.castRingHom ℂ) deltaTail)
      = PowerSeries.X * PowerSeries.map (Int.castRingHom ℂ) (E4Z ^ 3) := by
    linear_combination hkey
  have hcancel := mul_left_cancel₀ PowerSeries.X_ne_zero hX
  -- multiply by the inverse of the unit `deltaTail`
  have hunit : PowerSeries.map (Int.castRingHom ℂ) deltaTail
      * PowerSeries.map (Int.castRingHom ℂ) (deltaTail.invOfUnit 1) = 1 := by
    rw [← map_mul,
      PowerSeries.mul_invOfUnit deltaTail 1 (by rw [constantCoeff_deltaTail]; rfl), map_one]
  calc qExpansion 1 (fun τ : ℍ ↦ j τ * q τ)
      = qExpansion 1 (fun τ : ℍ ↦ j τ * q τ)
        * (PowerSeries.map (Int.castRingHom ℂ) deltaTail
          * PowerSeries.map (Int.castRingHom ℂ) (deltaTail.invOfUnit 1)) := by
        rw [hunit, mul_one]
    _ = (qExpansion 1 (fun τ : ℍ ↦ j τ * q τ)
          * PowerSeries.map (Int.castRingHom ℂ) deltaTail)
        * PowerSeries.map (Int.castRingHom ℂ) (deltaTail.invOfUnit 1) := by ring
    _ = PowerSeries.map (Int.castRingHom ℂ) (E4Z ^ 3)
        * PowerSeries.map (Int.castRingHom ℂ) (deltaTail.invOfUnit 1) := by rw [hcancel]
    _ = PowerSeries.map (Int.castRingHom ℂ) jqInt := by rw [jqInt, map_mul]

/-- **(B1) headline, convergent-sum form**: for every `τ ∈ ℍ`,
`j(τ)·q(τ) = ∑ c(n)·q(τ)ⁿ` with the integer coefficients `c = jqInt.coeff`. -/
theorem hasSum_j_mul_q (τ : ℍ) :
    HasSum (fun n : ℕ ↦ ((PowerSeries.coeff n jqInt : ℤ) : ℂ) * q τ ^ n) (j τ * q τ) := by
  have h := hasSum_qExpansion one_pos periodic_jq mdifferentiable_j_mul_q
    isBoundedAtImInfty_jq τ
  rw [qExpansion_j_mul_q] at h
  have heq : (fun n : ℕ ↦ ((PowerSeries.coeff n jqInt : ℤ) : ℂ) * q τ ^ n)
      = fun m : ℕ ↦ PowerSeries.coeff m (PowerSeries.map (Int.castRingHom ℂ) jqInt)
          • Function.Periodic.qParam 1 (τ : ℂ) ^ m := by
    funext m
    rw [PowerSeries.coeff_map, smul_eq_mul]
    rfl
  rw [heq]
  exact h

/-- Every q-expansion coefficient of `j·q` is an integer. -/
theorem j_mul_q_qExpansion_coeff_int (n : ℕ) :
    ∃ c : ℤ, PowerSeries.coeff n (qExpansion 1 (fun τ : ℍ ↦ j τ * q τ)) = (c : ℂ) :=
  ⟨PowerSeries.coeff n jqInt, by rw [qExpansion_j_mul_q, PowerSeries.coeff_map]; rfl⟩

/-- The q-expansion of `j·q` has constant coefficient `1` (equivalently, `j ~ 1/q` at the
cusp with leading coefficient `1` — the pole-order-1 structure needed downstream). -/
theorem j_mul_q_qExpansion_coeff_zero :
    PowerSeries.coeff 0 (qExpansion 1 (fun τ : ℍ ↦ j τ * q τ)) = 1 := by
  rw [qExpansion_j_mul_q, PowerSeries.coeff_map,
    PowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_jqInt]
  simp

/-- **(B1) headline, existential packaging**: `j·q ∈ 1 + q·ℤ⟦q⟧` — there are integers
`c 0 = 1, c 1 = 744, c 2 = 196884, …` with `j τ · q τ = ∑ c n · q τ ^ n` for all `τ : ℍ`. -/
theorem j_mul_q_hasSum_int :
    ∃ c : ℕ → ℤ, c 0 = 1 ∧
      ∀ τ : ℍ, HasSum (fun n : ℕ ↦ (c n : ℂ) * q τ ^ n) (j τ * q τ) :=
  ⟨fun n ↦ PowerSeries.coeff n jqInt,
    by
      change PowerSeries.coeff 0 jqInt = 1
      rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_jqInt],
    hasSum_j_mul_q⟩

end IntegerQExpansion

end Chudnovsky
