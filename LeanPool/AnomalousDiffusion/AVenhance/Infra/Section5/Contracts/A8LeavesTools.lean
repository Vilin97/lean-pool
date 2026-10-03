/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.A7Assembly
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.Produced
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.LaterStart

/-! # Quantifier-block combinators and amplitude monotonicity for the step-down estimate leaves

`OnA8Instances` is a long `∀` chain.  This file packages the three moves used when assembling the
seven relative fields from the θ-profile leaf: mapping a pointwise implication, applying an
implication proved on the block to a premise proved on the block (thresholds combine by `max`),
and passing from the big-bound premise block (no `θ_m`) to the step-down premise block.  It also
    records the (elementary)
monotonicity of the T-jet contracts in the coefficient `A`, and the scale inequality
`ε_{m-1}^{1+γ/2} ≤ R` on the block.
-/

@[expose] public section

open MeasureTheory Homogenization
noncomputable section
namespace AVenhance.Infra.Section5.Contracts
open AVenhance AVenhance.Infra.Section5 Integration

/-- The type of predicates over the step-down premise block. -/
abbrev A8Pred (β : ℝ) : Type :=
  ∀ (I : Ingredients β) (Φ : ℕ → ℝ → Vec 2 → ℝ), IsStreamSeq I Φ → ℝ → ℕ → ℝ →
    (Vec 2 → ℝ) → ℕ → (ℝ → Vec 2 → ℝ) → (ℝ → Vec 2 → ℝ) → (ℕ → ℝ → Vec 2 → ℝ) → Prop

/-- The relative amplitude `S = √κ_{m-1} · √‖∇θ_{m-1}‖²`. -/
abbrev relS {β : ℝ} (I : Ingredients β) (κ : ℝ) (M m : ℕ) (θprev : ℝ → Vec 2 → ℝ) : ℝ :=
  Real.sqrt (I.kappaSeq κ M (m - 1)) *
    Real.sqrt (spaceTimeGradNormSq (fun s x => spaceGrad (θprev s) x))

theorem relS_nonneg {β : ℝ} (I : Ingredients β) (κ : ℝ) (M m : ℕ) (θprev : ℝ → Vec 2 → ℝ) :
    0 ≤ relS I κ M m θprev :=
  mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

/-- Pointwise implication between block predicates. -/
theorem OnA8Instances.map {β C₀ C₁ : ℝ} {P Q : A8Pred β}
    (h : OnA8Instances β C₀ C₁ P)
    (f : ∀ I Φ hΦ κ M R θ₀ m θm θprev T,
      P I Φ hΦ κ M R θ₀ m θm θprev T → Q I Φ hΦ κ M R θ₀ m θm θprev T) :
    OnA8Instances β C₀ C₁ Q := by
  intro I hz hx hh hΛ Φ hΦ κ hκ M hM hperm R hR θ₀ hs hp hmean ha m hm hmM θm θprev T hθm hθ hT
  exact f _ _ _ _ _ _ _ _ _ _ _ (h I hz hx hh hΛ Φ hΦ κ hκ M hM hperm R hR θ₀ hs hp hmean ha
    m hm hmM θm θprev T hθm hθ hT)

/-- Pointwise implication that may use the radius and the cutoff index of the block. -/
theorem OnA8Instances.map_R {β C₀ C₁ : ℝ} {P Q : A8Pred β}
    (h : OnA8Instances β C₀ C₁ P)
    (f : ∀ I Φ hΦ κ M R θ₀ m θm θprev T, 0 < R → mTheta0 β I.Λ R ≤ m →
      P I Φ hΦ κ M R θ₀ m θm θprev T → Q I Φ hΦ κ M R θ₀ m θm θprev T) :
    OnA8Instances β C₀ C₁ Q := by
  intro I hz hx hh hΛ Φ hΦ κ hκ M hM hperm R hR θ₀ hs hp hmean ha m hm hmM θm θprev T hθm hθ hT
  exact f _ _ _ _ _ _ _ _ _ _ _ hR hm (h I hz hx hh hΛ Φ hΦ κ hκ M hM hperm R hR θ₀ hs hp hmean
    ha m hm hmM θm θprev T hθm hθ hT)

/-- Two-premise pointwise implication on the block. -/
theorem OnA8Instances.map₂ {β C₀ C₁ C₂ : ℝ} {P Q Z : A8Pred β}
    (hP : OnA8Instances β C₀ C₁ P) (hQ : OnA8Instances β C₀ C₂ Q)
    (f : ∀ I Φ hΦ κ M R θ₀ m θm θprev T,
      P I Φ hΦ κ M R θ₀ m θm θprev T → Q I Φ hΦ κ M R θ₀ m θm θprev T →
        Z I Φ hΦ κ M R θ₀ m θm θprev T) :
    OnA8Instances β C₀ (max C₁ C₂) Z := by
  intro I hz hx hh hΛ Φ hΦ κ hκ M hM hperm R hR θ₀ hs hp hmean ha m hm hmM θm θprev T hθm hθ hT
  exact f _ _ _ _ _ _ _ _ _ _ _
    (hP I hz hx hh ((le_max_left _ _).trans hΛ) Φ hΦ κ hκ M hM hperm R hR θ₀ hs hp hmean ha
      m hm hmM θm θprev T hθm hθ hT)
    (hQ I hz hx hh ((le_max_right _ _).trans hΛ) Φ hΦ κ hκ M hM hperm R hR θ₀ hs hp hmean ha
      m hm hmM θm θprev T hθm hθ hT)

/-- Conjunction on the block. -/
theorem OnA8Instances.and {β C₀ C₁ C₂ : ℝ} {P Q : A8Pred β}
    (hP : OnA8Instances β C₀ C₁ P) (hQ : OnA8Instances β C₀ C₂ Q) :
    OnA8Instances β C₀ (max C₁ C₂) (fun I Φ hΦ κ M R θ₀ m θm θprev T =>
      P I Φ hΦ κ M R θ₀ m θm θprev T ∧ Q I Φ hΦ κ M R θ₀ m θm θprev T) := by
  intro I hz hx hh hΛ Φ hΦ κ hκ M hM hperm R hR θ₀ hs hp hmean ha m hm hmM θm θprev T hθm hθ hT
  exact ⟨hP I hz hx hh ((le_max_left _ _).trans hΛ) Φ hΦ κ hκ M hM hperm R hR θ₀ hs hp hmean ha
      m hm hmM θm θprev T hθm hθ hT,
    hQ I hz hx hh ((le_max_right _ _).trans hΛ) Φ hΦ κ hκ M hM hperm R hR θ₀ hs hp hmean ha
      m hm hmM θm θprev T hθm hθ hT⟩

/-- A big-bound premise block statement is a step-down premise-block statement that ignores `θ_m`.
-/
theorem OnA8Instances.of_A7 {β C₀ C₁ : ℝ}
    {P : ∀ (I : Ingredients β) (Φ : ℕ → ℝ → Vec 2 → ℝ), IsStreamSeq I Φ → ℝ → ℕ → ℝ →
      (Vec 2 → ℝ) → ℕ → (ℝ → Vec 2 → ℝ) → (ℕ → ℝ → Vec 2 → ℝ) → Prop}
    (h : OnA7Instances β C₀ C₁ P) :
    OnA8Instances β C₀ C₁ (fun I Φ hΦ κ M R θ₀ m _θm θprev T =>
      P I Φ hΦ κ M R θ₀ m θprev T) := by
  intro I hz hx hh hΛ Φ hΦ κ hκ M hM hperm R hR θ₀ hs hp hmean ha m hm hmM θm θprev T hθm hθ hT
  exact h I hz hx hh hΛ Φ hΦ κ hκ M hM hperm R hR θ₀ hs hp hmean ha m hm hmM θprev T hθ hT

/-- Specialize a big-bound premise block family `∀ B ≥ 0, Q B` to the relative amplitude `S`. -/
theorem OnA8Instances.of_A7_forall {β C₀ C₁ : ℝ}
    {Q : ∀ (I : Ingredients β) (Φ : ℕ → ℝ → Vec 2 → ℝ), IsStreamSeq I Φ → ℝ → ℕ → ℝ →
      (Vec 2 → ℝ) → ℕ → (ℝ → Vec 2 → ℝ) → (ℕ → ℝ → Vec 2 → ℝ) → ℝ → Prop}
    (h : OnA7Instances β C₀ C₁ (fun I Φ hΦ κ M R θ₀ m θprev T =>
      ∀ B : ℝ, 0 ≤ B → Q I Φ hΦ κ M R θ₀ m θprev T B)) :
    OnA8Instances β C₀ C₁ (fun I Φ hΦ κ M R θ₀ m _θm θprev T =>
      Q I Φ hΦ κ M R θ₀ m θprev T (relS I κ M m θprev)) :=
  OnA8Instances.map (OnA8Instances.of_A7 h) fun I _ _ κ M _ _ m _ θprev _ hq => hq _ (relS_nonneg
      I κ M m θprev)

/-- Modus ponens under the gate: an ungated implication on the block applied to a gated
premise gives a gated conclusion. -/
theorem OnA8Instances.gate_mp {β C₀ C₁ C₂ : ℝ} {P Q : A8Pred β}
    (hPQ : OnA8Instances β C₀ C₁ (fun I Φ hΦ κ M R θ₀ m θm θprev T =>
      P I Φ hΦ κ M R θ₀ m θm θprev T → Q I Φ hΦ κ M R θ₀ m θm θprev T))
    (hP : OnA8Instances β C₀ C₂ (fun I Φ hΦ κ M R θ₀ m θm θprev T =>
      (6 : ℝ) / 5 ≤ β → epsilon β I.Λ (m - 1) ^ (1 + gamma β / 2 - delta β) ≤ R →
        P I Φ hΦ κ M R θ₀ m θm θprev T)) :
    OnA8Instances β C₀ (max C₁ C₂) (fun I Φ hΦ κ M R θ₀ m θm θprev T =>
      (6 : ℝ) / 5 ≤ β → epsilon β I.Λ (m - 1) ^ (1 + gamma β / 2 - delta β) ≤ R →
        Q I Φ hΦ κ M R θ₀ m θm θprev T) := by
  intro I hz hx hh hΛ Φ hΦ κ hκ M hM hperm R hR θ₀ hs hp hmean ha m hm hmM θm θprev T hθm hθ hT
    hβ hg
  exact hPQ I hz hx hh ((le_max_left _ _).trans hΛ) Φ hΦ κ hκ M hM hperm R hR θ₀ hs hp hmean ha
    m hm hmM θm θprev T hθm hθ hT
    (hP I hz hx hh ((le_max_right _ _).trans hΛ) Φ hΦ κ hκ M hM hperm R hR θ₀ hs hp hmean ha
      m hm hmM θm θprev T hθm hθ hT hβ hg)

/-- Conjunction under the gate. -/
theorem OnA8Instances.gate_and {β C₀ C₁ C₂ : ℝ} {P Q : A8Pred β}
    (hP : OnA8Instances β C₀ C₁ (fun I Φ hΦ κ M R θ₀ m θm θprev T =>
      (6 : ℝ) / 5 ≤ β → epsilon β I.Λ (m - 1) ^ (1 + gamma β / 2 - delta β) ≤ R →
        P I Φ hΦ κ M R θ₀ m θm θprev T))
    (hQ : OnA8Instances β C₀ C₂ (fun I Φ hΦ κ M R θ₀ m θm θprev T =>
      (6 : ℝ) / 5 ≤ β → epsilon β I.Λ (m - 1) ^ (1 + gamma β / 2 - delta β) ≤ R →
        Q I Φ hΦ κ M R θ₀ m θm θprev T)) :
    OnA8Instances β C₀ (max C₁ C₂) (fun I Φ hΦ κ M R θ₀ m θm θprev T =>
      (6 : ℝ) / 5 ≤ β → epsilon β I.Λ (m - 1) ^ (1 + gamma β / 2 - delta β) ≤ R →
        P I Φ hΦ κ M R θ₀ m θm θprev T ∧ Q I Φ hΦ κ M R θ₀ m θm θprev T) := by
  intro I hz hx hh hΛ Φ hΦ κ hκ M hM hperm R hR θ₀ hs hp hmean ha m hm hmM θm θprev T hθm hθ hT
    hβ hg
  exact ⟨hP I hz hx hh ((le_max_left _ _).trans hΛ) Φ hΦ κ hκ M hM hperm R hR θ₀ hs hp hmean ha
      m hm hmM θm θprev T hθm hθ hT hβ hg,
    hQ I hz hx hh ((le_max_right _ _).trans hΛ) Φ hΦ κ hκ M hM hperm R hR θ₀ hs hp hmean ha
      m hm hmM θm θprev T hθm hθ hT hβ hg⟩

/-- Pointwise implication under the gate. -/
theorem OnA8Instances.gate_map {β C₀ C₁ : ℝ} {P Q : A8Pred β}
    (h : OnA8Instances β C₀ C₁ (fun I Φ hΦ κ M R θ₀ m θm θprev T =>
      (6 : ℝ) / 5 ≤ β → epsilon β I.Λ (m - 1) ^ (1 + gamma β / 2 - delta β) ≤ R →
        P I Φ hΦ κ M R θ₀ m θm θprev T))
    (f : ∀ I Φ hΦ κ M R θ₀ m θm θprev T,
      P I Φ hΦ κ M R θ₀ m θm θprev T → Q I Φ hΦ κ M R θ₀ m θm θprev T) :
    OnA8Instances β C₀ C₁ (fun I Φ hΦ κ M R θ₀ m θm θprev T =>
      (6 : ℝ) / 5 ≤ β → epsilon β I.Λ (m - 1) ^ (1 + gamma β / 2 - delta β) ≤ R →
        Q I Φ hΦ κ M R θ₀ m θm θprev T) :=
  OnA8Instances.map h fun _ _ _ _ _ _ _ _ _ _ _ hp hβ hg => f _ _ _ _ _ _ _ _ _ _ _ (hp hβ hg)

/-! ### Scales on the block -/

/-- `ε_{m-1}^{1+γ/2} ≤ R` for `m ≥ m_θ₀(R)`. -/
theorem epsilon_radius_le_of_mTheta0 {β : ℝ} (I : Ingredients β) {R : ℝ} (hR : 0 < R) {m : ℕ}
    (hm : mTheta0 β I.Λ R ≤ m) :
    epsilon β I.Λ (m - 1) ^ (1 + gamma β / 2) ≤ R := by
  have hstar := mTheta0_spec I.one_lt_beta I.beta_lt I.two_pow_seven_le hR
  have he := AVenhance.Infra.Section5.RelativeError.epsilon_antitone I.one_lt_beta I.beta_lt
      I.two_pow_seven_le
    (by omega : mTheta0 β I.Λ R - 1 ≤ m - 1)
  have hγ := Infra.Ingredients.gamma_pos I.one_lt_beta I.beta_lt
  exact (Real.rpow_le_rpow
    (Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le).le he
    (by linarith : 0 ≤ 1 + gamma β / 2)).trans hstar.2

/-- The radius scale holds on the whole step-down premise block. -/
theorem OnA8Instances.radius (β C₀ : ℝ) :
    OnA8Instances β C₀ 0 (fun I _Φ _hΦ _κ _M R _θ₀ m _θm _θprev _T =>
      epsilon β I.Λ (m - 1) ^ (1 + gamma β / 2) ≤ R) := by
  intro I _ _ _ _ _ _ _ _ _ _ _ R hR _ _ _ _ _ m hm _ _ _ _ _ _ _
  exact epsilon_radius_le_of_mTheta0 I hR hm

/-! ### Monotonicity of the V-increment contract in the profile constant -/

theorem A8LeavesTools.iterateAmplitude_mono {η η' : ℝ} (hη : 0 ≤ η) (hle : η ≤ η') (i : ℕ) :
    Infra.Section4.iterateAmplitude η i ≤ Infra.Section4.iterateAmplitude η' i := by
  unfold Infra.Section4.iterateAmplitude
  split_ifs
  · exact le_rfl
  · exact hle
  · exact Real.rpow_le_rpow hη hle (by positivity)

theorem A8LeavesTools.iterateAmplitude_nonneg' {η : ℝ} (hη : 0 ≤ η) (i : ℕ) :
    0 ≤ Infra.Section4.iterateAmplitude η i := by
  unfold Infra.Section4.iterateAmplitude
  split_ifs
  · exact zero_le_one
  · exact hη
  · exact Real.rpow_nonneg hη _

theorem vIncrementContract_mono {β : ℝ} {I : Ingredients β} {m : ℕ} {κ Cs Cs' R N : ℝ}
    {T : ℕ → ℝ → Vec 2 → ℝ}
    (h : VIncrementContract I m κ T Cs R N) (hCs : 0 ≤ Cs) (hle : Cs ≤ Cs') (hR : 0 < R)
    (hN : 0 ≤ N) : VIncrementContract I m κ T Cs' R N := by
  intro i hi hiN v w hvw s hs0 hs1
  refine (h i hi hiN v w hvw s hs0 hs1).trans ?_
  have he : 0 < epsilon β I.Λ (m - 1) :=
    Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
  have hCs' : 0 ≤ Cs' := hCs.trans hle
  have hηbase : 0 ≤ epsilon β I.Λ (m - 1) ^ (2 * delta β) *
      max 1 (epsilon β I.Λ (m - 1) ^ (2 + gamma β) * R ^ (-2 : ℤ)) := by positivity
  have hη0 : 0 ≤ Cs ^ 3 * epsilon β I.Λ (m - 1) ^ (2 * delta β) *
      max 1 (epsilon β I.Λ (m - 1) ^ (2 + gamma β) * R ^ (-2 : ℤ)) := by positivity
  have hη : Cs ^ 3 * epsilon β I.Λ (m - 1) ^ (2 * delta β) *
      max 1 (epsilon β I.Λ (m - 1) ^ (2 + gamma β) * R ^ (-2 : ℤ)) ≤
      Cs' ^ 3 * epsilon β I.Λ (m - 1) ^ (2 * delta β) *
      max 1 (epsilon β I.Λ (m - 1) ^ (2 + gamma β) * R ^ (-2 : ℤ)) := by
    have h3 : Cs ^ 3 ≤ Cs' ^ 3 := pow_le_pow_left₀ hCs hle 3
    rw [mul_assoc, mul_assoc]
    exact mul_le_mul_of_nonneg_right h3 hηbase
  have hpowe : 0 ≤ epsilon β I.Λ (m - 1) ^ (-1 - gamma β / 2) := Real.rpow_nonneg he.le _
  have hL : max (Cs * epsilon β I.Λ (m - 1) ^ (-1 - gamma β / 2)) (Cs / R) ≤
      max (Cs' * epsilon β I.Λ (m - 1) ^ (-1 - gamma β / 2)) (Cs' / R) :=
    max_le_max (mul_le_mul_of_nonneg_right hle hpowe) (div_le_div_of_nonneg_right hle hR.le)
  have hL0 : 0 ≤ max (Cs * epsilon β I.Λ (m - 1) ^ (-1 - gamma β / 2)) (Cs / R) :=
    (mul_nonneg hCs hpowe).trans (le_max_left _ _)
  have hamp := A8LeavesTools.iterateAmplitude_mono hη0 hη i
  have hamp0 := A8LeavesTools.iterateAmplitude_nonneg' hη0 i
  have hw : Infra.Section4.iterateAnalyticWeight v.length i
      (max (Cs * epsilon β I.Λ (m - 1) ^ (-1 - gamma β / 2)) (Cs / R)) ≤
      Infra.Section4.iterateAnalyticWeight v.length i
      (max (Cs' * epsilon β I.Λ (m - 1) ^ (-1 - gamma β / 2)) (Cs' / R)) := by
    unfold Infra.Section4.iterateAnalyticWeight
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hL0 hL _) (by positivity)
  have hw0 := Infra.Section4.iterateAnalyticWeight_nonneg v.length i hL0
  exact mul_le_mul (mul_le_mul_of_nonneg_left hamp hN) hw hw0 (mul_nonneg hN
    (A8LeavesTools.iterateAmplitude_nonneg' (by positivity) i))

/-! ### Monotonicity of the T-jet contracts in the coefficient -/

theorem tGradientContract_mono {β κ A A' S : ℝ} {T : ℕ → ℝ → Vec 2 → ℝ}
    (h : TGradientContract β κ T A S) (hAA : A ≤ A') (hS : 0 ≤ S) :
    TGradientContract β κ T A' S :=
  h.trans (mul_le_mul_of_nonneg_right hAA hS)

theorem tPositiveJetsContract_mono {β : ℝ} {I : Ingredients β} {m : ℕ} {A A' S : ℝ}
    {T : ℕ → ℝ → Vec 2 → ℝ}
    (h : TPositiveJetsContract I m T A S) (hA : 0 ≤ A) (hAA : A ≤ A') (hS : 0 ≤ S) :
    TPositiveJetsContract I m T A' S := by
  intro n i hn t ht
  refine (h n i hn t ht).trans ?_
  have hr : 0 ≤ epsilon β I.Λ (m - 1) ^ (1 + gamma β / 2) :=
    Real.rpow_nonneg (Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt
      I.two_pow_seven_le).le _
  have hdiv : A / epsilon β I.Λ (m - 1) ^ (1 + gamma β / 2) ≤
      A' / epsilon β I.Λ (m - 1) ^ (1 + gamma β / 2) :=
    div_le_div_of_nonneg_right hAA hr
  have hpow := pow_le_pow_left₀ (div_nonneg hA hr) hdiv n
  have hf : (0 : ℝ) ≤ n.factorial := Nat.cast_nonneg _
  have hA' : 0 ≤ A' := hA.trans hAA
  calc A * S * n.factorial * (A / epsilon β I.Λ (m - 1) ^ (1 + gamma β / 2)) ^ n
      ≤ A' * S * n.factorial * (A / epsilon β I.Λ (m - 1) ^ (1 + gamma β / 2)) ^ n := by
        gcongr
    _ ≤ A' * S * n.factorial * (A' / epsilon β I.Λ (m - 1) ^ (1 + gamma β / 2)) ^ n := by
        gcongr

theorem firstOrderGradJetContract_mono {β : ℝ} {I : Ingredients β} {m : ℕ} {κ A A' S : ℝ}
    {T : ℕ → ℝ → Vec 2 → ℝ}
    (h : FirstOrderGradJetContract I m κ T A S) (hA : 0 ≤ A) (hAA : A ≤ A') (hS : 0 ≤ S) :
    FirstOrderGradJetContract I m κ T A' S := by
  intro i
  refine (h i).trans ?_
  have hr : 0 ≤ epsilon β I.Λ (m - 1) ^ (1 + gamma β / 2) :=
    Real.rpow_nonneg (Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt
      I.two_pow_seven_le).le _
  have hdiv : A / epsilon β I.Λ (m - 1) ^ (1 + gamma β / 2) ≤
      A' / epsilon β I.Λ (m - 1) ^ (1 + gamma β / 2) :=
    div_le_div_of_nonneg_right hAA hr
  have hA' : 0 ≤ A' := hA.trans hAA
  have hd0 : 0 ≤ A / epsilon β I.Λ (m - 1) ^ (1 + gamma β / 2) := div_nonneg hA hr
  gcongr

theorem secondOrderGradJetContract_mono {β : ℝ} {I : Ingredients β} {m : ℕ} {κ A A' S : ℝ}
    {T : ℕ → ℝ → Vec 2 → ℝ}
    (h : SecondOrderGradJetContract I m κ T A S) (hA : 0 ≤ A) (hAA : A ≤ A') (hS : 0 ≤ S) :
    SecondOrderGradJetContract I m κ T A' S := by
  intro i j
  refine (h i j).trans ?_
  have hr : 0 ≤ epsilon β I.Λ (m - 1) ^ (1 + gamma β / 2) :=
    Real.rpow_nonneg (Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt
      I.two_pow_seven_le).le _
  have hdiv : A / epsilon β I.Λ (m - 1) ^ (1 + gamma β / 2) ≤
      A' / epsilon β I.Λ (m - 1) ^ (1 + gamma β / 2) :=
    div_le_div_of_nonneg_right hAA hr
  have hA' : 0 ≤ A' := hA.trans hAA
  have hd0 : 0 ≤ A / epsilon β I.Λ (m - 1) ^ (1 + gamma β / 2) := div_nonneg hA hr
  gcongr

end AVenhance.Infra.Section5.Contracts

end
