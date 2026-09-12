/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.DiagonalJetBounds
public import LeanPool.NavierStokesAndEuler.NavierStokes.ResidualStability
import LeanPool.NavierStokesAndEuler.NavierStokes.ResidualRegularity

/-!
# Residual flatness from quantitative finite-stage data

The finite approximation used in the proof depends on the requested jet order
and decay power. Stage constants and neighborhoods may depend on that stage;
the loss of powers in the background estimates must not. All jet estimates
refer to actual iterated Fréchet derivatives of the displayed fields.
-/

@[expose] public section


noncomputable section

namespace NavierStokes.DiagonalResidual

open Set Filter Function
open scoped Topology BigOperators ContDiff

/-- Cache the standard `NormedAddCommGroup (ProblemStatement.SpaceTime →L[ℝ]
ProblemStatement.SpaceTime →L[ℝ] ProblemStatement.Space)` instance to shorten typeclass
synthesis. -/
local instance instDiagonalResidual1 : NormedAddCommGroup
    (ProblemStatement.SpaceTime →L[ℝ] ProblemStatement.SpaceTime →L[ℝ] ProblemStatement.Space) :=
  inferInstance
/-- Cache the standard `NormedSpace ℝ (ProblemStatement.SpaceTime →L[ℝ]
ProblemStatement.SpaceTime →L[ℝ] ProblemStatement.Space)` instance to shorten typeclass
synthesis. -/
local instance instDiagonalResidual2 : NormedSpace ℝ
    (ProblemStatement.SpaceTime →L[ℝ] ProblemStatement.SpaceTime →L[ℝ] ProblemStatement.Space) :=
  inferInstance

section Rates

variable {D V : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- A single quantitative order for one actual derivative. -/
def JetRate (l : Filter D) (q : D → ℝ) (f : D → V) (m : ℕ) (r : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ x in l, ‖iteratedFDeriv ℝ m f x‖ ≤ C * (q x) ^ r

/-- A common constant and neighborhood for a finite list of actual jets. -/
def FiniteJetRate (l : Filter D) (q : D → ℝ) (f : D → V) (M : ℕ) (r : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ x in l, ∀ m ≤ M,
    ‖iteratedFDeriv ℝ m f x‖ ≤ C * (q x) ^ r

theorem JetRate.weaken {l : Filter D} {q : D → ℝ} {f : D → V} {m : ℕ} {r s : ℝ}
    (hf : JetRate l q f m r) (hq : ∀ᶠ x in l, 0 < q x ∧ q x ≤ 1) (hsr : s ≤ r) :
    JetRate l q f m s := by
  obtain ⟨C, hC, hb⟩ := hf
  refine ⟨C, hC, ?_⟩
  filter_upwards [hq, hb] with x hx hbound
  exact hbound.trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_ge hx.1 hx.2 hsr) hC)

theorem finiteJetRate_of_jetRate {l : Filter D} {q : D → ℝ} {f : D → V} {r : ℝ}
    (hq : ∀ᶠ x in l, 0 < q x) (M : ℕ) :
    (∀ m ≤ M, JetRate l q f m r) → FiniteJetRate l q f M r := by
  induction M with
  | zero =>
      intro h
      obtain ⟨C, hC, hb⟩ := h 0 le_rfl
      refine ⟨C, hC, ?_⟩
      filter_upwards [hb] with x hx
      intro m hm
      have hm0 : m = 0 := Nat.eq_zero_of_le_zero hm
      subst m
      exact hx
  | succ M ih =>
      intro h
      obtain ⟨A, hA, ha⟩ := ih (fun m hm => h m (by omega))
      obtain ⟨B, hB, hb⟩ := h (M + 1) le_rfl
      refine ⟨A + B, add_nonneg hA hB, ?_⟩
      filter_upwards [hq, ha, hb] with x hx hax hbx
      intro m hm
      by_cases hmM : m ≤ M
      · exact (hax m hmM).trans (mul_le_mul_of_nonneg_right
          (le_add_of_nonneg_right hB) (Real.rpow_nonneg hx.le r))
      · have hm' : m = M + 1 := by omega
        subst m
        exact hbx.trans (mul_le_mul_of_nonneg_right
          (le_add_of_nonneg_left hA) (Real.rpow_nonneg hx.le r))

theorem JetRate.add {l : Filter D} {q : D → ℝ} {f g : D → V} {m : ℕ} {r : ℝ}
    {U : Set D} (hf : JetRate l q f m r) (hg : JetRate l q g m r)
    (hU : IsOpen U) (hlU : ∀ᶠ x in l, x ∈ U)
    (hsf : ContDiffOn ℝ ∞ f U) (hsg : ContDiffOn ℝ ∞ g U) :
    JetRate l q (fun x => f x + g x) m r := by
  obtain ⟨A, hA, ha⟩ := hf
  obtain ⟨B, hB, hb⟩ := hg
  refine ⟨A + B, add_nonneg hA hB, ?_⟩
  filter_upwards [hlU, ha, hb] with x hx hax hbx
  calc
    _ ≤ ‖iteratedFDeriv ℝ m f x‖ + ‖iteratedFDeriv ℝ m g x‖ :=
      ResidualStability.norm_jet_add_le hU hsf hsg hx m
    _ ≤ A * (q x) ^ r + B * (q x) ^ r := add_le_add hax hbx
    _ = (A + B) * (q x) ^ r := (add_mul _ _ _).symm

theorem JetRate.congr_on {l : Filter D} {q : D → ℝ} {f g : D → V} {m : ℕ} {r : ℝ}
    {U : Set D} (hf : JetRate l q f m r) (hU : IsOpen U)
    (hlU : ∀ᶠ x in l, x ∈ U) (hfg : EqOn f g U) : JetRate l q g m r := by
  obtain ⟨C, hC, hb⟩ := hf
  refine ⟨C, hC, ?_⟩
  filter_upwards [hlU, hb] with x hx hbound
  rwa [← ResidualStability.iteratedFDeriv_eqOn hU hfg m hx]

end Rates

section Powers

/-- A nonnegative upper bound for every loss in a finite derivative list. -/
def maxJetLoss (L : ℕ → ℝ) (M : ℕ) : ℝ :=
  max 0 ((Finset.range (M + 1)).sup'
    ⟨0, Finset.mem_range.mpr (Nat.succ_pos M)⟩ L)

theorem maxJetLoss_nonneg (L : ℕ → ℝ) (M : ℕ) : 0 ≤ maxJetLoss L M :=
  le_max_left _ _

theorem le_maxJetLoss (L : ℕ → ℝ) {m M : ℕ} (hm : m ≤ M) : L m ≤ maxJetLoss L M :=
  (Finset.le_sup' L (Finset.mem_range.mpr (Nat.lt_succ_of_le hm))).trans (le_max_right _ _)

theorem power_product_le {q A B r s n : ℝ} (hq : 0 < q) (hq1 : q ≤ 1)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hn : n ≤ r + s) :
    (A * q ^ r) * (B * q ^ s) ≤ (A * B) * q ^ n := by
  calc
    _ = (A * B) * q ^ (r + s) := by rw [Real.rpow_add hq]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_ge hq hq1 hn) (mul_nonneg hA hB)

/-- A scalar version of the six-term residual estimate. Taking the tail
order at least `n+b` absorbs background growth `q^(-b)` and the quadratic
tail term, with constants allowed to depend on the chosen stage. -/
theorem perturbation_majorant_le {q A W P b n t d p k : ℝ}
    (hq : 0 < q) (hq1 : q ≤ 1) (hA : 0 ≤ A) (hW : 0 ≤ W) (hP : 0 ≤ P)
    (hb : 0 ≤ b) (hn : 0 ≤ n)
    (ht : 0 ≤ t) (hd : 0 ≤ d) (hp : 0 ≤ p) (hk : 0 ≤ k) :
    t * (W * q ^ (n + b)) + d * (W * q ^ (n + b)) + p * (P * q ^ (n + b)) +
      k * (A * q ^ (-b)) * (W * q ^ (n + b)) +
      k * (W * q ^ (n + b)) * (A * q ^ (-b)) +
      k * (W * q ^ (n + b)) * (W * q ^ (n + b)) ≤
      (t * W + d * W + p * P + k * A * W + k * W * A + k * W * W) * q ^ n := by
  have hpow : q ^ (n + b) ≤ q ^ n :=
    Real.rpow_le_rpow_of_exponent_ge hq hq1 (by linarith)
  have hlinW := mul_le_mul_of_nonneg_left hpow hW
  have hlinP := mul_le_mul_of_nonneg_left hpow hP
  have hAW := power_product_le hq hq1 hA hW (show n ≤ -b + (n + b) by linarith)
  have hWA := power_product_le hq hq1 hW hA (show n ≤ (n + b) + -b by linarith)
  have hWW := power_product_le hq hq1 hW hW (show n ≤ (n + b) + (n + b) by linarith)
  have h1 := mul_le_mul_of_nonneg_left hlinW ht
  have h2 := mul_le_mul_of_nonneg_left hlinW hd
  have h3 := mul_le_mul_of_nonneg_left hlinP hp
  have h4 := mul_le_mul_of_nonneg_left hAW hk
  have h5 := mul_le_mul_of_nonneg_left hWA hk
  have h6 := mul_le_mul_of_nonneg_left hWW hk
  calc
    _ ≤ t * (W * q ^ n) + d * (W * q ^ n) + p * (P * q ^ n) +
        k * ((A * W) * q ^ n) + k * ((W * A) * q ^ n) + k * ((W * W) * q ^ n) := by
      simpa only [mul_assoc] using add_le_add (add_le_add (add_le_add (add_le_add
        (add_le_add h1 h2) h3) h4) h5) h6
    _ = _ := by ring

end Powers


section Residual

open ProblemStatement ResidualStability

/-- Quantitative residual stability packaged as an eventual power estimate.
The background exponent `b` is paid for by selecting tail order `n+b`. -/
theorem residualDifference_jetRate {U : Set SpaceTime} {l : Filter SpaceTime}
    {q : SpaceTime → ℝ} {u w : VelocityField} {p r : PressureField}
    (hU : IsOpen U) (hlU : ∀ᶠ z in l, z ∈ U)
    (hq : ∀ᶠ z in l, 0 < q z ∧ q z ≤ 1)
    (hu : ContDiffOn ℝ ∞ u U) (hw : ContDiffOn ℝ ∞ w U)
    (hp : ContDiffOn ℝ ∞ p U) (hr : ContDiffOn ℝ ∞ r U)
    (m : ℕ) {b n : ℝ} (hb : 0 ≤ b) (hn : 0 ≤ n)
    (hbg : FiniteJetRate l q u (m + 1) (-b))
    (hwu : FiniteJetRate l q w (m + 2) (n + b))
    (hpr : FiniteJetRate l q r (m + 1) (n + b)) :
    JetRate l q (residualDifference u w p r) m n := by
  obtain ⟨A, hA, hAb⟩ := hbg
  obtain ⟨W, hW, hWb⟩ := hwu
  obtain ⟨P, hP, hPb⟩ := hpr
  let K : ℝ := ‖spaceRestriction Space‖ * (2 : ℝ) ^ m
  let C : ℝ := ‖timeJet‖ * W + ‖laplaceJet‖ * W + ‖pressureJet‖ * P +
    K * A * W + K * W * A + K * W * W
  refine ⟨C, ?_, ?_⟩
  · dsimp [C, K]
    positivity
  · filter_upwards [hlU, hq, hAb, hWb, hPb] with z hz hqz hAz hWz hPz
    have hres := residualDifference_jet_bound hU hu hw hp hr hz m hAz hWz hPz
    have hpow := perturbation_majorant_le hqz.1 hqz.2 hA hW hP hb hn
      (norm_nonneg timeJet) (norm_nonneg laplaceJet) (norm_nonneg pressureJet)
      (show 0 ≤ K by dsimp [K]; positivity)
    exact hres.trans hpow

/-- For each requested order choose a single sufficiently advanced stage.
Only the jets through `m+2` of its tail are used, and the background power
losses are independent of the stage. Constants and neighborhoods may depend
on the stage and derivative order. -/
theorem residual_jetRate_of_stages {U : Set SpaceTime} {l : Filter SpaceTime}
    {q : SpaceTime → ℝ} {u : VelocityField} {p : PressureField}
    {uStage : ℕ → VelocityField} {pStage : ℕ → PressureField}
    {g Lbg Ltail Lres : ℕ → ℝ}
    (hU : IsOpen U) (hlU : ∀ᶠ z in l, z ∈ U)
    (hq : ∀ᶠ z in l, 0 < q z ∧ q z ≤ 1)
    (hu : ContDiffOn ℝ ∞ u U) (hp : ContDiffOn ℝ ∞ p U)
    (hus : ∀ J, ContDiffOn ℝ ∞ (uStage J) U)
    (hps : ∀ J, ContDiffOn ℝ ∞ (pStage J) U)
    (hg : Tendsto g atTop atTop)
    (hbg : ∀ J m, JetRate l q (uStage J) m (-Lbg m))
    (htu : ∀ J m, m ≤ J →
      JetRate l q (fun z => u z - uStage J z) m (g J - Ltail m))
    (htp : ∀ J m, m ≤ J →
      JetRate l q (fun z => p z - pStage J z) m (g J - Ltail m))
    (hres : ∀ J m, JetRate l q
      (fun z => navierStokesResidual (uStage J) (pStage J) z.1 z.2) m (g J - Lres m))
    (m : ℕ) (n : ℝ) (hn : 0 ≤ n) :
    JetRate l q (fun z => navierStokesResidual u p z.1 z.2) m n := by
  let b := maxJetLoss Lbg (m + 1)
  let t := maxJetLoss Ltail (m + 2)
  have hb : 0 ≤ b := maxJetLoss_nonneg Lbg (m + 1)
  obtain ⟨J₀, hJ₀⟩ := eventually_atTop.1
    (hg.eventually (eventually_ge_atTop (max (n + b + t) (n + Lres m))))
  let J := max (m + 2) J₀
  have hJm : m + 2 ≤ J := le_max_left _ _
  have hgJ : max (n + b + t) (n + Lres m) ≤ g J := hJ₀ J (le_max_right _ _)
  have hgain : n + b + t ≤ g J := (le_max_left _ _).trans hgJ
  have hresgain : n + Lres m ≤ g J := (le_max_right _ _).trans hgJ
  have hqpos : ∀ᶠ z in l, 0 < q z := hq.mono (fun _ hz => hz.1)
  have hbackground : FiniteJetRate l q (uStage J) (m + 1) (-b) := by
    apply finiteJetRate_of_jetRate hqpos
    intro k hk
    exact (hbg J k).weaken hq (neg_le_neg (le_maxJetLoss Lbg hk))
  have htailgain (k : ℕ) (hk : k ≤ m + 2) : n + b ≤ g J - Ltail k := by
    have hkt : Ltail k ≤ t := le_maxJetLoss Ltail hk
    linarith
  have hvelocity : FiniteJetRate l q (fun z => u z - uStage J z) (m + 2) (n + b) := by
    apply finiteJetRate_of_jetRate hqpos
    intro k hk
    exact (htu J k (hk.trans hJm)).weaken hq (htailgain k hk)
  have hpressure : FiniteJetRate l q (fun z => p z - pStage J z) (m + 1) (n + b) := by
    apply finiteJetRate_of_jetRate hqpos
    intro k hk
    exact (htp J k (by omega)).weaken hq (htailgain k (by omega))
  have hstage : JetRate l q
      (fun z => navierStokesResidual (uStage J) (pStage J) z.1 z.2) m n :=
    (hres J m).weaken hq (by linarith)
  have hdiff := residualDifference_jetRate hU hlU hq (hus J) (hu.sub (hus J))
    (hps J) (hp.sub (hps J)) m hb hn hbackground hvelocity hpressure
  have hsStage := ResidualRegularity.contDiffOn_residual hU (hus J) (hps J)
  have hsDiff : ContDiffOn ℝ ∞
      (residualDifference (uStage J) (fun z => u z - uStage J z)
        (pStage J) (fun z => p z - pStage J z)) U :=
    (ResidualRegularity.contDiffOn_residual hU ((hus J).add (hu.sub (hus J)))
      ((hps J).add (hp.sub (hps J)))).sub hsStage
  have hsum := hstage.add hdiff hU hlU hsStage hsDiff
  have huadd : (fun z => uStage J z + (u z - uStage J z)) = u := by
    funext z
    abel
  have hpadd : (fun z => pStage J z + (p z - pStage J z)) = p := by
    funext z
    abel
  have hidentity :
      (fun z => navierStokesResidual (uStage J) (pStage J) z.1 z.2 +
        residualDifference (uStage J) (fun y => u y - uStage J y)
          (pStage J) (fun y => p y - pStage J y) z) =
      (fun z => navierStokesResidual u p z.1 z.2) := by
    funext z
    simp only [residualDifference, huadd, hpadd]
    abel
  rwa [hidentity] at hsum

/-- Every actual residual jet is flat. This follows by choosing a different
finite stage for each requested derivative and decay order; no fixed tail
is assumed or proved flat to all orders. -/
theorem allJetsFlat_residual_of_stages {U : Set SpaceTime} {l : Filter SpaceTime}
    {q : SpaceTime → ℝ} {u : VelocityField} {p : PressureField}
    {uStage : ℕ → VelocityField} {pStage : ℕ → PressureField}
    {g Lbg Ltail Lres : ℕ → ℝ}
    (hU : IsOpen U) (hlU : ∀ᶠ z in l, z ∈ U)
    (hq : ∀ᶠ z in l, 0 < q z ∧ q z ≤ 1)
    (hu : ContDiffOn ℝ ∞ u U) (hp : ContDiffOn ℝ ∞ p U)
    (hus : ∀ J, ContDiffOn ℝ ∞ (uStage J) U)
    (hps : ∀ J, ContDiffOn ℝ ∞ (pStage J) U)
    (hg : Tendsto g atTop atTop)
    (hbg : ∀ J m, JetRate l q (uStage J) m (-Lbg m))
    (htu : ∀ J m, m ≤ J →
      JetRate l q (fun z => u z - uStage J z) m (g J - Ltail m))
    (htp : ∀ J m, m ≤ J →
      JetRate l q (fun z => p z - pStage J z) m (g J - Ltail m))
    (hres : ∀ J m, JetRate l q
      (fun z => navierStokesResidual (uStage J) (pStage J) z.1 z.2) m (g J - Lres m)) :
    AllJetsFlat l q (fun z => navierStokesResidual u p z.1 z.2) := by
  intro m N
  obtain ⟨C, hC, hbound⟩ := residual_jetRate_of_stages hU hlU hq hu hp hus hps
    hg hbg htu htp hres m (N : ℝ) (Nat.cast_nonneg N)
  refine ⟨C, hC, ?_⟩
  filter_upwards [hq, hbound] with z hz hb
  simpa only [abs_norm, abs_of_pos hz.1, Real.rpow_natCast] using hb

end Residual

section DiagonalBridge

variable {D V : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The actual diagonal tail provides the `JetRate` used in the residual
theorem. This is a fixed-prefix rate, not all-order flatness of that tail. -/
theorem jetRate_diagonal_tail {a : ℕ → ℝ} (ha : Tendsto a atTop atTop)
    {q : D → ℝ} {A : ℕ → D → V} {g L : ℕ → ℝ} {U : Set D} {l : Filter D}
    (hU : IsOpen U) (hq : ContDiffOn ℝ ∞ q U)
    (hA : ∀ j, ContDiffOn ℝ ∞ (A j) U) (hg : Monotone g)
    (hb : DiagonalJetBounds.CutStageBounds a q A g L U)
    (hlU : ∀ᶠ x in l, x ∈ U) (hlq : ∀ᶠ x in l, 0 < q x ∧ q x ≤ 1)
    (hqzero : Tendsto q l (𝓝 0)) (J m : ℕ) (hm : m ≤ J + 3) :
    JetRate l q
      (fun x => SolenoidalDiagonal.potentialSum a q A x -
        DiagonalJetBounds.uncutPrefix A (J + 1) x) m (g (J + 1) - L m) := by
  obtain ⟨δ, hδ, hprefix⟩ :=
    DiagonalJetBounds.partialPotential_eventuallyEq_uncut a q A (J + 1)
  refine ⟨(1 / 2 : ℝ) ^ J, by positivity, ?_⟩
  filter_upwards [hlU, hlq, hqzero.eventually (gt_mem_nhds hδ)] with x hx hqx hsmall
  have hpref := hprefix x (hq.contDiffAt (hU.mem_nhds hx)).continuousAt
    (by simpa only [abs_of_pos hqx.1] using hsmall)
  have heq :
      (fun y => SolenoidalDiagonal.potentialSum a q A y -
        SolenoidalDiagonal.partialPotential a q A (J + 1) y) =ᶠ[𝓝 x]
      (fun y => SolenoidalDiagonal.potentialSum a q A y -
        DiagonalJetBounds.uncutPrefix A (J + 1) y) := by
    filter_upwards [hpref] with y hy
    rw [hy]
  rw [← (SolenoidalDiagonal.iteratedFDeriv_eventuallyEq heq m).self_of_nhds]
  exact DiagonalJetBounds.potential_tail_jet_bound ha hU hq hA hg hb hx
    hqx.1 hqx.2 J m hm

end DiagonalBridge

section DiagonalVelocity

open ProblemStatement ResidualStability

/-- A spatial curl costs one actual full derivative and a fixed operator
norm, independently of the chosen diagonal prefix. -/
theorem JetRate.spatialCurl {U : Set SpaceTime} {l : Filter SpaceTime}
    {q : SpaceTime → ℝ} {A : VelocityField} {m : ℕ} {r : ℝ}
    (hbound : JetRate l q A (m + 1) r) (hU : IsOpen U)
    (hlU : ∀ᶠ z in l, z ∈ U) (hA : ContDiffOn ℝ ∞ A U) :
    JetRate l q (SpatialCurl.spatialCurl A) m r := by
  obtain ⟨C, hC, hb⟩ := hbound
  let K : ℝ := ‖SpatialCurl.curlLinear.comp (spaceRestriction Space)‖
  refine ⟨K * C, mul_nonneg
    (norm_nonneg (SpatialCurl.curlLinear.comp (spaceRestriction Space))) hC, ?_⟩
  filter_upwards [hlU, hb] with z hz hboundz
  calc
    _ ≤ K * ‖iteratedFDeriv ℝ (m + 1) A z‖ :=
      norm_iteratedFDeriv_spatialCurl_le hU hA hz m
    _ ≤ K * (C * (q z) ^ r) := mul_le_mul_of_nonneg_left hboundz
      (norm_nonneg (SpatialCurl.curlLinear.comp (spaceRestriction Space)))
    _ = (K * C) * (q z) ^ r := (mul_assoc _ _ _).symm

theorem spatialCurl_sub_on {U : Set SpaceTime} {A B : VelocityField}
    (hU : IsOpen U) (hA : ContDiffOn ℝ ∞ A U) (hB : ContDiffOn ℝ ∞ B U) :
    EqOn (SpatialCurl.spatialCurl (fun z => A z - B z))
      (fun z => SpatialCurl.spatialCurl A z - SpatialCurl.spatialCurl B z) U := by
  intro z hz
  have hAs := spatialSlice_differentiable hU hA hz
  have hBs := spatialSlice_differentiable hU hB hz
  change SpatialCurl.curlLinear
      (fderiv ℝ (fun y => A (z.1, y) - B (z.1, y)) z.2) = _
  rw [fderiv_fun_sub hAs hBs, map_sub]
  rfl

/-- The velocity tail of the actual solenoidal diagonal construction has a
fixed-prefix jet rate, obtained from one higher potential derivative. -/
theorem jetRate_diagonal_velocity_tail {a : ℕ → ℝ} (ha : Tendsto a atTop atTop)
    {q : SpaceTime → ℝ} {A : ℕ → VelocityField} {g L : ℕ → ℝ}
    {U : Set SpaceTime} {l : Filter SpaceTime}
    (hU : IsOpen U) (hqpos : ∀ z ∈ U, 0 < q z) (hq : ContDiffOn ℝ ∞ q U)
    (hA : ∀ j, ContDiffOn ℝ ∞ (A j) U) (hg : Monotone g)
    (hb : DiagonalJetBounds.CutStageBounds a q A g L U)
    (hlU : ∀ᶠ z in l, z ∈ U) (hlq : ∀ᶠ z in l, 0 < q z ∧ q z ≤ 1)
    (hqzero : Tendsto q l (𝓝 0)) (J m : ℕ) (hm : m + 1 ≤ J + 3) :
    JetRate l q
      (fun z => SolenoidalDiagonal.velocitySum a q A z -
        SpatialCurl.spatialCurl (DiagonalJetBounds.uncutPrefix A (J + 1)) z)
      m (g (J + 1) - L (m + 1)) := by
  have hsum := SolenoidalDiagonal.potentialSum_contDiffOn ha hU hqpos hq hA
  have hprefix : ContDiffOn ℝ ∞ (DiagonalJetBounds.uncutPrefix A (J + 1)) U :=
    ContDiffOn.sum (fun j _ => hA j)
  have htail := jetRate_diagonal_tail ha hU hq hA hg hb hlU hlq hqzero J (m + 1) hm
  exact (htail.spatialCurl hU hlU (hsum.sub hprefix)).congr_on hU hlU
    (spatialCurl_sub_on hU hsum hprefix)

/-- Explicit diagonal-sum corollary. Velocity is the curl of the constructed
potential sum and pressure is the constructed scalar sum. Their tail
assumptions are discharged by `DiagonalJetBounds`; the background growth and
finite-stage residual estimates remain the genuine construction inputs. -/
theorem allJetsFlat_diagonal_residual {a : ℕ → ℝ} (ha : Tendsto a atTop atTop)
    {q : SpaceTime → ℝ} {A : ℕ → VelocityField} {P : ℕ → PressureField}
    {g LA LP Lbg Lres : ℕ → ℝ} {U : Set SpaceTime} {l : Filter SpaceTime}
    (hU : IsOpen U) (hqpos : ∀ z ∈ U, 0 < q z) (hq : ContDiffOn ℝ ∞ q U)
    (hA : ∀ j, ContDiffOn ℝ ∞ (A j) U) (hP : ∀ j, ContDiffOn ℝ ∞ (P j) U)
    (hgmono : Monotone g) (hgtop : Tendsto g atTop atTop)
    (hbA : DiagonalJetBounds.CutStageBounds a q A g LA U)
    (hbP : DiagonalJetBounds.CutStageBounds a q P g LP U)
    (hlU : ∀ᶠ z in l, z ∈ U) (hqzero : Tendsto q l (𝓝 0))
    (hbg : ∀ J m, JetRate l q
      (SpatialCurl.spatialCurl (DiagonalJetBounds.uncutPrefix A (J + 1))) m (-Lbg m))
    (hres : ∀ J m, JetRate l q
      (fun z => navierStokesResidual
        (SpatialCurl.spatialCurl (DiagonalJetBounds.uncutPrefix A (J + 1)))
        (DiagonalJetBounds.uncutPrefix P (J + 1)) z.1 z.2) m (g J - Lres m)) :
    AllJetsFlat l q (fun z => navierStokesResidual
      (SolenoidalDiagonal.velocitySum a q A)
      (SolenoidalDiagonal.potentialSum a q P) z.1 z.2) := by
  have hlq : ∀ᶠ z in l, 0 < q z ∧ q z ≤ 1 := by
    filter_upwards [hlU, hqzero.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))]
      with z hz hq1
    exact ⟨hqpos z hz, hq1.le⟩
  have hprefixA (J : ℕ) :
      ContDiffOn ℝ ∞ (DiagonalJetBounds.uncutPrefix A (J + 1)) U :=
    ContDiffOn.sum (fun j _ => hA j)
  have hprefixP (J : ℕ) :
      ContDiffOn ℝ ∞ (DiagonalJetBounds.uncutPrefix P (J + 1)) U :=
    ContDiffOn.sum (fun j _ => hP j)
  have hvelocity (J : ℕ) : ContDiffOn ℝ ∞
      (SpatialCurl.spatialCurl (DiagonalJetBounds.uncutPrefix A (J + 1))) U := by
    intro z hz
    exact (SpatialCurl.contDiffAt_spatialCurl
      ((hprefixA J).contDiffAt (hU.mem_nhds hz)) (by simp)).contDiffWithinAt
  apply allJetsFlat_residual_of_stages
    (uStage := fun J => SpatialCurl.spatialCurl (DiagonalJetBounds.uncutPrefix A (J + 1)))
    (pStage := fun J => DiagonalJetBounds.uncutPrefix P (J + 1))
    (g := g) (Ltail := fun m => max (LA (m + 1)) (LP m))
    hU hlU hlq (SolenoidalDiagonal.velocitySum_contDiffOn ha hU hqpos hq hA)
    (SolenoidalDiagonal.potentialSum_contDiffOn ha hU hqpos hq hP)
    hvelocity hprefixP hgtop hbg ?_ ?_ hres
  · intro J m hm
    apply (jetRate_diagonal_velocity_tail ha hU hqpos hq hA hgmono hbA hlU hlq
      hqzero J m (by omega)).weaken hlq
    exact sub_le_sub (hgmono (Nat.le_succ J)) (le_max_left (LA (m + 1)) (LP m))
  · intro J m hm
    apply (jetRate_diagonal_tail ha hU hq hP hgmono hbP hlU hlq hqzero J m
      (by omega)).weaken hlq
    exact sub_le_sub (hgmono (Nat.le_succ J)) (le_max_right (LA (m + 1)) (LP m))

end DiagonalVelocity

end NavierStokes.DiagonalResidual
