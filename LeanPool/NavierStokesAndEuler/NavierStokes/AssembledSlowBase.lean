/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.GlobalSlowProfiles
public import LeanPool.NavierStokesAndEuler.NavierStokes.ParametricRadialExtension
public import LeanPool.NavierStokesAndEuler.NavierStokes.SlowBorelBase
public import LeanPool.NavierStokesAndEuler.NavierStokes.ReservedPatches
public import LeanPool.NavierStokesAndEuler.NavierStokes.NominalProfile
public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualSlowAxis
import LeanPool.NavierStokesAndEuler.NavierStokes.NaturalCoefficientBridge

/-!
# Assembling the actual global slow coefficients and their common base

All coefficient extensions in this module are constructed from the coherent
`GlobalSlowProfiles` sequence.  One parameter window is fixed before any
coefficient or derivative order is selected.
-/

@[expose] public section


noncomputable section

open Set Filter Function MeasureTheory
open scoped ContDiff Topology BigOperators

namespace NavierStokes.AssembledSlowBase

open GlobalSlowProfiles

/-- Common window, given by `ParametricRadialExtension.parameterWindow s.domain.isOpen hI`. -/
noncomputable def commonWindow {S : Set ℝ} {h C : ℝ} (s : Scheme S h C)
    (hI : Icc (-1 : ℝ) 1 ⊆ S) : ParametricRadialExtension.ParameterWindow S :=
  ParametricRadialExtension.parameterWindow s.domain.isOpen hI

/-- Extend even, given by `ParametricRadialExtension.extension w f f.smooth (fun _ heta R =>
f.even heta R)`. -/
noncomputable def extendEven {S : Set ℝ} (w : ParametricRadialExtension.ParameterWindow S)
    (f : EvenProfile S) : Field :=
  ParametricRadialExtension.extension w f f.smooth (fun _ heta R => f.even heta R)

theorem extendEven_contDiff {S : Set ℝ} (w : ParametricRadialExtension.ParameterWindow S)
    (f : EvenProfile S) : ContDiff ℝ ∞ (extendEven w f) :=
  ParametricRadialExtension.extension_contDiff w f.smooth (fun _ heta R => f.even heta R)

theorem extendEven_eq {S : Set ℝ} (w : ParametricRadialExtension.ParameterWindow S)
    (f : EvenProfile S) {p : ℝ × ℝ} (hX : 0 ≤ p.1) (heta : |p.2| ≤ w.inner) :
    extendEven w f p = xProfile f p :=
  ParametricRadialExtension.extension_eq w f.smooth (fun _ he R => f.even he R) hX heta

theorem extendEven_pullback {S : Set ℝ} (w : ParametricRadialExtension.ParameterWindow S)
    (f : EvenProfile S) (R : ℝ) {eta : ℝ} (heta : |eta| ≤ w.inner) :
    extendEven w f (R ^ 2 / 2, eta) = f (R, eta) :=
  ParametricRadialExtension.extension_pullback w f.smooth (fun _ he r => f.even he r) R heta

theorem extendEven_germ {S : Set ℝ} (w : ParametricRadialExtension.ParameterWindow S)
    (f : EvenProfile S) {p : ℝ × ℝ} (hX : 0 < p.1) (heta : |p.2| < w.inner) :
    extendEven w f =ᶠ[𝓝 p] xProfile f := by
  filter_upwards [(isOpen_Ioi.prod isOpen_Ioo).mem_nhds ⟨hX, abs_lt.mp heta⟩] with q hq
  exact extendEven_eq w f hq.1.le (abs_lt.mpr hq.2).le

theorem extendEven_right_jets {S : Set ℝ} (w : ParametricRadialExtension.ParameterWindow S)
    (f : EvenProfile S) (m : ℕ) {X eta : ℝ} (hX : 0 ≤ X) (heta : |eta| ≤ w.inner) :
    iteratedDeriv m (fun Y => extendEven w f (Y, eta)) X =
      iteratedDerivWithin m (fun Y => xProfile f (Y, eta)) (Ici 0) X :=
  ParametricRadialExtension.extension_radial_jets w f.smooth (fun _ he R => f.even he R) m hX heta

theorem extendEven_mixed_jets {S : Set ℝ} (w : ParametricRadialExtension.ParameterWindow S)
    (f : EvenProfile S) (m : ℕ) {p : ℝ × ℝ}
    (hp : p ∈ Ici 0 ×ˢ Ioo (-w.inner) w.inner) :
    iteratedFDeriv ℝ m (extendEven w f) p =
      iteratedFDerivWithin ℝ m (xProfile f) (Ici 0 ×ˢ Ioo (-w.inner) w.inner) p :=
  ParametricRadialExtension.extension_mixed_jets w f.smooth (fun _ he R => f.even he R) m hp

theorem extendEven_support {S : Set ℝ} (w : ParametricRadialExtension.ParameterWindow S)
    (f : EvenProfile S) {B : ℝ} (hB : 0 ≤ B) (hs : Exterior B S f) :
    tsupport (extendEven w f) ⊆ Icc (-1 : ℝ) (B ^ 2 / 2) ×ˢ Icc (-w.outer) w.outer :=
  ParametricRadialExtension.extension_tsupport w f.smooth (fun _ he R => f.even he R) hB hs

/-- For a profile already zero on a fixed axis neighborhood, remove the
unused negative-X extension without changing any physical value. -/
noncomputable def extendCoreZero {S : Set ℝ}
    (w : ParametricRadialExtension.ParameterWindow S) (r : ℝ) (f : EvenProfile S) (p : ℝ × ℝ) : ℝ :=
  TransportPrimitive.cutoff (r / 8) (r / 4) p.1 * extendEven w f p

theorem extendCoreZero_contDiff {S : Set ℝ}
    (w : ParametricRadialExtension.ParameterWindow S) (r : ℝ) (f : EvenProfile S) :
    ContDiff ℝ ∞ (extendCoreZero w r f) :=
  ((TransportPrimitive.cutoff_contDiff _ _).comp contDiff_fst).mul (extendEven_contDiff w f)

theorem extendCoreZero_eq {S : Set ℝ} (w : ParametricRadialExtension.ParameterWindow S)
    {r : ℝ} (hr : 0 < r) (f : EvenProfile S)
    (hz : ∀ eta ∈ S, ∀ R ∈ Icc 0 (Real.sqrt r), f (R, eta) = 0)
    {p : ℝ × ℝ} (hX : 0 ≤ p.1) (heta : |p.2| ≤ w.inner) :
    extendCoreZero w r f p = xProfile f p := by
  unfold extendCoreZero
  rw [extendEven_eq w f hX heta]
  by_cases hp : r / 4 ≤ p.1
  · rw [TransportPrimitive.cutoff_one (by linarith) hp, one_mul]
  · have heS : p.2 ∈ S := w.outer_subset (abs_lt.mp (heta.trans_lt w.inner_lt_outer))
    have hs : Real.sqrt (2 * p.1) ≤ Real.sqrt r := Real.sqrt_le_sqrt (by linarith)
    have hf := hz p.2 heS _ ⟨Real.sqrt_nonneg _, hs⟩
    change _ * f (Real.sqrt (2 * p.1), p.2) = f (Real.sqrt (2 * p.1), p.2)
    rw [hf, mul_zero]

theorem extendCoreZero_zero_left {S : Set ℝ}
    (w : ParametricRadialExtension.ParameterWindow S) {r : ℝ} (hr : 0 < r)
    (f : EvenProfile S) {p : ℝ × ℝ} (hp : p.1 ≤ r / 8) : extendCoreZero w r f p = 0 := by
  rw [extendCoreZero, TransportPrimitive.cutoff_zero (by linarith) hp, zero_mul]

theorem extendCoreZero_zero_right {S : Set ℝ}
    (w : ParametricRadialExtension.ParameterWindow S) (r : ℝ) (f : EvenProfile S)
    {B : ℝ} (hB : 0 ≤ B) (hs : Exterior B S f) {p : ℝ × ℝ} (hp : B ^ 2 / 2 ≤ p.1) :
    extendCoreZero w r f p = 0 := by
  rw [extendCoreZero, show extendEven w f p = 0 from
    ParametricRadialExtension.extension_zero_exterior w f.smooth
      (fun _ he R => f.even he R) hB hs hp, mul_zero]

theorem extendCoreZero_zero_parameter {S : Set ℝ}
    (w : ParametricRadialExtension.ParameterWindow S) (r : ℝ) (f : EvenProfile S)
    {p : ℝ × ℝ} (hp : w.outer ≤ |p.2|) : extendCoreZero w r f p = 0 := by
  rw [extendCoreZero, show extendEven w f p = 0 from
    ParametricRadialExtension.extension_zero_parameter w f.smooth
      (fun _ he R => f.even he R) hp, mul_zero]

/-- Each entry is an extension of the actual recursively repaired field. -/
noncomputable def extendedCoefficient {S : Set ℝ} {h C : ℝ} (s : Scheme S h C)
    (hI : Icc (-1 : ℝ) 1 ⊆ S) (n : ℕ) (i : Fin 4) : Field :=
  extendEven (commonWindow s hI) (component (profiles s n) i)

theorem extendedCoefficient_contDiff {S : Set ℝ} {h C : ℝ} (s : Scheme S h C)
    (hI : Icc (-1 : ℝ) 1 ⊆ S) (n : ℕ) (i : Fin 4) :
    ContDiff ℝ ∞ (extendedCoefficient s hI n i) :=
  extendEven_contDiff _ _

theorem extendedCoefficient_eq {S : Set ℝ} {h C : ℝ} (s : Scheme S h C)
    (hI : Icc (-1 : ℝ) 1 ⊆ S) (n : ℕ) (i : Fin 4) {p : ℝ × ℝ}
    (hX : 0 ≤ p.1) (heta : |p.2| ≤ 1) :
    extendedCoefficient s hI n i p = xProfile (component (profiles s n) i) p :=
  extendEven_eq _ _ hX (heta.trans (commonWindow s hI).one_lt_inner.le)

theorem extendedCoefficient_support {S : Set ℝ} {h C : ℝ} (s : Scheme S h C)
    (hI : Icc (-1 : ℝ) 1 ⊆ S) {n : ℕ} (hn : 0 < n) (i : Fin 4) :
    tsupport (extendedCoefficient s hI n i) ⊆
      Icc (-1 : ℝ) (s.B ^ 2 / 2) ×ˢ Icc (-(commonWindow s hI).outer) (commonWindow s hI).outer := by
  apply extendEven_support _ _ s.B_pos.le
  fin_cases i
  · exact profiles_phi_exterior s hn
  · exact profiles_axial_exterior s n
  · exact profiles_beta_exterior s n
  · exact profiles_pressure_exterior s hn

theorem extendedCoefficient_compactSupport {S : Set ℝ} {h C : ℝ} (s : Scheme S h C)
    (hI : Icc (-1 : ℝ) 1 ⊆ S) {n : ℕ} (hn : 0 < n) (i : Fin 4) :
    HasCompactSupport (extendedCoefficient s hI n i) :=
  (isCompact_Icc.prod isCompact_Icc).of_isClosed_subset isClosed_closure
    (extendedCoefficient_support s hI hn i)

theorem extendedCoefficient_zero_exterior {S : Set ℝ} {h C : ℝ} (s : Scheme S h C)
    (hI : Icc (-1 : ℝ) 1 ⊆ S) {n : ℕ} (hn : 0 < n) (i : Fin 4) {p : ℝ × ℝ}
    (hp : s.B ^ 2 / 2 ≤ p.1) : extendedCoefficient s hI n i p = 0 := by
  apply ParametricRadialExtension.extension_zero_exterior _
    (component (profiles s n) i).smooth (fun _ he R => (component (profiles s n) i).even he R)
    s.B_pos.le _ hp
  fin_cases i
  · exact profiles_phi_exterior s hn
  · exact profiles_axial_exterior s n
  · exact profiles_beta_exterior s n
  · exact profiles_pressure_exterior s hn

theorem extendedCoefficient_inner {S : Set ℝ} {h C rho inner : ℝ} {U : Set ℂ}
    {base : Fin 5 → SimilarityProfile.InnerProfile} {s : Scheme S h C}
    {A : SlowRecursion.LocalHierarchy rho U h C base}
    (L : Localization s A inner) (B0 : BaseAgreement s A inner)
    (hI : Icc (-1 : ℝ) 1 ⊆ S) {n : ℕ} (hn : 0 < n) (i : Fin 4) {p : ℝ × ℝ}
    (hX : 0 ≤ p.1) (hi : p.1 < inner) (heta : |p.2| ≤ 1) :
    extendedCoefficient s hI n i p = SlowRecursion.profile (A.coefficients n (localIndex i)) p := by
  rw [extendedCoefficient_eq s hI n i hX heta]
  exact profiles_inner_eq L B0 hn i hX hi (hI (abs_le.mp heta))

theorem extendedCoefficient_axis {S : Set ℝ} {h C rho inner : ℝ} {U : Set ℂ}
    {base : Fin 5 → SimilarityProfile.InnerProfile} {s : Scheme S h C}
    {A : SlowRecursion.LocalHierarchy rho U h C base}
    (L : Localization s A inner) (B0 : BaseAgreement s A inner)
    (hI : Icc (-1 : ℝ) 1 ⊆ S) {n : ℕ} (hn : 0 < n) (i : Fin 4) {eta : ℝ}
    (heta : |eta| ≤ 1) : extendedCoefficient s hI n i (0, eta) = 0 := by
  rw [extendedCoefficient_eq s hI n i le_rfl heta]
  change component (profiles s n) i (Real.sqrt (2 * 0), eta) = 0
  rw [mul_zero, Real.sqrt_zero]
  exact profiles_axis_zero L B0 hn i (hI (abs_le.mp heta))

theorem extendedCoefficient_axis_jets {S : Set ℝ} {h C rho inner : ℝ} {U : Set ℂ}
    {base : Fin 5 → SimilarityProfile.InnerProfile} {s : Scheme S h C}
    {A : SlowRecursion.LocalHierarchy rho U h C base}
    (L : Localization s A inner) (B0 : BaseAgreement s A inner)
    (hI : Icc (-1 : ℝ) 1 ⊆ S) {n : ℕ} (hn : 0 < n) (i : Fin 4) (m : ℕ) {eta : ℝ}
    (heta : |eta| ≤ 1) :
    iteratedDeriv m (fun X => extendedCoefficient s hI n i (X, eta)) 0 =
      iteratedDerivWithin m (fun X => SlowRecursion.profile (A.coefficients n (localIndex i)) (X,
          eta))
        (Ici 0) 0 := by
  unfold extendedCoefficient
  rw [extendEven_right_jets _ _ m le_rfl (heta.trans (commonWindow s hI).one_lt_inner.le)]
  exact profiles_axis_right_jets L B0 hn i m (hI (abs_le.mp heta))

/-- A profile smooth on a neighborhood of the nonnegative X half-plane
gives a genuine globally signed-radius even field by polynomial pullback. -/
noncomputable def radialPullback {S : Set ℝ} {D : Set (ℝ × ℝ)} (F : Field)
    (hF : ContDiffOn ℝ ∞ F D) (hD : ∀ X, 0 ≤ X → ∀ eta ∈ S, (X, eta) ∈ D) : EvenProfile S :=
  ⟨fun w => F (w.1 ^ 2 / 2, w.2), ⟨hF.comp
    (((contDiffOn_fst.pow 2).div_const 2).prodMk contDiffOn_snd)
    (fun w hw => hD _ (by positivity) _ hw.2),
    fun _ _ R => by simp only [neg_sq]⟩⟩

theorem radialPullback_xProfile {S : Set ℝ} {D : Set (ℝ × ℝ)} (F : Field)
    (hF : ContDiffOn ℝ ∞ F D) (hD : ∀ X, 0 ≤ X → ∀ eta ∈ S, (X, eta) ∈ D)
    {p : ℝ × ℝ} (hX : 0 ≤ p.1) : xProfile (radialPullback F hF hD) p = F p := by
  change F ((Real.sqrt (2 * p.1)) ^ 2 / 2, p.2) = F p
  rw [Real.sq_sqrt (mul_nonneg (by norm_num) hX)]
  congr 1
  ext
  · dsimp
    ring
  · rfl

theorem coefficient_smoothAt {S : Set ℝ} {h C : ℝ} (s : Scheme S h C)
    (n : ℕ) {w : ℝ × ℝ} (hX : 0 < w.1) (heta : w.2 ∈ S) :
    ContDiffAt ℝ ∞ (SlowExpansionResidual.angularCoefficient h (asSlowProfiles s) n) w ∧
    ContDiffAt ℝ ∞ (SlowExpansionResidual.axialCoefficient h (asSlowProfiles s) n) w := by
  have hu (j : ℕ) : ContDiffAt ℝ ∞ ((asSlowProfiles s).axial j) w :=
    xProfile_contDiffAt s.domain.isOpen _ hX heta
  have hf (j : ℕ) : ContDiffAt ℝ ∞ ((asSlowProfiles s).phi j) w :=
    xProfile_contDiffAt s.domain.isOpen _ hX heta
  have hv (j : ℕ) : ContDiffAt ℝ ∞ ((asSlowProfiles s).flux j) w :=
    contDiffAt_fst.mul (xProfile_contDiffAt s.domain.isOpen _ hX heta)
  have hp (j : ℕ) : ContDiffAt ℝ ∞ ((asSlowProfiles s).pressure j) w :=
    xProfile_contDiffAt s.domain.isOpen _ hX heta
  have hL : CoordinateAlgebra.L h w.2 ≠ 0 := s.domain.denominator w.2 heta
  exact ⟨SlowResidualMatching.transportCoefficient_smoothAt _ _ _ _ _ _ _ _ n
    (fun j _ => hv j) (fun j _ => hu j) (fun j _ => hf j) contDiffAt_const hX.ne' hL,
    SlowResidualMatching.transportCoefficient_smoothAt _ _ _ _ _ _ _ _ n
      (fun j _ => hv j) (fun j _ => hu j) (fun j _ => hu j)
      (AxisSourceRegularity.Z_smooth _ _ (hp n) hL) hX.ne' hL⟩

/-- A positive radial weight removes the irrelevant value of a coefficient
at X=0. Vanishing on a genuine core then gives joint smoothness there. -/
theorem weightedRadius_smooth {S : Set ℝ} (hS : IsOpen S) {r : ℝ} (hr : 0 < r)
    {F : Field} (hF : ∀ w, 0 < w.1 → w.2 ∈ S → ContDiffAt ℝ ∞ F w)
    (hz : ∀ w, 0 < w.1 → w.1 < r → w.2 ∈ S → F w = 0)
    {m : ℕ} (hm : m ≠ 0) :
    Smooth S (fun w => w.1 ^ m * F (w.1 ^ 2 / 2, w.2)) := by
  intro w hw
  apply ContDiffAt.contDiffWithinAt
  by_cases hw0 : w.1 = 0
  · apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
    have hn : ∀ᶠ p : ℝ × ℝ in 𝓝 w, p.1 ^ 2 / 2 < r ∧ p.2 ∈ S :=
      (isOpen_lt (((continuous_fst.pow 2).div_const 2)) continuous_const).inter
        (hS.preimage continuous_snd) |>.mem_nhds ⟨by simpa [hw0] using hr, hw.2⟩
    filter_upwards [hn] with p hp
    by_cases hp0 : p.1 = 0
    · simp [hp0, hm]
    · rw [hz (p.1 ^ 2 / 2, p.2) (div_pos (sq_pos_of_ne_zero hp0) (by norm_num)) hp.1 hp.2, mul_zero]
  · exact (contDiffAt_fst.pow m).mul ((hF (w.1 ^ 2 / 2, w.2)
      (div_pos (sq_pos_of_ne_zero hw0) (by norm_num)) hw.2).comp w
        (((contDiffAt_fst.pow 2).div_const 2).prodMk contDiffAt_snd))

/-- The remaining finite order-zero input. Positive-order equations are
proved by `GlobalSlowProfiles` and are not fields of this proposition. -/
structure ZeroOrderSolved {S : Set ℝ} {h C : ℝ} (s : Scheme S h C) (r : ℝ) : Prop where
  angular : ∀ w, 0 < w.1 → w.1 < r → w.2 ∈ S →
    SlowExpansionResidual.angularCoefficient h (asSlowProfiles s) 0 w = 0
  axial : ∀ w, 0 < w.1 → w.1 < r → w.2 ∈ S →
    SlowExpansionResidual.axialCoefficient h (asSlowProfiles s) 0 w = 0

section StressConstruction

variable {S : Set ℝ} {h C rho inner : ℝ} {U : Set ℂ}
  {base : Fin 5 → SimilarityProfile.InnerProfile} {s : Scheme S h C}
  {A : SlowRecursion.LocalHierarchy rho U h C base}
  (L : Localization s A inner) (B0 : BaseAgreement s A inner)

include L B0

theorem coefficients_zero_inner (Z0 : ZeroOrderSolved s inner) (n : ℕ)
    {w : ℝ × ℝ} (hX : 0 < w.1) (hi : w.1 < inner) (heta : w.2 ∈ S) :
    SlowExpansionResidual.angularCoefficient h (asSlowProfiles s) n w = 0 ∧
    SlowExpansionResidual.axialCoefficient h (asSlowProfiles s) n w = 0 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨Z0.angular w hX hi heta, Z0.axial w hX hi heta⟩
  · exact profiles_inner_tangential L B0 hn hX hi heta

theorem thetaDensity_smooth (Z0 : ZeroOrderSolved s inner) (n : ℕ) :
    Smooth S (SlowResidualMatching.thetaDensity h C (asSlowProfiles s) n) := by
  have hs := weightedRadius_smooth s.domain.isOpen L.inner_pos
    (F := SlowExpansionResidual.angularCoefficient h (asSlowProfiles s) n)
    (fun w hx he => (coefficient_smoothAt s n hx he).1)
    (fun w hx hi he => (coefficients_zero_inner L B0 Z0 n hx hi he).1) (m := 3) (by norm_num)
  convert! hs.div_const C using 1
  ext w
  dsimp [SlowResidualMatching.thetaDensity, SlowResidualMatching.radiusPoint]
  ring

theorem zDensity_smooth (Z0 : ZeroOrderSolved s inner) (n : ℕ) :
    Smooth S (SlowResidualMatching.zDensity h (asSlowProfiles s) n) := by
  have hs := weightedRadius_smooth s.domain.isOpen L.inner_pos
    (F := SlowExpansionResidual.axialCoefficient h (asSlowProfiles s) n)
    (fun w hx he => (coefficient_smoothAt s n hx he).2)
    (fun w hx hi he => (coefficients_zero_inner L B0 Z0 n hx hi he).2) (m := 1) (by norm_num)
  simp only [pow_one] at hs ⊢
  exact hs

theorem densities_zero_inner (Z0 : ZeroOrderSolved s inner) (n : ℕ)
    {R eta : ℝ} (hR : R ∈ Icc 0 (Real.sqrt inner)) (heta : eta ∈ S) :
    SlowResidualMatching.thetaDensity h C (asSlowProfiles s) n (R, eta) = 0 ∧
    SlowResidualMatching.zDensity h (asSlowProfiles s) n (R, eta) = 0 := by
  by_cases hR0 : R = 0
  · simp [SlowResidualMatching.thetaDensity, SlowResidualMatching.zDensity, hR0]
  · have hRsq : R ^ 2 ≤ inner := by
      calc
        R ^ 2 ≤ (Real.sqrt inner) ^ 2 := (sq_le_sq₀ hR.1 (Real.sqrt_nonneg _)).2 hR.2
        _ = inner := Real.sq_sqrt L.inner_pos.le
    have hx : 0 < R ^ 2 / 2 := div_pos (sq_pos_of_ne_zero hR0) (by norm_num)
    have hi : R ^ 2 / 2 < inner := by linarith [L.inner_pos]
    have hz := coefficients_zero_inner L B0 Z0 n (w := (R ^ 2 / 2, eta)) hx hi heta
    simp only [SlowResidualMatching.thetaDensity, SlowResidualMatching.zDensity,
      SlowResidualMatching.radiusPoint, hz.1, hz.2, mul_zero]
    trivial

/-- Theta even, constructed using `evenCorrection`. -/
noncomputable def thetaEven (Z0 : ZeroOrderSolved s inner) (n : ℕ) : EvenProfile S :=
  evenCorrection (SlowStressSupport.stress_smooth s.domain.isOpen
    (thetaDensity_smooth L B0 Z0 n) 2 (Real.sqrt_pos.2 L.inner_pos)
    (fun _ he _ hR => (densities_zero_inner L B0 Z0 n hR he).1))

/-- Z even, constructed using `evenCorrection`. -/
noncomputable def zEven (Z0 : ZeroOrderSolved s inner) (n : ℕ) : EvenProfile S :=
  evenCorrection (SlowStressSupport.stress_smooth s.domain.isOpen
    (zDensity_smooth L B0 Z0 n) 1 (Real.sqrt_pos.2 L.inner_pos)
    (fun _ he _ hR => (densities_zero_inner L B0 Z0 n hR he).2))

theorem thetaEven_eq (Z0 : ZeroOrderSolved s inner) (n : ℕ) {R eta : ℝ}
    (hR : 0 ≤ R) :
    thetaEven L B0 Z0 n (R, eta) =
      SlowStressSupport.stress 2 (SlowResidualMatching.thetaDensity h C (asSlowProfiles s) n) (R,
          eta) := by
  change _ + SlowStressSupport.stress 2 _ (-R, eta) = _
  simp only [SlowStressSupport.stress, ite_eq_right (by linarith : ¬0 < -R), add_zero]

theorem zEven_eq (Z0 : ZeroOrderSolved s inner) (n : ℕ) {R eta : ℝ}
    (hR : 0 ≤ R) :
    zEven L B0 Z0 n (R, eta) =
      SlowStressSupport.stress 1 (SlowResidualMatching.zDensity h (asSlowProfiles s) n) (R, eta) :=
          by
  change _ + SlowStressSupport.stress 1 _ (-R, eta) = _
  simp only [SlowStressSupport.stress, ite_eq_right (by linarith : ¬0 < -R), add_zero]

theorem thetaEven_zero (Z0 : ZeroOrderSolved s inner) (n : ℕ) {R eta : ℝ}
    (hR : R ∈ Icc 0 (Real.sqrt inner)) (heta : eta ∈ S) : thetaEven L B0 Z0 n (R, eta) = 0 := by
  rw [thetaEven_eq L B0 Z0 n hR.1]
  exact SlowStressSupport.stress_inner 2
    (fun _ he _ hr => (densities_zero_inner L B0 Z0 n hr he).1) hR.2 heta

theorem zEven_zero (Z0 : ZeroOrderSolved s inner) (n : ℕ) {R eta : ℝ}
    (hR : R ∈ Icc 0 (Real.sqrt inner)) (heta : eta ∈ S) : zEven L B0 Z0 n (R, eta) = 0 := by
  rw [zEven_eq L B0 Z0 n hR.1]
  exact SlowStressSupport.stress_inner 1
    (fun _ he _ hr => (densities_zero_inner L B0 Z0 n hr he).2) hR.2 heta

/-- Coefficients, bundling `axial`, `phi`, `pressure`, `stressTheta` and the required
compatibility proofs. -/
noncomputable def coefficients (Z0 : ZeroOrderSolved s inner)
    (hI : Icc (-1 : ℝ) 1 ⊆ S) : SlowBorelBase.Coefficients where
  axial := fun n => extendedCoefficient s hI n 1
  phi := fun n => extendedCoefficient s hI n 0
  pressure := fun n => extendedCoefficient s hI n 3
  stressTheta := fun n => extendCoreZero (commonWindow s hI) inner (thetaEven L B0 Z0 n)
  stressAxial := fun n => extendCoreZero (commonWindow s hI) inner (zEven L B0 Z0 n)

theorem coefficients_smooth (Z0 : ZeroOrderSolved s inner)
    (hI : Icc (-1 : ℝ) 1 ⊆ S) : SlowBorelBase.SmoothCoefficients (coefficients L B0 Z0 hI) :=
  ⟨fun _ => extendedCoefficient_contDiff _ _ _ _,
   fun _ => extendedCoefficient_contDiff _ _ _ _,
   fun _ => extendedCoefficient_contDiff _ _ _ _,
   fun _ => extendCoreZero_contDiff _ _ _, fun _ => extendCoreZero_contDiff _ _ _⟩

theorem coefficients_fields_eq (Z0 : ZeroOrderSolved s inner)
    (hI : Icc (-1 : ℝ) 1 ⊆ S) (n : ℕ) {p : ℝ × ℝ}
    (hX : 0 ≤ p.1) (heta : |p.2| ≤ 1) :
    (coefficients L B0 Z0 hI).phi n p = (asSlowProfiles s).phi n p ∧
    (coefficients L B0 Z0 hI).axial n p = (asSlowProfiles s).axial n p ∧
    (coefficients L B0 Z0 hI).pressure n p = (asSlowProfiles s).pressure n p :=
  ⟨extendedCoefficient_eq s hI n 0 hX heta, extendedCoefficient_eq s hI n 1 hX heta,
    extendedCoefficient_eq s hI n 3 hX heta⟩

theorem coefficients_fields_germ (Z0 : ZeroOrderSolved s inner)
    (hI : Icc (-1 : ℝ) 1 ⊆ S) (n : ℕ) {p : ℝ × ℝ}
    (hX : 0 < p.1) (heta : |p.2| ≤ 1) :
    (coefficients L B0 Z0 hI).phi n =ᶠ[𝓝 p] (asSlowProfiles s).phi n ∧
    (coefficients L B0 Z0 hI).axial n =ᶠ[𝓝 p] (asSlowProfiles s).axial n ∧
    (coefficients L B0 Z0 hI).pressure n =ᶠ[𝓝 p] (asSlowProfiles s).pressure n :=
  ⟨extendEven_germ _ _ hX (heta.trans_lt (commonWindow s hI).one_lt_inner),
    extendEven_germ _ _ hX (heta.trans_lt (commonWindow s hI).one_lt_inner),
    extendEven_germ _ _ hX (heta.trans_lt (commonWindow s hI).one_lt_inner)⟩

theorem coefficients_stress_eq (Z0 : ZeroOrderSolved s inner)
    (hI : Icc (-1 : ℝ) 1 ⊆ S) (n : ℕ) {w : ℝ × ℝ}
    (hX : 0 ≤ w.1) (heta : |w.2| ≤ 1) :
    (coefficients L B0 Z0 hI).stressTheta n w = SlowResidualMatching.thetaStress h C
        (asSlowProfiles s) n w ∧
    (coefficients L B0 Z0 hI).stressAxial n w = SlowResidualMatching.zStress h (asSlowProfiles s) n
        w := by
  constructor
  · change extendCoreZero _ _ _ w = _
    rw [extendCoreZero_eq _ L.inner_pos _ (fun _ he _ hr => thetaEven_zero L B0 Z0 n hr he)
      hX (heta.trans (commonWindow s hI).one_lt_inner.le)]
    exact thetaEven_eq L B0 Z0 n (Real.sqrt_nonneg _)
  · change extendCoreZero _ _ _ w = _
    rw [extendCoreZero_eq _ L.inner_pos _ (fun _ he _ hr => zEven_zero L B0 Z0 n hr he)
      hX (heta.trans (commonWindow s hI).one_lt_inner.le)]
    exact zEven_eq L B0 Z0 n (Real.sqrt_nonneg _)

theorem coefficients_stress_zero_left (Z0 : ZeroOrderSolved s inner)
    (hI : Icc (-1 : ℝ) 1 ⊆ S) (n : ℕ) {w : ℝ × ℝ} (hw : w.1 ≤ inner / 8) :
    (coefficients L B0 Z0 hI).stressTheta n w = 0 ∧
    (coefficients L B0 Z0 hI).stressAxial n w = 0 :=
  ⟨extendCoreZero_zero_left _ L.inner_pos _ hw, extendCoreZero_zero_left _ L.inner_pos _ hw⟩

theorem coefficients_stress_zero_right (Z0 : ZeroOrderSolved s inner)
    (hI : Icc (-1 : ℝ) 1 ⊆ S) (n : ℕ) {B : ℝ} (hB : 0 ≤ B)
    (hTheta : Exterior B S (SlowStressSupport.stress 2
      (SlowResidualMatching.thetaDensity h C (asSlowProfiles s) n)))
    (hZ : Exterior B S (SlowStressSupport.stress 1
      (SlowResidualMatching.zDensity h (asSlowProfiles s) n)))
    {w : ℝ × ℝ} (hw : B ^ 2 / 2 ≤ w.1) :
    (coefficients L B0 Z0 hI).stressTheta n w = 0 ∧
    (coefficients L B0 Z0 hI).stressAxial n w = 0 := by
  constructor
  · apply extendCoreZero_zero_right _ _ _ hB _ hw
    intro eta he R hR
    rw [thetaEven_eq L B0 Z0 n (hB.trans hR)]
    exact hTheta eta he R hR
  · apply extendCoreZero_zero_right _ _ _ hB _ hw
    intro eta he R hR
    rw [zEven_eq L B0 Z0 n (hB.trans hR)]
    exact hZ eta he R hR

theorem coefficients_stress_zero_parameter (Z0 : ZeroOrderSolved s inner)
    (hI : Icc (-1 : ℝ) 1 ⊆ S) (n : ℕ) {w : ℝ × ℝ}
    (hw : (commonWindow s hI).outer ≤ |w.2|) :
    (coefficients L B0 Z0 hI).stressTheta n w = 0 ∧
    (coefficients L B0 Z0 hI).stressAxial n w = 0 :=
  ⟨extendCoreZero_zero_parameter _ _ _ hw, extendCoreZero_zero_parameter _ _ _ hw⟩

theorem coefficients_stress_support (Z0 : ZeroOrderSolved s inner)
    (hI : Icc (-1 : ℝ) 1 ⊆ S) (n : ℕ) {B : ℝ} (hB : 0 ≤ B)
    (hTheta : Exterior B S (SlowStressSupport.stress 2
      (SlowResidualMatching.thetaDensity h C (asSlowProfiles s) n)))
    (hZ : Exterior B S (SlowStressSupport.stress 1
      (SlowResidualMatching.zDensity h (asSlowProfiles s) n))) :
    tsupport (fun w => ((coefficients L B0 Z0 hI).stressTheta n w,
        (coefficients L B0 Z0 hI).stressAxial n w)) ⊆
      Icc (inner / 8) (B ^ 2 / 2) ×ˢ Icc (-(commonWindow s hI).outer) (commonWindow s hI).outer :=
          by
  apply closure_minimal _ (isClosed_Icc.prod isClosed_Icc)
  intro w hw
  have hn : ((coefficients L B0 Z0 hI).stressTheta n w,
      (coefficients L B0 Z0 hI).stressAxial n w) ≠ 0 := hw
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · by_contra hh
    have hz := coefficients_stress_zero_left L B0 Z0 hI n (le_of_not_ge hh)
    exact hn (Prod.ext hz.1 hz.2)
  · by_contra hh
    have hz := coefficients_stress_zero_right L B0 Z0 hI n hB hTheta hZ (le_of_not_ge hh)
    exact hn (Prod.ext hz.1 hz.2)
  · apply abs_le.mp
    by_contra hh
    have hz := coefficients_stress_zero_parameter L B0 Z0 hI n (le_of_not_ge hh)
    exact hn (Prod.ext hz.1 hz.2)

theorem coefficients_stress_zero (Z0 : ZeroOrderSolved s inner)
    (hI : Icc (-1 : ℝ) 1 ⊆ S) (n : ℕ) {w : ℝ × ℝ}
    (hX : 0 ≤ w.1) (hi : w.1 ≤ inner / 2) (heta : |w.2| ≤ 1) :
    (coefficients L B0 Z0 hI).stressTheta n w = 0 ∧
    (coefficients L B0 Z0 hI).stressAxial n w = 0 := by
  rw [(coefficients_stress_eq L B0 Z0 hI n hX heta).1,
    (coefficients_stress_eq L B0 Z0 hI n hX heta).2]
  have hr : Real.sqrt (2 * w.1) ≤ Real.sqrt inner :=
    Real.sqrt_le_sqrt (by linarith)
  exact ⟨SlowStressSupport.stress_inner 2
    (fun _ he _ hR => (densities_zero_inner L B0 Z0 n hR he).1) hr (hI (abs_le.mp heta)),
    SlowStressSupport.stress_inner 1
    (fun _ he _ hR => (densities_zero_inner L B0 Z0 n hR he).2) hr (hI (abs_le.mp heta))⟩

theorem coefficients_common_zero_core (Z0 : ZeroOrderSolved s inner)
    (hI : Icc (-1 : ℝ) 1 ⊆ S) :
    ∃ r : ℝ, 0 < r ∧ ∀ n : ℕ, ∀ X ∈ Ico 0 r, ∀ eta ∈ Icc (-1 : ℝ) 1,
      (coefficients L B0 Z0 hI).stressTheta n (X, eta) = 0 ∧
      (coefficients L B0 Z0 hI).stressAxial n (X, eta) = 0 :=
  ⟨inner / 2, half_pos L.inner_pos, fun n _ hX _ he =>
    coefficients_stress_zero L B0 Z0 hI n hX.1 hX.2.le (abs_le.mpr he)⟩

/-- One actual coefficient family gives one schedule and one smooth
divergence-free physical base. No scale bounds are supplied as hypotheses. -/
theorem exists_assembled_base (Z0 : ZeroOrderSolved s inner)
    (hI : Icc (-1 : ℝ) 1 ⊆ S) (hh : 0 < h) (hh1 : h < 1 / 2)
    (lo hi : ℝ) (N : ℕ) :
    ∃ a : ℕ → ℕ, N ≤ a 0 ∧
      SlowBorelBase.AdmissibleScales h (SlowBorelBase.coefficientBundle C (coefficients L B0 Z0 hI))
        (SlowBorelBase.innerBox lo hi) a ∧
      ContDiffOn ℝ ∞ (SlowBorelBase.baseVelocity a h C (coefficients L B0 Z0 hI))
        (Iio 1 ×ˢ (univ : Set ProblemStatement.Space)) ∧
      ∀ t : ℝ, t < 1 → ∀ x : ProblemStatement.Space,
        ProblemStatement.spatialDivergence (SlowBorelBase.baseVelocity a h C (coefficients L B0 Z0
            hI)) t x = 0 :=
  SlowBorelBase.exists_base_fields hh hh1 (coefficients_smooth L B0 Z0 hI) C lo hi N

end StressConstruction

section ActualFlux

variable {S : Set ℝ}

theorem massHistory_extendEven (w : ParametricRadialExtension.ParameterWindow S)
    (u : EvenProfile S) {R eta : ℝ} (hR : 0 ≤ R) (heta : |eta| ≤ w.inner) :
    PositiveOrderMoments.massHistory u (R, eta) =
      ProfileHistories.primitive (extendEven w u) (R ^ 2 / 2, eta) := by
  apply massHistory_of_composition u _ hR
  · exact ((extendEven_contDiff w u).continuous.comp (continuous_id.prodMk
      continuous_const)).continuousOn
  · intro r _
    exact (extendEven_pullback w u r heta).symm

theorem parameterMassHistory_extendEven (hS : IsOpen S)
    (w : ParametricRadialExtension.ParameterWindow S)
    (u : EvenProfile S) {R eta : ℝ} (hR : 0 ≤ R) (heta : |eta| < w.inner) :
    PositiveOrderMoments.parameterMassHistory u (R, eta) =
      ProfileHistories.primitive (ProfileHistories.parameterPartial (extendEven w u)) (R ^ 2 / 2,
          eta) := by
  have heS : eta ∈ S := w.outer_subset (abs_lt.mp (heta.trans w.inner_lt_outer))
  have hmass := ProfileHistories.primitive_smooth (PositiveOrderMoments.parameterDomain S hS)
    (contDiffOn_fst.mul u.smooth)
  have hd := parameter_derivative hS hmass heS R
  change HasDerivAt (fun t => PositiveOrderMoments.massHistory u (R, t))
    (ProfileHistories.parameterPartial (PositiveOrderMoments.massHistory u) (R, eta)) eta at hd
  rw [PositiveOrderMoments.massHistory_parameterPartial_on hS u.smooth heS] at hd
  have hp := ProfileHistories.parameterPartial_hasDerivAt SlowBorelBase.globalRadialDomain
    (SlowBorelBase.primitive_smooth (extendEven_contDiff w u)).contDiffOn
    (p := (R ^ 2 / 2, eta)) (mem_univ _)
  rw [ProfileHistories.parameterPartial_primitive SlowBorelBase.globalRadialDomain
    (extendEven_contDiff w u).contDiffOn (mem_univ _)] at hp
  have he : (fun t => PositiveOrderMoments.massHistory u (R, t)) =ᶠ[𝓝 eta]
      fun t => ProfileHistories.primitive (extendEven w u) (R ^ 2 / 2, t) := by
    filter_upwards [(isOpen_Ioo.mem_nhds (abs_lt.mp heta))] with t ht
    exact massHistory_extendEven w u hR (abs_lt.mpr ht).le
  exact hd.unique (hp.congr_of_eventuallyEq he)

theorem fluxHistory_extendEven {h : ℝ} (d : Domain S h)
    (w : ParametricRadialExtension.ParameterWindow S) (lam : ℝ)
    (u : EvenProfile S) {R eta : ℝ} (hR : 0 ≤ R) (heta : |eta| < w.inner) :
    PositiveOrderMoments.fluxHistory h lam u (R, eta) =
      SlowDivergence.radialFlux h lam (extendEven w u) (R ^ 2 / 2, eta) := by
  rw [SlowDivergence.radialFlux_eq_histories SlowBorelBase.globalRadialDomain
    (extendEven_contDiff w u).contDiffOn h lam (mem_univ _),
    PositiveOrderMoments.fluxHistory, massHistory_extendEven w u hR heta.le,
    parameterMassHistory_extendEven d.isOpen w u hR heta,
    extendEven_pullback w u R heta.le]
  simp only [PositiveAxisSystem.dScale, CoordinateAlgebra.D, PositiveAxisSystem.edge,
    CoordinateAlgebra.d, PositiveAxisSystem.ell, CoordinateAlgebra.L]
  ring

/-- The extended regular quotient is the actual radial flux of the
extended axial coefficient. The identity includes X=0. -/
theorem betaFromU_extended {h : ℝ} (d : Domain S h)
    (w : ParametricRadialExtension.ParameterWindow S) (lam : ℝ) (u : EvenProfile S)
    {p : ℝ × ℝ} (hX : 0 ≤ p.1) (heta : |p.2| < w.inner) :
    p.1 * extendEven w (betaFromU d lam u) p = SlowDivergence.radialFlux h lam (extendEven w u) p
        := by
  have heS : p.2 ∈ S := w.outer_subset (abs_lt.mp (heta.trans w.inner_lt_outer))
  have hr : (Real.sqrt (2 * p.1)) ^ 2 / 2 = p.1 := by
    rw [Real.sq_sqrt (mul_nonneg (by norm_num) hX)]
    ring
  rw [extendEven_eq w (betaFromU d lam u) hX heta.le]
  change p.1 * betaFromU d lam u (Real.sqrt (2 * p.1), p.2) = _
  calc
    _ = (Real.sqrt (2 * p.1)) ^ 2 / 2 * betaFromU d lam u (Real.sqrt (2 * p.1), p.2) := by rw [hr]
    _ = PositiveOrderMoments.fluxHistory h lam u (Real.sqrt (2 * p.1), p.2) :=
      betaFromU_eq_fluxHistory d lam u (w := (Real.sqrt (2 * p.1), p.2)) heS
    _ = SlowDivergence.radialFlux h lam (extendEven w u) ((Real.sqrt (2 * p.1)) ^ 2 / 2, p.2) :=
      fluxHistory_extendEven d w lam u (Real.sqrt_nonneg _) heta
    _ = _ := by rw [hr]

theorem extended_flux {h C : ℝ} (s : Scheme S h C) (hI : Icc (-1 : ℝ) 1 ⊆ S)
    {n : ℕ} (hn : 0 < n) {p : ℝ × ℝ} (hX : 0 ≤ p.1) (heta : |p.2| ≤ 1) :
    p.1 * extendedCoefficient s hI n 2 p =
      SlowDivergence.radialFlux h (AxisSourceRegularity.slowOrder h n)
        (extendedCoefficient s hI n 1) p := by
  change p.1 * extendEven (commonWindow s hI) (profiles s n).beta p =
    SlowDivergence.radialFlux h _ (extendEven (commonWindow s hI) (profiles s n).axial) p
  rw [profiles_beta_eq s hn]
  exact betaFromU_extended s.domain _ _ _ hX (heta.trans_lt (commonWindow s hI).one_lt_inner)

theorem extended_flux_zero {h C : ℝ} (s : Scheme S h C) (hI : Icc (-1 : ℝ) 1 ⊆ S)
    (hbase : s.base.beta = betaFromU s.domain 0 s.base.axial)
    {p : ℝ × ℝ} (hX : 0 ≤ p.1) (heta : |p.2| ≤ 1) :
    p.1 * extendedCoefficient s hI 0 2 p =
      SlowDivergence.radialFlux h 0 (extendedCoefficient s hI 0 1) p := by
  change p.1 * extendEven (commonWindow s hI) (profiles s 0).beta p =
    SlowDivergence.radialFlux h 0 (extendEven (commonWindow s hI) (profiles s 0).axial) p
  rw [profiles_zero, hbase]
  exact betaFromU_extended s.domain _ _ _ hX (heta.trans_lt (commonWindow s hI).one_lt_inner)

/-- The repaired mass row makes the actual positive-order stream primitive
zero outside the common support radius. -/
theorem extended_axial_primitive_zero {h C : ℝ} (s : Scheme S h C)
    (hI : Icc (-1 : ℝ) 1 ⊆ S) {n : ℕ} (hn : 0 < n) {p : ℝ × ℝ}
    (hX : s.B ^ 2 / 2 ≤ p.1) (heta : |p.2| ≤ 1) :
    ProfileHistories.primitive (extendedCoefficient s hI n 1) p = 0 := by
  have hXp : 0 ≤ p.1 := (by positivity : 0 ≤ s.B ^ 2 / 2).trans hX
  have hr2 : (Real.sqrt (2 * p.1)) ^ 2 / 2 = p.1 := by
    rw [Real.sq_sqrt (mul_nonneg (by norm_num) hXp)]
    ring
  have hrB : s.B ≤ Real.sqrt (2 * p.1) := by
    apply (sq_le_sq₀ s.B_pos.le (Real.sqrt_nonneg _)).mp
    rw [Real.sq_sqrt (mul_nonneg (by norm_num) hXp)]
    linarith
  have hm : PositiveOrderMoments.massHistory (profiles s n).axial
      (Real.sqrt (2 * p.1), p.2) = 0 := by
    change (∫ R in (0 : ℝ)..Real.sqrt (2 * p.1), R * (profiles s n).axial (R, p.2)) = 0
    rw [← PositiveOrderMoments.positiveIntegral_eq_primitive s.B_pos.le hrB
      (fun R hR => by rw [profiles_axial_exterior s n p.2 (hI (abs_le.mp heta)) R hR, mul_zero])]
    have hh := congrFun (profiles_moments s hn (hI (abs_le.mp heta))) (0 : Fin 5)
    simpa only [PositiveOrderMoments.moments, PositiveOrderMoments.rowDensity,
      PositiveOrderMoments.slice, Matrix.cons_val_zero, Pi.zero_apply] using hh
  have he := massHistory_extendEven (commonWindow s hI) (profiles s n).axial
    (Real.sqrt_nonneg (2 * p.1)) (heta.trans (commonWindow s hI).one_lt_inner.le)
  rw [hr2] at he
  exact he.symm.trans hm

theorem extended_axial_average_zero {h C : ℝ} (s : Scheme S h C)
    (hI : Icc (-1 : ℝ) 1 ⊆ S) {n : ℕ} (hn : 0 < n) {p : ℝ × ℝ}
    (hX : s.B ^ 2 / 2 ≤ p.1) (heta : |p.2| ≤ 1) :
    ProfileHistories.average (extendedCoefficient s hI n 1) p = 0 := by
  have hp : 0 < p.1 := (div_pos (sq_pos_of_pos s.B_pos) (by norm_num)).trans_le hX
  have hm := extended_axial_primitive_zero s hI hn hX heta
  rw [ProfileHistories.primitive_eq_mul_average] at hm
  exact (mul_eq_zero.mp hm).resolve_left hp.ne'

end ActualFlux

section FiniteBase

variable {S : Set ℝ} {h : ℝ} {D : ProfileHistories.RadialDomain}
  (d : Domain S h) (C : ℝ) (P : ProfileHistories.Profiles D)
  (hD : ∀ X, 0 ≤ X → ∀ eta ∈ S, (X, eta) ∈ D.carrier)

/-- The four order-zero fields are computed from one actual profile.
In particular beta is reconstructed from U; it is not independent data. -/
noncomputable def baseFields : Coefficient S where
  phi := boundConstant S C * radialPullback P.f P.f_smooth hD
  axial := radialPullback P.U P.U_smooth hD
  beta := betaFromU d 0 (radialPullback P.U P.U_smooth hD)
  pressure := radialPullback P.pressure P.pressure_smooth hD

theorem baseFields_phi {p : ℝ × ℝ} (hX : 0 ≤ p.1) :
    xProfile (baseFields d C P hD).phi p = C * P.f p := by
  change C * xProfile (radialPullback P.f P.f_smooth hD) p = _
  rw [radialPullback_xProfile _ _ _ hX]

theorem baseFields_axial {p : ℝ × ℝ} (hX : 0 ≤ p.1) :
    xProfile (baseFields d C P hD).axial p = P.U p :=
  radialPullback_xProfile P.U P.U_smooth hD hX

theorem baseFields_pressure {p : ℝ × ℝ} (hX : 0 ≤ p.1) :
    xProfile (baseFields d C P hD).pressure p = P.pressure p :=
  radialPullback_xProfile P.pressure P.pressure_smooth hD hX

theorem baseFields_angular (hC : C ≠ 0) {R eta : ℝ} (hR : 0 ≤ R) :
    angularField C (baseFields d C P hD).phi (R, eta) = P.E (R ^ 2 / 2, eta) := by
  change R / C * (C * P.f (R ^ 2 / 2, eta)) =
    Real.sqrt (2 * (R ^ 2 / 2)) * P.f (R ^ 2 / 2, eta)
  rw [show 2 * (R ^ 2 / 2) = R ^ 2 by ring, Real.sqrt_sq hR]
  field_simp

theorem baseFields_mass {R eta : ℝ} (hR : 0 ≤ R) (heta : eta ∈ S) :
    PositiveOrderMoments.massHistory (baseFields d C P hD).axial (R, eta) =
      P.M (R ^ 2 / 2, eta) := by
  apply massHistory_of_composition _ _ hR
  · exact P.U_smooth.continuousOn.comp
      (continuous_id.prodMk continuous_const).continuousOn
      (fun X hX => hD X hX.1 eta heta)
  · intro r _
    rfl

theorem baseFields_parameterMass {R eta : ℝ} (hR : 0 ≤ R) (heta : eta ∈ S) :
    PositiveOrderMoments.parameterMassHistory (baseFields d C P hD).axial (R, eta) =
      ProfileHistories.primitive (ProfileHistories.parameterPartial P.U) (R ^ 2 / 2, eta) := by
  have hu := (baseFields d C P hD).axial.smooth
  have hm := ProfileHistories.primitive_smooth (PositiveOrderMoments.parameterDomain S d.isOpen)
    (contDiffOn_fst.mul hu)
  have hd := parameter_derivative d.isOpen hm heta R
  change HasDerivAt (fun t => PositiveOrderMoments.massHistory (baseFields d C P hD).axial (R, t))
    (ProfileHistories.parameterPartial (PositiveOrderMoments.massHistory (baseFields d C P
        hD).axial) (R, eta)) eta at hd
  rw [PositiveOrderMoments.massHistory_parameterPartial_on d.isOpen hu heta] at hd
  have hp := ProfileHistories.parameterPartial_hasDerivAt D P.M_smooth
    (hD (R ^ 2 / 2) (by positivity) eta heta)
  change HasDerivAt (fun t => P.M (R ^ 2 / 2, t))
    (ProfileHistories.parameterPartial (ProfileHistories.primitive P.U) (R ^ 2 / 2, eta)) eta at hp
  rw [ProfileHistories.parameterPartial_primitive D P.U_smooth
    (hD (R ^ 2 / 2) (by positivity) eta heta)] at hp
  apply hd.unique (hp.congr_of_eventuallyEq _)
  filter_upwards [d.isOpen.mem_nhds heta] with t ht
  exact baseFields_mass d C P hD hR ht

theorem baseFields_beta_flux {R eta : ℝ} (hR : 0 ≤ R) (heta : eta ∈ S) :
    R ^ 2 / 2 * (baseFields d C P hD).beta (R, eta) =
      SlowDivergence.radialFlux h 0 P.U (R ^ 2 / 2, eta) := by
  rw [SlowDivergence.radialFlux_eq_histories D P.U_smooth h 0
    (hD (R ^ 2 / 2) (by positivity) eta heta)]
  change R ^ 2 / 2 * betaFromU d 0 (baseFields d C P hD).axial (R, eta) = _
  rw [betaFromU_eq_fluxHistory d 0 (baseFields d C P hD).axial (w := (R, eta)) heta,
      PositiveOrderMoments.fluxHistory,
    baseFields_mass d C P hD hR heta, baseFields_parameterMass d C P hD hR heta]
  change (eta * R ^ 2 * P.U (R ^ 2 / 2, eta) -
    2 * eta * (PositiveAxisSystem.dScale h + 0) * P.M (R ^ 2 / 2, eta) -
    PositiveAxisSystem.edge eta * _) / PositiveAxisSystem.ell h eta = _
  simp only [PositiveAxisSystem.dScale, CoordinateAlgebra.D, PositiveAxisSystem.edge,
    CoordinateAlgebra.d, PositiveAxisSystem.ell, CoordinateAlgebra.L, ProfileHistories.Profiles.M]
  ring

theorem baseFields_beta_value {p : ℝ × ℝ} (hX : 0 < p.1) (heta : p.2 ∈ S) :
    xProfile (baseFields d C P hD).beta p = SlowDivergence.radialFlux h 0 P.U p / p.1 := by
  have he := baseFields_beta_flux d C P hD (Real.sqrt_nonneg (2 * p.1)) heta
  have hr : (Real.sqrt (2 * p.1)) ^ 2 / 2 = p.1 := by
    rw [Real.sq_sqrt (by positivity)]
    ring
  rw [hr] at he
  exact (eq_div_iff hX.ne').mpr (by simpa only [xProfile, mul_comm] using he)

theorem baseFields_axial_exterior {B : ℝ} (hB : 0 ≤ B)
    (hu : ∀ eta ∈ S, ∀ X, B ^ 2 / 2 ≤ X → P.U (X, eta) = 0) :
    Exterior B S (baseFields d C P hD).axial := by
  intro eta heta R hR
  apply hu eta heta
  exact div_le_div_of_nonneg_right ((sq_le_sq₀ hB (hB.trans hR)).2 hR) (by norm_num)

theorem baseFields_beta_exterior {B : ℝ} (hB : 0 < B)
    (hu : ∀ eta ∈ S, ∀ X, B ^ 2 / 2 ≤ X → P.U (X, eta) = 0)
    (hm : ∀ eta ∈ S, P.M (B ^ 2 / 2, eta) = 0) :
    Exterior B S (baseFields d C P hD).beta := by
  have hex := baseFields_axial_exterior d C P hD hB.le hu
  apply reconstructed_beta_exterior d 0 _ hB hex
  intro eta heta
  rw [PositiveOrderMoments.positiveIntegral_eq_primitive hB.le le_rfl
    (fun R hR => by rw [hex eta heta R hR, mul_zero])]
  change PositiveOrderMoments.massHistory (baseFields d C P hD).axial (B, eta) = 0
  rw [baseFields_mass d C P hD hB.le heta, hm eta heta]

/-- Finite exterior and pure-power facts suffice to construct the input
record for the actual infinite repair recursion. -/
noncomputable def baseDataOfProfile {lam a b B : ℝ} (hC : C ≠ 0) (ha : 0 ≤ a) (hB : 0 < B)
    (hu : ∀ eta ∈ S, ∀ X, B ^ 2 / 2 ≤ X → P.U (X, eta) = 0)
    (hm : ∀ eta ∈ S, P.M (B ^ 2 / 2, eta) = 0)
    (amplitude : ℝ → ℝ) (hs : ContDiffOn ℝ ∞ amplitude S)
    (hne : ∀ eta ∈ S, amplitude eta ≠ 0)
    (hup : ∀ eta ∈ S, ∀ R ∈ Ioo a b, P.U (R ^ 2 / 2, eta) = 0)
    (hep : ∀ eta ∈ S, ∀ R ∈ Ioo a b,
      P.E (R ^ 2 / 2, eta) = FiveRowRank.background lam (amplitude eta) R) :
    BaseData S C lam a b B where
  fields := baseFields d C P hD
  axial_exterior := baseFields_axial_exterior d C P hD hB.le hu
  beta_exterior := baseFields_beta_exterior d C P hD hB hu hm
  amplitude := amplitude
  amplitude_smooth := hs
  amplitude_ne := hne
  axial_patch := hup
  angular_patch := fun eta he R hR => (baseFields_angular d C P hD hC (ha.trans hR.1.le)).trans
      (hep eta he R hR)

end FiniteBase

section LocalChanges

variable {S : Set ℝ} {h C r : ℝ} {D D' : ProfileHistories.RadialDomain}
  (d : Domain S h) (P : ProfileHistories.Profiles D) (Q : ProfileHistories.Profiles D')
  (hP : ∀ X, 0 ≤ X → ∀ eta ∈ S, (X, eta) ∈ D.carrier)
  (hQ : ∀ X, 0 ≤ X → ∀ eta ∈ S, (X, eta) ∈ D'.carrier)

theorem local_average_eq
    (hu : EqOn P.U Q.U (Ico 0 r ×ˢ S)) {p : ℝ × ℝ}
    (hp : p ∈ Ico 0 r ×ˢ S) : P.Ubar p = Q.Ubar p := by
  change (∫ t in (0 : ℝ)..1, P.U (t * p.1, p.2)) = ∫ t in (0 : ℝ)..1, Q.U (t * p.1, p.2)
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le zero_le_one] at ht
  exact hu ⟨⟨mul_nonneg ht.1 hp.1.1, (mul_le_of_le_one_left hp.1.1 ht.2).trans_lt hp.1.2⟩, hp.2⟩

include d in
theorem local_flux_eq (hu : EqOn P.U Q.U (Ico 0 r ×ˢ S))
    {p : ℝ × ℝ} (hX : 0 < p.1) (hi : p.1 < r) (heta : p.2 ∈ S) :
    SlowDivergence.radialFlux h 0 P.U p = SlowDivergence.radialFlux h 0 Q.U p := by
  have hn := (isOpen_Ioo.prod d.isOpen).mem_nhds ⟨⟨hX, hi⟩, heta⟩
  have hug : P.U =ᶠ[𝓝 p] Q.U := by
    filter_upwards [hn] with q hq
    exact hu ⟨⟨hq.1.1.le, hq.1.2⟩, hq.2⟩
  have hag : ProfileHistories.average P.U =ᶠ[𝓝 p] ProfileHistories.average Q.U := by
    filter_upwards [hn] with q hq
    exact local_average_eq P Q hu ⟨⟨hq.1.1.le, hq.1.2⟩, hq.2⟩
  exact (NaturalCoefficientBridge.radialFlux_congr_germ h 0 hug hag).eq_of_nhds

theorem local_beta_eq_pos (hu : EqOn P.U Q.U (Ico 0 r ×ˢ S))
    {p : ℝ × ℝ} (hX : 0 < p.1) (hi : p.1 < r) (heta : p.2 ∈ S) :
    xProfile (baseFields d C P hP).beta p = xProfile (baseFields d C Q hQ).beta p := by
  rw [baseFields_beta_value d C P hP hX heta, baseFields_beta_value d C Q hQ hX heta,
    local_flux_eq d P Q hu hX hi heta]

theorem local_beta_eq_axis (hr : 0 < r) (hu : EqOn P.U Q.U (Ico 0 r ×ˢ S))
    {eta : ℝ} (heta : eta ∈ S) :
    (baseFields d C P hP).beta (0, eta) = (baseFields d C Q hQ).beta (0, eta) := by
  have hs : 0 < Real.sqrt r := Real.sqrt_pos.mpr hr
  have he : EqOn (fun R => (baseFields d C P hP).beta (R, eta))
      (fun R => (baseFields d C Q hQ).beta (R, eta)) (Ioo 0 (Real.sqrt r)) := by
    intro R hR
    have hi : R ^ 2 / 2 < r := by
      have hsq := (sq_lt_sq₀ hR.1.le hs.le).2 hR.2
      rw [Real.sq_sqrt hr.le] at hsq
      linarith [sq_nonneg R]
    change (baseFields d C P hP).beta (R, eta) = (baseFields d C Q hQ).beta (R, eta)
    rw [← xProfile_radius (baseFields d C P hP).beta hR.1.le eta,
      ← xProfile_radius (baseFields d C Q hQ).beta hR.1.le eta]
    exact local_beta_eq_pos d P Q hP hQ hu (div_pos (sq_pos_of_pos hR.1) (by norm_num)) hi heta
  have hc := he.closure (slice_smooth (baseFields d C P hP).beta.smooth heta).continuous
    (slice_smooth (baseFields d C Q hQ).beta.smooth heta).continuous
  apply hc
  rw [closure_Ioo hs.ne]
  exact ⟨le_rfl, hs.le⟩

/-- Local edits do not change any base field on the smaller core. The
pressure and beta conclusions are derived from actual integrals and germs. -/
theorem baseFields_local_eq (hr : 0 < r) (h0 : P.pressure0 = Q.pressure0)
    (hf : EqOn P.f Q.f (Ico 0 r ×ˢ S)) (hu : EqOn P.U Q.U (Ico 0 r ×ˢ S))
    (i : Fin 4) {p : ℝ × ℝ} (hp : p ∈ Ico 0 r ×ˢ S) :
    xProfile (component (baseFields d C P hP) i) p =
      xProfile (component (baseFields d C Q hQ) i) p := by
  fin_cases i
  · change xProfile (baseFields d C P hP).phi p = xProfile (baseFields d C Q hQ).phi p
    rw [baseFields_phi d C P hP hp.1.1, baseFields_phi d C Q hQ hp.1.1, hf hp]
  · change xProfile (baseFields d C P hP).axial p = xProfile (baseFields d C Q hQ).axial p
    rw [baseFields_axial d C P hP hp.1.1, baseFields_axial d C Q hQ hp.1.1, hu hp]
  · change xProfile (baseFields d C P hP).beta p = xProfile (baseFields d C Q hQ).beta p
    by_cases hX : p.1 = 0
    · have hp' : p = (0, p.2) := Prod.ext hX rfl
      rw [hp']
      simpa only [xProfile, mul_zero, Real.sqrt_zero] using
        local_beta_eq_axis d P Q hP hQ hr hu hp.2
    · exact local_beta_eq_pos d P Q hP hQ hu (lt_of_le_of_ne hp.1.1 (Ne.symm hX)) hp.1.2 hp.2
  · change xProfile (baseFields d C P hP).pressure p = xProfile (baseFields d C Q hQ).pressure p
    rw [baseFields_pressure d C P hP hp.1.1, baseFields_pressure d C Q hQ hp.1.1]
    exact (ActualSlowAxis.histories_congr_below P Q hp.1.1 (congrFun h0 p.2)
      (fun Y hY => hf ⟨⟨hY.1, hY.2.trans_lt hp.1.2⟩, hp.2⟩)
      (fun Y hY => hu ⟨⟨hY.1, hY.2.trans_lt hp.1.2⟩, hp.2⟩)).2

end LocalChanges

section NominalBase

variable {F : OutgoingProfile.Profile} (W : NominalProfile.Witness F)

/-- Nominal outer X, constructed using `max`. -/
noncomputable def nominalOuterX : ℝ :=
  max W.controls.radius (max (OutgoingDilation.pulseEndRadius F W.controls.radius)
    (ReservedPatches.right F W.controls.radius .positive)) + 1

/-- Nominal outer radius, given by `Real.sqrt (2 * nominalOuterX W)`. -/
noncomputable def nominalOuterRadius : ℝ := Real.sqrt (2 * nominalOuterX W)

theorem nominalOuterX_gt_radius : W.controls.radius < nominalOuterX W := by
  have := le_max_left W.controls.radius
    (max (OutgoingDilation.pulseEndRadius F W.controls.radius)
      (ReservedPatches.right F W.controls.radius .positive))
  dsimp [nominalOuterX]
  linarith

theorem nominalOuterX_pos : 0 < nominalOuterX W :=
  W.controls.radius_pos.trans (nominalOuterX_gt_radius W)

theorem nominalOuterX_gt_pulse : OutgoingDilation.pulseEndRadius F W.controls.radius <
    nominalOuterX W := by
  have h₁ := le_max_left (OutgoingDilation.pulseEndRadius F W.controls.radius)
    (ReservedPatches.right F W.controls.radius .positive)
  have h₂ := le_max_right W.controls.radius
    (max (OutgoingDilation.pulseEndRadius F W.controls.radius)
      (ReservedPatches.right F W.controls.radius .positive))
  dsimp [nominalOuterX]
  linarith

theorem nominalOuterX_gt_patch : ReservedPatches.right F W.controls.radius .positive <
    nominalOuterX W := by
  have h₁ := le_max_right (OutgoingDilation.pulseEndRadius F W.controls.radius)
    (ReservedPatches.right F W.controls.radius .positive)
  have h₂ := le_max_right W.controls.radius
    (max (OutgoingDilation.pulseEndRadius F W.controls.radius)
      (ReservedPatches.right F W.controls.radius .positive))
  dsimp [nominalOuterX]
  linarith

theorem nominalOuterRadius_pos : 0 < nominalOuterRadius W :=
  Real.sqrt_pos.2 (mul_pos (by norm_num) (nominalOuterX_pos W))

theorem nominalOuterRadius_square : nominalOuterRadius W ^ 2 / 2 = nominalOuterX W := by
  rw [nominalOuterRadius, Real.sq_sqrt (mul_nonneg (by norm_num) (nominalOuterX_pos W).le)]
  ring

theorem nominal_patch_before_outer :
    ReservedPatches.radialRight F W.controls.radius .positive < nominalOuterRadius W := by
  apply Real.sqrt_lt_sqrt (mul_nonneg (by norm_num)
    (ReservedPatches.right_pos F W.controls.radius W.controls.radius_pos .positive).le)
  exact mul_lt_mul_of_pos_left (nominalOuterX_gt_patch W) (by norm_num)

theorem nominal_pulse_gt_radius : W.controls.radius < OutgoingDilation.pulseEndRadius F
    W.controls.radius := by
  have hp : 0 < F.data.core.endpoint := by
    dsimp only [OutgoingSchedule.Parameters.endpoint]
    linarith [F.data.core.pulseStart_pos, F.data.core.pulseLength_pos]
  simpa only [OutgoingDilation.radius, Real.exp_zero, mul_one, OutgoingDilation.pulseEndRadius]
      using
    ReservedPatches.radius_strictMono W.controls.radius W.controls.radius_pos hp

theorem nominalOuterX_eq_pulse :
    nominalOuterX W = OutgoingDilation.pulseEndRadius F W.controls.radius + 1 := by
  have hp : ReservedPatches.right F W.controls.radius .positive <
      OutgoingDilation.pulseEndRadius F W.controls.radius := by
    apply ReservedPatches.radius_strictMono W.controls.radius W.controls.radius_pos
    have hc := (ReservedPatches.clock_inside_wait F .positive).2
    dsimp only [OutgoingSchedule.Parameters.endpoint]
    linarith [F.data.core.pulseLength_pos]
  simp only [nominalOuterX, max_eq_left hp.le, max_eq_right (nominal_pulse_gt_radius W).le]

/-- The common higher-order support radius is strictly inside the later
heat switch and hence before the order-one terminal collar. -/
theorem nominalOuterX_lt_switch : nominalOuterX W < OutgoingDilation.switchRadius F
    W.controls.radius := by
  have hflat : 1 < OutgoingTail.flattenLength := by
    have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
    dsimp only [OutgoingTail.flattenLength]
    nlinarith [OutgoingTail.stepBound_ge_one]
  have hc : F.data.core.endpoint + 1 < HeatTailEdit.switchStart F.data := by
    have h₁ := OutgoingTail.releaseStart_gt_flattenEnd F.data
    have h₂ := OutgoingTail.tailStart_gt_release F.data
    dsimp only [OutgoingTail.TailData.flattenEnd] at h₁
    dsimp only [HeatTailEdit.switchStart]
    linarith
  have hr : 1 < W.controls.radius := by
    have hx := (W.controls.Xi_lt_heatJoin W.separated).trans W.controls.heatJoin_lt_radius
    norm_num [NominalProfile.Xi] at hx
    linarith
  have hp : 1 < OutgoingDilation.pulseEndRadius F W.controls.radius := hr.trans
      (nominal_pulse_gt_radius W)
  have he : (2 : ℝ) ≤ Real.exp 1 := by
    have he := Real.add_one_le_exp (1 : ℝ)
    linarith
  rw [nominalOuterX_eq_pulse]
  calc
    OutgoingDilation.pulseEndRadius F W.controls.radius + 1 <
        OutgoingDilation.pulseEndRadius F W.controls.radius * 2 := by linarith
    _ ≤ OutgoingDilation.pulseEndRadius F W.controls.radius * Real.exp 1 :=
      mul_le_mul_of_nonneg_left he (by linarith)
    _ = OutgoingDilation.radius W.controls.radius (F.data.core.endpoint + 1) := by
      rw [OutgoingDilation.pulseEndRadius, OutgoingDilation.radius, OutgoingDilation.radius,
          Real.exp_add]
      ring
    _ < OutgoingDilation.switchRadius F W.controls.radius :=
      ReservedPatches.radius_strictMono W.controls.radius W.controls.radius_pos hc

theorem matching_before_window (slot : ReservedPatches.Slot) {X : ℝ}
    (hX : X ∈ ReservedPatches.window F W.controls.radius slot) : W.controls.radius < X := by
  have hc : 0 < ReservedPatches.leftClock F slot :=
    F.data.core.holdStart_pos.trans (ReservedPatches.clock_inside_wait F slot).1
  have hs := ReservedPatches.radius_strictMono W.controls.radius W.controls.radius_pos hc
  have hleft : W.controls.radius < ReservedPatches.left F W.controls.radius slot := by
    simpa only [OutgoingDilation.radius, Real.exp_zero, mul_one, ReservedPatches.left] using hs
  exact hleft.trans hX.1

theorem nominal_positive_patch {R eta : ℝ}
    (hR : R ∈ ReservedPatches.radialWindow F W.controls.radius .positive) :
    W.U (R ^ 2 / 2, eta) = 0 ∧
    W.E (R ^ 2 / 2, eta) =
      FiveRowRank.background F.data.core.lam (ReservedPatches.radialAmplitude F W.controls.radius
          eta) R := by
  have hx := ReservedPatches.radial_mem_window F W.controls.radius W.controls.radius_pos .positive
      hR
  have hmatch := matching_before_window W .positive hx
  have hsep : ReservedPatches.right F W.controls.radius .heat ≤
      ReservedPatches.left F W.controls.radius .positive := by
    apply (ReservedPatches.radius_strictMono W.controls.radius W.controls.radius_pos).monotone
    dsimp [ReservedPatches.rightClock, ReservedPatches.leftClock,
      ReservedPatches.rightOffset, ReservedPatches.leftOffset]
    linarith
  have he : W.E (R ^ 2 / 2, eta) = OutgoingDilation.E F W.controls.radius (R ^ 2 / 2, eta) :=
    W.E_outgoing_between_patch_and_switch hmatch.le
      (by rw [← ReservedPatches.heat_right]; exact hsep.trans hx.1.le)
      (hx.2.le.trans (ReservedPatches.right_before_switch F W.controls.radius W.controls.radius_pos
          .positive).le)
  have hrpos := (ReservedPatches.radialLeft_pos F W.controls.radius W.controls.radius_pos
      .positive).trans hR.1
  have hc := ReservedPatches.clean_fields F W.controls.radius W.controls.radius_pos .positive eta hx
  refine ⟨(W.U_outgoing (W.controls.heatJoin_lt_radius.trans hmatch)).trans hc.1, ?_⟩
  rw [he, hc.2, ReservedPatches.square_half_power _ _ hrpos]
  simp only [ReservedPatches.radialAmplitude, FiveRowRank.background, mul_assoc]

variable {S : Set ℝ} (d : Domain S F.data.h)
  (hD : ∀ X, 0 ≤ X → ∀ eta ∈ S, (X, eta) ∈ W.domain.carrier)

include hD

theorem nominal_axial_exterior :
    ∀ eta ∈ S, ∀ X, nominalOuterRadius W ^ 2 / 2 ≤ X → W.profiles.U (X, eta) = 0 := by
  intro eta heta X hX
  rw [nominalOuterRadius_square] at hX
  have hmatch := (nominalOuterX_gt_radius W).trans_le hX
  exact (W.after_pulse_open (W.controls.heatJoin_lt_radius.trans hmatch)
    (hD X ((nominalOuterX_pos W).le.trans hX) eta heta)
    ((nominalOuterX_gt_pulse W).le.trans hX)).1

theorem nominal_mass_exterior :
    ∀ eta ∈ S, W.profiles.M (nominalOuterRadius W ^ 2 / 2, eta) = 0 := by
  intro eta heta
  rw [nominalOuterRadius_square]
  change (∫ x in (0 : ℝ)..nominalOuterX W, W.U (x, eta)) = 0
  rw [intervalIntegral.integral_of_le (nominalOuterX_pos W).le]
  exact (W.after_pulse_open (W.controls.heatJoin_lt_radius.trans (nominalOuterX_gt_radius W))
    (hD _ (nominalOuterX_pos W).le eta heta) (nominalOuterX_gt_pulse W).le).2

/-- A finite base input constructed from the same nominal witness,
with the manuscript's reserved positive-order patch. -/
noncomputable def nominalBaseData :
    BaseData S W.axis.normalization F.data.core.lam
      (ReservedPatches.radialLeft F W.controls.radius .positive)
      (ReservedPatches.radialRight F W.controls.radius .positive) (nominalOuterRadius W) :=
  baseDataOfProfile d W.axis.normalization W.profiles hD W.axis.normalization_pos.ne'
    (ReservedPatches.radialLeft_pos F W.controls.radius W.controls.radius_pos .positive).le
    (nominalOuterRadius_pos W) (nominal_axial_exterior W hD) (nominal_mass_exterior W hD)
    (ReservedPatches.radialAmplitude F W.controls.radius)
    (ReservedPatches.radialAmplitude_contDiff F W.controls.radius).contDiffOn
    (fun eta _ => (ReservedPatches.radialAmplitude_pos F W.controls.radius eta).ne')
    (fun _ _ _ hR => (nominal_positive_patch W hR).1)
    (fun eta _ R hR => by
      change Real.sqrt (2 * (R ^ 2 / 2)) * W.f (R ^ 2 / 2, eta) = _
      rw [← W.E_eq_sqrt_f (p := (R ^ 2 / 2, eta)) (div_pos (sq_pos_of_pos
        ((ReservedPatches.radialLeft_pos F W.controls.radius W.controls.radius_pos .positive).trans
            hR.1)) (by
            norm_num))]
      exact (nominal_positive_patch W hR).2)

theorem nominalBaseData_beta : (nominalBaseData W d hD).fields.beta =
    betaFromU d 0 (nominalBaseData W d hD).fields.axial := rfl

end NominalBase

section CoherentHierarchy

variable {F : OutgoingProfile.Profile} (W : NominalProfile.Witness F)

theorem nominalPressure_eq : F.axisDatum = PressureDatum.pressure
    (SchedulePressure.clockWeight F.data) (SchedulePressure.shapeExponent F.data) :=
  F.axisDatum_eq.trans (SchedulePressure.axisPressure_eq F.data)

/-- Nominal tube, constructed using `ActualSlowAxis.constructedTube`. -/
noncomputable def nominalTube :=
  ActualSlowAxis.constructedTube (SchedulePressure.admissible F.data) (nominalPressure_eq (F := F))
    W.axis.natural.profile W.axis.scale_pos W.axis.small W.axis.preparation.sigma_pos

/-- Nominal complex domain, constructed using `ActualSlowAxis.parameterDomain`. -/
noncomputable def nominalComplexDomain : Set ℂ :=
  ActualSlowAxis.parameterDomain (AxisHolomorphic.parameterTube
      ActivationHolomorphic.parameterWindow
    (ActualSlowAxis.tubeWidth (SchedulePressure.admissible F.data) (nominalPressure_eq (F := F))
      W.axis.natural.profile W.axis.scale_pos W.axis.small W.axis.preparation.sigma_pos))

theorem nominalComplexDomain_open : IsOpen (nominalComplexDomain W) :=
  ActualSlowAxis.parameterDomain_open (nominalTube W).isOpen

/-- Nominal hierarchy, constructed using `ActualSlowAxis.hierarchy`. -/
noncomputable def nominalHierarchy :=
  ActualSlowAxis.hierarchy (nominalTube W) W.controls.activationTime_pos
      W.controls.referenceWidth_pos
    W.controls.referenceWidth_small W.controls.kappa F.axisDatum_contDiff W.axis.normalization

/-- Nominal radius, given by `ActualSlowAxis.axisRadius W.axis.referenceInput
W.controls.referenceWidth`. -/
noncomputable def nominalRadius : ℝ :=
  ActualSlowAxis.axisRadius W.axis.referenceInput W.controls.referenceWidth

/-- One open parameter set serves the nominal fields and every order of
the same analytic local hierarchy. -/
noncomputable def nominalParameters : Set ℝ :=
  {eta | (0, eta) ∈ W.domain.carrier} ∩ Complex.ofReal ⁻¹' nominalComplexDomain W

theorem nominalParameters_open : IsOpen (nominalParameters W) :=
  (W.domain.isOpen.preimage (continuous_const.prodMk continuous_id)).inter
    ((nominalComplexDomain_open W).preimage Complex.continuous_ofReal)

theorem nominalParameters_contains : Icc (-1 : ℝ) 1 ⊆ nominalParameters W := by
  intro eta heta
  refine ⟨W.domain_contains le_rfl heta, ?_⟩
  exact ActualSlowAxis.parameterDomain_real (nominalTube W).real_mem heta

theorem nominalParameters_domain (X : ℝ) (hX : 0 ≤ X) (eta : ℝ)
    (heta : eta ∈ nominalParameters W) : (X, eta) ∈ W.domain.carrier :=
  W.controls.extendedDomain_nonnegative hX heta.1.1.1.2 heta.1.2 heta.1.1.2

theorem nominalParameters_reference {eta : ℝ} (heta : eta ∈ nominalParameters W) :
    eta ∈ ReferencePath.parameterInterval :=
  ActualSlowAxis.parameterDomain_real_interval heta.2

theorem nominalDomain : Domain (nominalParameters W) F.data.h where
  isOpen := nominalParameters_open W
  denominator := fun _ heta =>
    SlowRecursion.domain_real_denominator (ActualSlowAxis.domain (nominalTube W) zero_lt_one) heta.2

/-- Nominal inner, given by `(4 / W.axis.scale) / 4`. -/
noncomputable def nominalInner : ℝ := (4 / W.axis.scale) / 4
/-- Nominal stop, given by `(4 / W.axis.scale) / 2`. -/
noncomputable def nominalStop : ℝ := (4 / W.axis.scale) / 2

theorem nominalInner_pos : 0 < nominalInner W := by
  dsimp [nominalInner]
  exact div_pos (div_pos (by norm_num) W.axis.scale_pos) (by norm_num)

theorem nominalInner_lt_stop : nominalInner W < nominalStop W := by
  have hi := div_pos (show (0 : ℝ) < 4 by norm_num) W.axis.scale_pos
  dsimp [nominalInner, nominalStop]
  linarith

theorem nominalStop_lt_initial : nominalStop W < 4 / W.axis.scale := by
  have hi := div_pos (show (0 : ℝ) < 4 by norm_num) W.axis.scale_pos
  dsimp [nominalStop]
  linarith

theorem nominalInitial_le_collar :
    4 / W.axis.scale ≤ (4 / W.axis.scale) * Real.exp W.controls.referenceWidth :=
  le_mul_of_one_le_right (div_pos (by norm_num) W.axis.scale_pos).le
    (Real.one_le_exp_iff.mpr W.controls.referenceWidth_pos.le)

theorem nominalStop_lt_radius : nominalStop W < nominalRadius W ^ 2 :=
  ((nominalStop_lt_initial W).trans_le (nominalInitial_le_collar W)).trans
    (ActualSlowAxis.collar_lt_square W.axis.referenceInput W.controls.referenceWidth)

theorem nominalStop_lt_patch :
    nominalStop W < (ReservedPatches.radialLeft F W.controls.radius .positive) ^ 2 / 2 := by
  have hleft : W.controls.radius < ReservedPatches.left F W.controls.radius .positive := by
    have hc := F.data.core.holdStart_pos.trans (ReservedPatches.clock_inside_wait F .positive).1
    have hs := ReservedPatches.radius_strictMono W.controls.radius W.controls.radius_pos hc
    simpa only [OutgoingDilation.radius, Real.exp_zero, mul_one, ReservedPatches.left] using hs
  have hsmall := (nominalStop_lt_initial W).trans_le
    ((nominalInitial_le_collar W).trans W.controls.activation_collar_le_Xi)
  have hbig := ((W.controls.Xi_lt_heatJoin W.separated).trans W.controls.heatJoin_lt_radius).trans
      hleft
  rw [ReservedPatches.radialLeft, Real.sq_sqrt
    (mul_nonneg (by
        norm_num) (ReservedPatches.left_pos F W.controls.radius W.controls.radius_pos
            .positive).le)]
  linarith

/-- The global recursive sequence uses the same nominal profile and the
same constructed natural/ACT local hierarchy, with one common cutoff. -/
noncomputable def nominalScheme : Scheme (nominalParameters W) F.data.h W.axis.normalization :=
  schemeFromHierarchy (nominalHierarchy W) (ActualSlowAxis.axisRadius_pos _ _)
    (nominalComplexDomain_open W) (nominalDomain W) (fun _ heta => heta.2)
    W.axis.normalization_pos.ne' F.data.core.lam_pos (nominalInner_lt_stop W)
    (nominalStop_lt_radius W) (nominalStop_lt_patch W)
    (ReservedPatches.radialLeft_pos F W.controls.radius W.controls.radius_pos .positive)
    (ReservedPatches.radial_left_lt_right F W.controls.radius W.controls.radius_pos .positive)
    (nominal_patch_before_outer W).le (nominalBaseData W (nominalDomain W)
        (nominalParameters_domain W))

theorem nominalLocalization : Localization (nominalScheme W) (nominalHierarchy W) (nominalInner W)
    :=
  localizationFromHierarchy (nominalHierarchy W) (ActualSlowAxis.axisRadius_pos _ _)
    (nominalComplexDomain_open W) (nominalDomain W) (fun _ heta => heta.2)
    W.axis.normalization_pos.ne' F.data.core.lam_pos (nominalInner_pos W) (nominalInner_lt_stop W)
    (nominalStop_lt_radius W) (nominalStop_lt_patch W)
    (ReservedPatches.radialLeft_pos F W.controls.radius W.controls.radius_pos .positive)
    (ReservedPatches.radial_left_lt_right F W.controls.radius W.controls.radius_pos .positive)
    (nominal_patch_before_outer W).le (nominalBaseData W (nominalDomain W)
        (nominalParameters_domain W))

/-- Nominal ACT, constructed using `StressActivation.FromReference.histories`. -/
noncomputable def nominalACT : ProfileHistories.Profiles W.axis.referenceInput.radialDomain :=
  StressActivation.FromReference.histories W.axis.referenceInput W.controls.activationTime_pos
    W.controls.referenceWidth_pos W.controls.referenceWidth_small W.controls.kappa
    F.axisDatum F.axisDatum_contDiff

theorem nominalInitial_le_Xi : 4 / W.axis.scale ≤ NominalProfile.Xi :=
  (nominalInitial_le_collar W).trans W.controls.activation_collar_le_Xi

theorem nominalACT_fields {X eta : ℝ} (hX : 0 ≤ X) (hi : X ≤ 4 / W.axis.scale)
    (heta : eta ∈ ReferencePath.parameterInterval) :
    W.profiles.f (X, eta) = (nominalACT W).f (X, eta) ∧
    W.profiles.U (X, eta) = (nominalACT W).U (X, eta) := by
  have hn := W.seed_agreement (p := (X, eta)) hX (hi.trans (nominalInitial_le_Xi W))
  have ha := W.controls.seed_activation (p := (X, eta)) heta (hi.trans (nominalInitial_le_collar W))
  exact ⟨hn.1.trans ha.1, hn.2.1.trans ha.2⟩

theorem nominalACT_histories {X eta : ℝ} (hX : 0 ≤ X) (hi : X ≤ 4 / W.axis.scale)
    (heta : eta ∈ ReferencePath.parameterInterval) :
    W.profiles.Ubar (X, eta) = (nominalACT W).Ubar (X, eta) ∧
    W.profiles.pressure (X, eta) = (nominalACT W).pressure (X, eta) :=
  ActualSlowAxis.histories_congr_below W.profiles (nominalACT W) hX rfl
    (fun _ hY => (nominalACT_fields W hY.1 (hY.2.trans hi) heta).1)
    (fun _ hY => (nominalACT_fields W hY.1 (hY.2.trans hi) heta).2)

theorem nominalACT_flux {X eta : ℝ} (hX : 0 < X) (hi : X < 4 / W.axis.scale)
    (heta : eta ∈ ReferencePath.parameterInterval) :
    SlowDivergence.radialFlux F.data.h 0 W.profiles.U (X, eta) =
      SlowDivergence.radialFlux F.data.h 0 (nominalACT W).U (X, eta) := by
  have hn := (isOpen_Ioo.prod ReferencePath.parameterInterval_open).mem_nhds
    (show (X, eta) ∈ Ioo (0 : ℝ) (4 / W.axis.scale) ×ˢ ReferencePath.parameterInterval from ⟨⟨hX,
        hi⟩, heta⟩)
  have hu : W.profiles.U =ᶠ[𝓝 (X, eta)] (nominalACT W).U := by
    filter_upwards [hn] with p hp
    exact (nominalACT_fields W hp.1.1.le hp.1.2.le hp.2).2
  have ha : ProfileHistories.average W.profiles.U =ᶠ[𝓝 (X, eta)]
      ProfileHistories.average (nominalACT W).U := by
    filter_upwards [hn] with p hp
    exact (nominalACT_histories W hp.1.1.le hp.1.2.le hp.2).1
  exact (NaturalCoefficientBridge.radialFlux_congr_germ F.data.h 0 hu ha).eq_of_nhds

theorem nominalHierarchy_base {X eta : ℝ} (hX : 0 ≤ X) (hi : X < nominalInner W)
    (heta : eta ∈ nominalParameters W) :
    SlowRecursion.profile ((nominalHierarchy W).coefficients 0 0) (X, eta) =
        W.axis.normalization * W.profiles.f (X, eta) ∧
    SlowRecursion.profile ((nominalHierarchy W).coefficients 0 1) (X, eta) = W.profiles.U (X, eta) ∧
    SlowRecursion.profile ((nominalHierarchy W).coefficients 0 3) (X, eta) = W.profiles.pressure
        (X, eta) := by
  have hinit : X ≤ 4 / W.axis.scale :=
    (hi.trans ((nominalInner_lt_stop W).trans (nominalStop_lt_initial W))).le
  have hv := ActualSlowAxis.hierarchy_base_values (nominalTube W) W.controls.activationTime_pos
    W.controls.referenceWidth_pos W.controls.referenceWidth_small W.controls.kappa
    F.axisDatum_contDiff W.axis.normalization hX (nominalParameters_reference W heta)
  have hf := nominalACT_fields W hX hinit (nominalParameters_reference W heta)
  have hp := nominalACT_histories W hX hinit (nominalParameters_reference W heta)
  exact ⟨hv.1.trans (congrArg (W.axis.normalization * ·) hf.1.symm),
    hv.2.1.trans hf.2.symm, hv.2.2.2.trans hp.2.symm⟩

theorem nominalBase_beta_pos {X eta : ℝ} (hX : 0 < X) (hi : X < nominalInner W)
    (heta : eta ∈ nominalParameters W) :
    xProfile (nominalScheme W).base.beta (X, eta) =
      SlowRecursion.profile ((nominalHierarchy W).coefficients 0 4) (X, eta) := by
  have hr : X < nominalRadius W ^ 2 :=
    hi.trans ((nominalInner_lt_stop W).trans (nominalStop_lt_radius W))
  have hinit : X < 4 / W.axis.scale := hi.trans
    ((nominalInner_lt_stop W).trans (nominalStop_lt_initial W))
  have hf := NaturalCoefficientBridge.hierarchy_flux_zero (nominalTube W)
      W.controls.activationTime_pos
    W.controls.referenceWidth_pos W.controls.referenceWidth_small W.controls.kappa
    F.axisDatum_contDiff W.axis.normalization ⟨hX, hr⟩ heta.2
  change X * SlowRecursion.profile ((nominalHierarchy W).coefficients 0 4) (X, eta) =
    SlowDivergence.radialFlux F.data.h 0 (nominalACT W).U (X, eta) at hf
  change xProfile (baseFields (nominalDomain W) W.axis.normalization W.profiles
      (nominalParameters_domain W)).beta (X, eta) = _
  rw [baseFields_beta_value _ _ _ _ hX heta, nominalACT_flux W hX hinit
      (nominalParameters_reference W heta)]
  exact ((eq_div_iff hX.ne').mpr (by simpa only [mul_comm] using hf)).symm

theorem nominalBase_beta_axis {eta : ℝ} (heta : eta ∈ nominalParameters W) :
    (nominalScheme W).base.beta (0, eta) =
      localExtension (nominalLocalization W) 0 4 (0, eta) := by
  have hs : 0 < Real.sqrt (nominalInner W) := Real.sqrt_pos.mpr (nominalInner_pos W)
  have he : EqOn (fun R => (nominalScheme W).base.beta (R, eta))
      (fun R => localExtension (nominalLocalization W) 0 4 (R, eta))
      (Ioo 0 (Real.sqrt (nominalInner W))) := by
    intro R hR
    have hi : R ^ 2 / 2 < nominalInner W := by
      have hh := (sq_lt_sq₀ hR.1.le hs.le).2 hR.2
      rw [Real.sq_sqrt (nominalInner_pos W).le] at hh
      linarith [sq_nonneg R]
    change (nominalScheme W).base.beta (R, eta) = localExtension (nominalLocalization W) 0 4 (R,
        eta)
    rw [← xProfile_radius (nominalScheme W).base.beta hR.1.le eta,
      nominalBase_beta_pos W (div_pos (sq_pos_of_pos hR.1) (by norm_num)) hi heta,
      localExtension_radial (nominalLocalization W) 0 4 hR.1.le hi.le]
  have hc := he.closure (slice_smooth (nominalScheme W).base.beta.smooth heta).continuous
    (slice_smooth (localExtension (nominalLocalization W) 0 4).smooth heta).continuous
  apply hc
  rw [closure_Ioo hs.ne]
  exact ⟨le_rfl, hs.le⟩

theorem nominalBaseAgreement : BaseAgreement (nominalScheme W) (nominalHierarchy W) (nominalInner
    W) := by
  constructor
  · intro p hX hi heta
    change xProfile (baseFields (nominalDomain W) W.axis.normalization W.profiles
        (nominalParameters_domain W)).phi p = _
    rw [baseFields_phi _ _ _ _ hX]
    exact (nominalHierarchy_base W hX hi heta).1.symm
  · intro p hX hi heta
    change xProfile (baseFields (nominalDomain W) W.axis.normalization W.profiles
        (nominalParameters_domain W)).axial p = _
    rw [baseFields_axial _ _ _ _ hX]
    exact (nominalHierarchy_base W hX hi heta).2.1.symm
  · intro p hX hi heta
    by_cases h0 : p.1 = 0
    · have he := nominalBase_beta_axis W heta
      have hp : p = (0, p.2) := Prod.ext h0 rfl
      rw [hp]
      simpa only [xProfile, mul_zero, Real.sqrt_zero, zero_pow (by
          norm_num : 2 ≠ 0), zero_div] using
        he.trans (localExtension_radial (nominalLocalization W) 0 4 le_rfl
          (by simpa using (nominalInner_pos W).le))
    · exact nominalBase_beta_pos W (lt_of_le_of_ne hX (Ne.symm h0)) hi heta

theorem nominal_pressure_inner {p : ℝ × ℝ} (hX : 0 ≤ p.1) (hi : p.1 < nominalInner W)
    (heta : p.2 ∈ nominalParameters W) :
    xProfile (nominalScheme W).base.pressure p =
      SlowRecursion.profile ((nominalHierarchy W).coefficients 0 3) p := by
  change xProfile (baseFields (nominalDomain W) W.axis.normalization W.profiles
      (nominalParameters_domain W)).pressure p = _
  rw [baseFields_pressure _ _ _ _ hX]
  exact (nominalHierarchy_base W hX hi heta).2.2.symm

theorem nominal_zero_coefficients {p : ℝ × ℝ} (hX : 0 < p.1) (hi : p.1 < nominalInner W)
    (heta : p.2 ∈ nominalParameters W) :
    SlowExpansionResidual.angularCoefficient F.data.h (asSlowProfiles (nominalScheme W)) 0 p = 0 ∧
    SlowExpansionResidual.axialCoefficient F.data.h (asSlowProfiles (nominalScheme W)) 0 p = 0 := by
  let f := asSlowProfiles (nominalScheme W)
  let g := SlowResidualMatching.hierarchyProfiles (nominalHierarchy W)
  have hp0 : p ∈ NaturalCoefficientBridge.initialCore W.axis.scale :=
    ⟨⟨hX, hi.trans ((nominalInner_lt_stop W).trans (nominalStop_lt_initial W))⟩,
      nominalParameters_reference W heta⟩
  have hz := NaturalCoefficientBridge.fromNatural_coefficients_zero
    (SchedulePressure.admissible F.data) (nominalPressure_eq (F := F)) W.axis.natural.profile
    W.axis.scale_pos W.axis.small W.axis.preparation.sigma_pos W.controls.activationTime_pos
    W.controls.referenceWidth_pos W.controls.referenceWidth_small W.controls.kappa hp0 heta.2
  change SlowExpansionResidual.angularCoefficient F.data.h g 0 p = 0 ∧
    SlowExpansionResidual.axialCoefficient F.data.h g 0 p = 0 at hz
  have hphi0 : f.phi 0 =ᶠ[𝓝 p] g.phi 0 :=
    profiles_x_phi_germ (nominalLocalization W) (nominalBaseAgreement W) 0 hX hi heta
  have hu0 : f.axial 0 =ᶠ[𝓝 p] g.axial 0 :=
    profiles_x_axial_germ (nominalLocalization W) (nominalBaseAgreement W) 0 hX hi heta
  have hb0 := profiles_x_beta_germ (nominalLocalization W) (nominalBaseAgreement W) 0 hX hi heta
  have hv0 : f.flux 0 =ᶠ[𝓝 p] g.flux 0 := by
    filter_upwards [hb0] with q hq
    exact congrArg (q.1 * ·) hq
  have hp : f.pressure 0 =ᶠ[𝓝 p] g.pressure 0 := by
    filter_upwards [(isOpen_Ioo.prod (nominalParameters_open W)).mem_nhds ⟨⟨hX, hi⟩, heta⟩] with q
        hq
    change xProfile (profiles (nominalScheme W) 0).pressure q = _
    rw [profiles_zero]
    exact nominal_pressure_inner W hq.1.1.le hq.1.2 hq.2
  have hv : ∀ j ≤ 0, f.flux j =ᶠ[𝓝 p] g.flux j := by
    intro j hj
    have hj0 : j = 0 := Nat.eq_zero_of_le_zero hj
    simpa only [hj0] using hv0
  have hu : ∀ j ≤ 0, f.axial j =ᶠ[𝓝 p] g.axial j := by
    intro j hj
    have hj0 : j = 0 := Nat.eq_zero_of_le_zero hj
    simpa only [hj0] using hu0
  have hphi : ∀ j ≤ 0, f.phi j =ᶠ[𝓝 p] g.phi j := by
    intro j hj
    have hj0 : j = 0 := Nat.eq_zero_of_le_zero hj
    simpa only [hj0] using hphi0
  exact ⟨(SlowResidualMatching.angularCoefficient_congr_germ F.data.h 0 hv hu hphi).trans hz.1,
    (SlowResidualMatching.axialCoefficient_congr_germ F.data.h 0 hv hu hp).trans hz.2⟩

theorem nominalZeroOrder : ZeroOrderSolved (nominalScheme W) (nominalInner W) :=
  ⟨fun _ hx hi he => (nominal_zero_coefficients W hx hi he).1,
   fun _ hx hi he => (nominal_zero_coefficients W hx hi he).2⟩

/-- The complete smooth input family is constructed from the single
nominal witness; there are no freely supplied repaired coefficient fields. -/
noncomputable def nominalCoefficients : SlowBorelBase.Coefficients :=
  coefficients (nominalLocalization W) (nominalBaseAgreement W) (nominalZeroOrder W)
    (nominalParameters_contains W)

theorem nominalCoefficients_smooth : SlowBorelBase.SmoothCoefficients (nominalCoefficients W) :=
  coefficients_smooth (nominalLocalization W) (nominalBaseAgreement W) (nominalZeroOrder W)
    (nominalParameters_contains W)

theorem nominalCoefficients_zero_fields {p : ℝ × ℝ} (hX : 0 ≤ p.1) (heta : |p.2| ≤ 1) :
    (nominalCoefficients W).phi 0 p = W.axis.normalization * W.f p ∧
    (nominalCoefficients W).axial 0 p = W.U p ∧
    (nominalCoefficients W).pressure 0 p = W.Pi p := by
  have he := coefficients_fields_eq (nominalLocalization W) (nominalBaseAgreement W)
    (nominalZeroOrder W) (nominalParameters_contains W) 0 hX heta
  refine ⟨he.1.trans ?_, he.2.1.trans ?_, he.2.2.trans ?_⟩
  · change xProfile (profiles (nominalScheme W) 0).phi p = _
    rw [profiles_zero]
    exact baseFields_phi (nominalDomain W) W.axis.normalization W.profiles
        (nominalParameters_domain W) hX
  · change xProfile (profiles (nominalScheme W) 0).axial p = _
    rw [profiles_zero]
    exact baseFields_axial (nominalDomain W) W.axis.normalization W.profiles
        (nominalParameters_domain W) hX
  · change xProfile (profiles (nominalScheme W) 0).pressure p = _
    rw [profiles_zero]
    exact baseFields_pressure (nominalDomain W) W.axis.normalization W.profiles
        (nominalParameters_domain W) hX

theorem nominalCoefficients_stress_zero {p : ℝ × ℝ}
    (hp : p.1 ≤ nominalInner W / 8) (n : ℕ) :
    (nominalCoefficients W).stressTheta n p = 0 ∧ (nominalCoefficients W).stressAxial n p = 0 :=
  coefficients_stress_zero_left (nominalLocalization W) (nominalBaseAgreement W) (nominalZeroOrder
      W)
    (nominalParameters_contains W) n hp

theorem nominalCoefficients_stress_eq {p : ℝ × ℝ}
    (hp : 0 ≤ p.1) (heta : |p.2| ≤ 1) (n : ℕ) :
    (nominalCoefficients W).stressTheta n p =
      SlowResidualMatching.thetaStress F.data.h W.axis.normalization (asSlowProfiles (nominalScheme
          W)) n p ∧
    (nominalCoefficients W).stressAxial n p =
      SlowResidualMatching.zStress F.data.h (asSlowProfiles (nominalScheme W)) n p :=
  coefficients_stress_eq (nominalLocalization W) (nominalBaseAgreement W) (nominalZeroOrder W)
    (nominalParameters_contains W) n hp heta

theorem nominal_extended_flux (n : ℕ) {p : ℝ × ℝ} (hX : 0 ≤ p.1) (heta : |p.2| ≤ 1) :
    p.1 * extendedCoefficient (nominalScheme W) (nominalParameters_contains W) n 2 p =
      SlowDivergence.radialFlux F.data.h (AxisSourceRegularity.slowOrder F.data.h n)
        ((nominalCoefficients W).axial n) p := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have h := extended_flux_zero (nominalScheme W) (nominalParameters_contains W) rfl hX heta
    simp only [AxisSourceRegularity.slowOrder, Nat.cast_zero, mul_zero, zero_mul] at h ⊢
    exact h
  · exact extended_flux (nominalScheme W) (nominalParameters_contains W) hn hX heta

/-- A common smooth solenoidal physical base now follows from one actual
nominal witness, including the derived zero-order equations. -/
theorem nominal_exists_base (lo hi : ℝ) (N : ℕ) :
    ∃ a : ℕ → ℕ, N ≤ a 0 ∧
      SlowBorelBase.AdmissibleScales F.data.h
        (SlowBorelBase.coefficientBundle W.axis.normalization (nominalCoefficients W))
        (SlowBorelBase.innerBox lo hi) a ∧
      ContDiffOn ℝ ∞ (SlowBorelBase.baseVelocity a F.data.h W.axis.normalization
          (nominalCoefficients W))
        (Iio 1 ×ˢ (univ : Set ProblemStatement.Space)) ∧
      ∀ t : ℝ, t < 1 → ∀ x : ProblemStatement.Space,
        ProblemStatement.spatialDivergence
          (SlowBorelBase.baseVelocity a F.data.h W.axis.normalization (nominalCoefficients W)) t x
              = 0 :=
  SlowBorelBase.exists_base_fields W.axis.small.h_pos (by linarith [W.axis.small.h_le])
    (nominalCoefficients_smooth W) W.axis.normalization lo hi N

theorem nominal_divergenceCoefficient (n : ℕ) {p : ℝ × ℝ}
    (hX : 0 < p.1) (heta : p.2 ∈ nominalParameters W) :
    SlowExpansionResidual.divergenceCoefficient F.data.h (asSlowProfiles (nominalScheme W)) n p = 0
        := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · change SimilarityProfile.partialX
        (AxisSourceRegularity.axisFactor (xProfile (profiles (nominalScheme W) 0).beta)) p +
      SimilarityProfile.Z F.data.h
        (SlowExpansionResidual.axialExponent F.data.h + SlowExpansionResidual.slowOrder F.data.h 0)
        (xProfile (profiles (nominalScheme W) 0).axial) p = 0
    rw [profiles_zero]
    have h := betaFromU_x_divergence (nominalDomain W) 0 (nominalScheme W).base.axial hX heta
    simp only [SlowExpansionResidual.axialExponent, SlowExpansionResidual.slowOrder,
      Nat.cast_zero, mul_zero, zero_mul] at h ⊢
    exact h
  · exact profiles_divergenceCoefficient (nominalScheme W) hn hX heta

theorem nominal_pressureCoefficient (n : ℕ) {p : ℝ × ℝ}
    (hX : 0 < p.1) (heta : p.2 ∈ nominalParameters W) :
    SlowExpansionResidual.pressureCoefficient F.data.h W.axis.normalization
      (asSlowProfiles (nominalScheme W)) n p = 0 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hpg : (asSlowProfiles (nominalScheme W)).pressure 0 =ᶠ[𝓝 p] W.profiles.pressure := by
      filter_upwards [continuous_fst.continuousAt (Ioi_mem_nhds hX)] with q hq
      change xProfile (profiles (nominalScheme W) 0).pressure q = _
      rw [profiles_zero]
      exact baseFields_pressure (nominalDomain W) W.axis.normalization W.profiles
        (nominalParameters_domain W) hq.le
    have hpr : SimilarityProfile.partialX ((asSlowProfiles (nominalScheme W)).pressure 0) p =
        W.profiles.f p ^ 2 := by
      rw [SimilarityProfile.partialX, hpg.fderiv_eq]
      exact W.profiles.radialPartial_pressure (nominalParameters_domain W p.1 hX.le p.2 heta)
    have hphi : (asSlowProfiles (nominalScheme W)).phi 0 p = W.axis.normalization * W.profiles.f p
        := by
      change xProfile (profiles (nominalScheme W) 0).phi p = _
      rw [profiles_zero]
      exact baseFields_phi (nominalDomain W) W.axis.normalization W.profiles
        (nominalParameters_domain W) hX.le
    simp only [SlowExpansionResidual.pressureCoefficient, SlowExpansionResidual.previous,
      SlowExpansionResidual.convolution, Finset.Nat.antidiagonal_zero, Finset.sum_singleton,
      hpr, hphi, zero_div, add_zero]
    field_simp [W.axis.normalization_pos.ne']; ring
  · exact profiles_pressureCoefficient (nominalScheme W) hn hX heta

theorem nominal_densities_smooth (n : ℕ) :
    Smooth (nominalParameters W)
      (SlowResidualMatching.thetaDensity F.data.h W.axis.normalization (asSlowProfiles
          (nominalScheme W)) n) ∧
    Smooth (nominalParameters W)
      (SlowResidualMatching.zDensity F.data.h (asSlowProfiles (nominalScheme W)) n) :=
  ⟨thetaDensity_smooth (nominalLocalization W) (nominalBaseAgreement W) (nominalZeroOrder W) n,
    zDensity_smooth (nominalLocalization W) (nominalBaseAgreement W) (nominalZeroOrder W) n⟩

theorem nominalCoefficients_axis {n : ℕ} (hn : 0 < n) {eta : ℝ} (heta : |eta| ≤ 1) :
    (nominalCoefficients W).phi n (0, eta) = 0 ∧
    (nominalCoefficients W).axial n (0, eta) = 0 ∧
    (nominalCoefficients W).pressure n (0, eta) = 0 :=
  ⟨extendedCoefficient_axis (nominalLocalization W) (nominalBaseAgreement W)
      (nominalParameters_contains W) hn 0 heta,
   extendedCoefficient_axis (nominalLocalization W) (nominalBaseAgreement W)
      (nominalParameters_contains W) hn 1 heta,
   extendedCoefficient_axis (nominalLocalization W) (nominalBaseAgreement W)
      (nominalParameters_contains W) hn 3 heta⟩

theorem nominalCoefficients_compactSupport {n : ℕ} (hn : 0 < n) :
    HasCompactSupport ((nominalCoefficients W).phi n) ∧
    HasCompactSupport ((nominalCoefficients W).axial n) ∧
    HasCompactSupport ((nominalCoefficients W).pressure n) :=
  ⟨extendedCoefficient_compactSupport (nominalScheme W) (nominalParameters_contains W) hn 0,
   extendedCoefficient_compactSupport (nominalScheme W) (nominalParameters_contains W) hn 1,
   extendedCoefficient_compactSupport (nominalScheme W) (nominalParameters_contains W) hn 3⟩

theorem nominalCoefficients_positive_exterior {n : ℕ} (hn : 0 < n) {p : ℝ × ℝ}
    (hp : nominalOuterX W ≤ p.1) :
    (nominalCoefficients W).phi n p = 0 ∧ (nominalCoefficients W).axial n p = 0 ∧
    (nominalCoefficients W).pressure n p = 0 := by
  have hp' : (nominalScheme W).B ^ 2 / 2 ≤ p.1 := by
    change nominalOuterRadius W ^ 2 / 2 ≤ p.1
    rwa [nominalOuterRadius_square]
  exact ⟨extendedCoefficient_zero_exterior (nominalScheme W) (nominalParameters_contains W) hn 0
      hp',
    extendedCoefficient_zero_exterior (nominalScheme W) (nominalParameters_contains W) hn 1 hp',
    extendedCoefficient_zero_exterior (nominalScheme W) (nominalParameters_contains W) hn 3 hp'⟩

theorem nominal_axial_primitive_zero {n : ℕ} (hn : 0 < n) {p : ℝ × ℝ}
    (hX : nominalOuterX W ≤ p.1) (heta : |p.2| ≤ 1) :
    ProfileHistories.primitive ((nominalCoefficients W).axial n) p = 0 := by
  apply extended_axial_primitive_zero (nominalScheme W) (nominalParameters_contains W) hn _ heta
  change nominalOuterRadius W ^ 2 / 2 ≤ p.1
  rwa [nominalOuterRadius_square]

theorem nominal_axial_average_zero {n : ℕ} (hn : 0 < n) {p : ℝ × ℝ}
    (hX : nominalOuterX W ≤ p.1) (heta : |p.2| ≤ 1) :
    ProfileHistories.average ((nominalCoefficients W).axial n) p = 0 := by
  apply extended_axial_average_zero (nominalScheme W) (nominalParameters_contains W) hn _ heta
  change nominalOuterRadius W ^ 2 / 2 ≤ p.1
  rwa [nominalOuterRadius_square]

theorem nominal_exterior_base {p : ℝ × ℝ} (hX : nominalOuterX W ≤ p.1) (heta : |p.2| ≤ 1) :
    W.U p = 0 ∧ W.profiles.M p = 0 := by
  have hXp : 0 ≤ p.1 := (nominalOuterX_pos W).le.trans hX
  have hh := W.after_pulse_open
    (W.controls.heatJoin_lt_radius.trans ((nominalOuterX_gt_radius W).trans_le hX))
    (nominalParameters_domain W p.1 hXp p.2 (nominalParameters_contains W (abs_le.mp heta)))
    ((nominalOuterX_gt_pulse W).le.trans hX)
  refine ⟨hh.1, ?_⟩
  change (∫ r in (0 : ℝ)..p.1, W.U (r, p.2)) = 0
  rw [intervalIntegral.integral_of_le hXp]
  exact hh.2

theorem nominalCoefficients_axial_zero_all (n : ℕ) {p : ℝ × ℝ}
    (hX : nominalOuterX W ≤ p.1) (heta : |p.2| ≤ 1) : (nominalCoefficients W).axial n p = 0 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact (nominalCoefficients_zero_fields W ((nominalOuterX_pos W).le.trans hX) heta).2.1.trans
      (nominal_exterior_base W hX heta).1
  · exact (nominalCoefficients_positive_exterior W hn hX).2.1

theorem nominal_axial_primitive_zero_all (n : ℕ) {p : ℝ × ℝ}
    (hX : nominalOuterX W ≤ p.1) (heta : |p.2| ≤ 1) :
    ProfileHistories.primitive ((nominalCoefficients W).axial n) p = 0 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hXp : 0 ≤ p.1 := (nominalOuterX_pos W).le.trans hX
    have he : EqOn (fun r => (nominalCoefficients W).axial 0 (r, p.2))
        (fun r => W.U (r, p.2)) (uIcc 0 p.1) := by
      intro r hr
      rw [uIcc_of_le hXp] at hr
      exact (nominalCoefficients_zero_fields W (p := (r, p.2)) hr.1 heta).2.1
    change (∫ r in (0 : ℝ)..p.1, (nominalCoefficients W).axial 0 (r, p.2)) = 0
    rw [intervalIntegral.integral_congr he]
    exact (nominal_exterior_base W hX heta).2
  · exact nominal_axial_primitive_zero W hn hX heta

theorem nominal_axial_average_zero_all (n : ℕ) {p : ℝ × ℝ}
    (hX : nominalOuterX W ≤ p.1) (heta : |p.2| ≤ 1) :
    ProfileHistories.average ((nominalCoefficients W).axial n) p = 0 := by
  have hp : 0 < p.1 := (nominalOuterX_pos W).trans_le hX
  have hm := nominal_axial_primitive_zero_all W n hX heta
  rw [ProfileHistories.primitive_eq_mul_average] at hm
  exact (mul_eq_zero.mp hm).resolve_left hp.ne'

end CoherentHierarchy

section ModifiedBase

variable {F : OutgoingProfile.Profile} (W : NominalProfile.Witness F)
  {D : ProfileHistories.RadialDomain} (Q : ProfileHistories.Profiles D)

/-- A finite modification certificate. These are literal identities of the
modified physical fields and their mass primitive, not assumptions about the
positive-order hierarchy or its infinite sum. A modulation construction can
obtain them from supported transplant and restoration of the five rows. -/
structure FiniteModification (S : Set ℝ) (lo hi : ℝ) : Prop where
  isOpen : IsOpen S
  contains : Icc (-1 : ℝ) 1 ⊆ S
  subset : S ⊆ nominalParameters W
  halfPlane : ∀ X, 0 ≤ X → ∀ eta ∈ S, (X, eta) ∈ D.carrier
  inner : nominalInner W ≤ lo
  ordered : lo < hi
  outer : hi ≤ ReservedPatches.left F W.controls.radius .positive
  pressure0 : Q.pressure0 = W.profiles.pressure0
  fields : ∀ p : ℝ × ℝ, 0 ≤ p.1 → p.2 ∈ S → p.1 ≤ lo ∨ hi ≤ p.1 →
    Q.f p = W.profiles.f p ∧ Q.U p = W.profiles.U p
  mass : ∀ eta ∈ S, Q.M (nominalOuterX W, eta) = W.profiles.M (nominalOuterX W, eta)

variable {S : Set ℝ} {lo hi : ℝ} (M : FiniteModification W Q S lo hi)

include M

theorem modifiedDomain : Domain S F.data.h where
  isOpen := M.isOpen
  denominator := fun eta heta => (nominalDomain W).denominator eta (M.subset heta)

theorem modified_original_domain (X : ℝ) (hX : 0 ≤ X) (eta : ℝ) (heta : eta ∈ S) :
    (X, eta) ∈ W.domain.carrier := nominalParameters_domain W X hX eta (M.subset heta)

theorem modification_before_outer : hi < nominalOuterX W :=
  (M.outer.trans_lt (ReservedPatches.left_lt_right F W.controls.radius W.controls.radius_pos
      .positive)).trans
    (nominalOuterX_gt_patch W)

theorem modified_axial_exterior :
    ∀ eta ∈ S, ∀ X, nominalOuterRadius W ^ 2 / 2 ≤ X → Q.U (X, eta) = 0 := by
  intro eta heta X hX
  have hX' : nominalOuterX W ≤ X := by simpa only [nominalOuterRadius_square] using hX
  have hXp : 0 ≤ X := (nominalOuterX_pos W).le.trans hX'
  rw [(M.fields (X, eta) hXp heta (Or.inr ((modification_before_outer W Q M).le.trans hX'))).2]
  exact nominal_axial_exterior W (modified_original_domain W Q M) eta heta X hX

theorem modified_mass_zero : ∀ eta ∈ S, Q.M (nominalOuterRadius W ^ 2 / 2, eta) = 0 := by
  intro eta heta
  rw [nominalOuterRadius_square, M.mass eta heta]
  have hm := nominal_mass_exterior W (modified_original_domain W Q M) eta heta
  simpa only [nominalOuterRadius_square] using hm

theorem modified_positive_patch {R eta : ℝ} (heta : eta ∈ S)
    (hR : R ∈ ReservedPatches.radialWindow F W.controls.radius .positive) :
    Q.U (R ^ 2 / 2, eta) = 0 ∧
    Q.E (R ^ 2 / 2, eta) =
      FiveRowRank.background F.data.core.lam (ReservedPatches.radialAmplitude F W.controls.radius
          eta) R := by
  have hx := ReservedPatches.radial_mem_window F W.controls.radius W.controls.radius_pos .positive
      hR
  have hp := M.fields (R ^ 2 / 2, eta) (by positivity) heta (Or.inr (M.outer.trans hx.1.le))
  refine ⟨hp.2.trans (nominal_positive_patch W hR).1, ?_⟩
  change Real.sqrt (2 * (R ^ 2 / 2)) * Q.f (R ^ 2 / 2, eta) = _
  rw [hp.1]
  change Real.sqrt (2 * (R ^ 2 / 2)) * W.f (R ^ 2 / 2, eta) = _
  rw [← W.E_eq_sqrt_f (p := (R ^ 2 / 2, eta))
    (ReservedPatches.mem_window_pos F W.controls.radius W.controls.radius_pos .positive hx)]
  exact (nominal_positive_patch W hR).2

/-- Modified base data, constructed using `baseDataOfProfile`. -/
noncomputable def modifiedBaseData :
    BaseData S W.axis.normalization F.data.core.lam
      (ReservedPatches.radialLeft F W.controls.radius .positive)
      (ReservedPatches.radialRight F W.controls.radius .positive) (nominalOuterRadius W) :=
  baseDataOfProfile (modifiedDomain W Q M) W.axis.normalization Q M.halfPlane
    W.axis.normalization_pos.ne'
    (ReservedPatches.radialLeft_pos F W.controls.radius W.controls.radius_pos .positive).le
    (nominalOuterRadius_pos W) (modified_axial_exterior W Q M) (modified_mass_zero W Q M)
    (ReservedPatches.radialAmplitude F W.controls.radius)
    (ReservedPatches.radialAmplitude_contDiff F W.controls.radius).contDiffOn
    (fun eta _ => (ReservedPatches.radialAmplitude_pos F W.controls.radius eta).ne')
    (fun _ he _ hR => (modified_positive_patch W Q M he hR).1)
    (fun _ he _ hR => (modified_positive_patch W Q M he hR).2)

/-- Modified scheme, constructed using `schemeFromHierarchy`. -/
noncomputable def modifiedScheme : Scheme S F.data.h W.axis.normalization :=
  schemeFromHierarchy (nominalHierarchy W) (ActualSlowAxis.axisRadius_pos _ _)
    (nominalComplexDomain_open W) (modifiedDomain W Q M) (fun _ heta => (M.subset heta).2)
    W.axis.normalization_pos.ne' F.data.core.lam_pos (nominalInner_lt_stop W)
    (nominalStop_lt_radius W) (nominalStop_lt_patch W)
    (ReservedPatches.radialLeft_pos F W.controls.radius W.controls.radius_pos .positive)
    (ReservedPatches.radial_left_lt_right F W.controls.radius W.controls.radius_pos .positive)
    (nominal_patch_before_outer W).le (modifiedBaseData W Q M)

theorem modifiedLocalization : Localization (modifiedScheme W Q M) (nominalHierarchy W)
    (nominalInner W) :=
  localizationFromHierarchy (nominalHierarchy W) (ActualSlowAxis.axisRadius_pos _ _)
    (nominalComplexDomain_open W) (modifiedDomain W Q M) (fun _ heta => (M.subset heta).2)
    W.axis.normalization_pos.ne' F.data.core.lam_pos (nominalInner_pos W) (nominalInner_lt_stop W)
    (nominalStop_lt_radius W) (nominalStop_lt_patch W)
    (ReservedPatches.radialLeft_pos F W.controls.radius W.controls.radius_pos .positive)
    (ReservedPatches.radial_left_lt_right F W.controls.radius W.controls.radius_pos .positive)
    (nominal_patch_before_outer W).le (modifiedBaseData W Q M)

theorem modified_base_local (i : Fin 4) {p : ℝ × ℝ}
    (hX : 0 ≤ p.1) (hinner : p.1 < nominalInner W) (heta : p.2 ∈ S) :
    xProfile (component (modifiedScheme W Q M).base i) p =
      xProfile (component (nominalScheme W).base i) p := by
  have he := baseFields_local_eq (C := W.axis.normalization) (modifiedDomain W Q M) Q W.profiles
    M.halfPlane (modified_original_domain W Q M) (nominalInner_pos W) M.pressure0
    (fun y hy => (M.fields y hy.1.1 hy.2 (Or.inl (hy.1.2.le.trans M.inner))).1)
    (fun y hy => (M.fields y hy.1.1 hy.2 (Or.inl (hy.1.2.le.trans M.inner))).2)
    i (p := p) ⟨⟨hX, hinner⟩, heta⟩
  fin_cases i <;> exact he

theorem modifiedBaseAgreement :
    BaseAgreement (modifiedScheme W Q M) (nominalHierarchy W) (nominalInner W) := by
  constructor
  · intro p hx hi he
    exact (modified_base_local W Q M 0 hx hi he).trans ((nominalBaseAgreement W).phi p hx hi
        (M.subset he))
  · intro p hx hi he
    exact (modified_base_local W Q M 1 hx hi he).trans ((nominalBaseAgreement W).axial p hx hi
        (M.subset he))
  · intro p hx hi he
    exact (modified_base_local W Q M 2 hx hi he).trans ((nominalBaseAgreement W).beta p hx hi
        (M.subset he))

theorem modified_zero_coefficients {p : ℝ × ℝ} (hX : 0 < p.1) (hinner : p.1 < nominalInner W)
    (heta : p.2 ∈ S) :
    SlowExpansionResidual.angularCoefficient F.data.h (asSlowProfiles (modifiedScheme W Q M)) 0 p =
        0 ∧
    SlowExpansionResidual.axialCoefficient F.data.h (asSlowProfiles (modifiedScheme W Q M)) 0 p = 0
        := by
  let f := asSlowProfiles (modifiedScheme W Q M)
  let g := asSlowProfiles (nominalScheme W)
  have hg (i : Fin 4) :
      xProfile (component (profiles (modifiedScheme W Q M) 0) i) =ᶠ[𝓝 p]
        xProfile (component (profiles (nominalScheme W) 0) i) := by
    filter_upwards [(isOpen_Ioo.prod M.isOpen).mem_nhds ⟨⟨hX, hinner⟩, heta⟩] with y hy
    rw [profiles_zero, profiles_zero]
    exact modified_base_local W Q M i hy.1.1.le hy.1.2 hy.2
  have hphi0 : f.phi 0 =ᶠ[𝓝 p] g.phi 0 := hg 0
  have hu0 : f.axial 0 =ᶠ[𝓝 p] g.axial 0 := hg 1
  have hp0 : f.pressure 0 =ᶠ[𝓝 p] g.pressure 0 := hg 3
  have hv0 : f.flux 0 =ᶠ[𝓝 p] g.flux 0 := by
    filter_upwards [hg 2] with y hy
    exact congrArg (y.1 * ·) hy
  have hv : ∀ j ≤ 0, f.flux j =ᶠ[𝓝 p] g.flux j := by
    intro j hj
    simpa only [Nat.eq_zero_of_le_zero hj] using hv0
  have hu : ∀ j ≤ 0, f.axial j =ᶠ[𝓝 p] g.axial j := by
    intro j hj
    simpa only [Nat.eq_zero_of_le_zero hj] using hu0
  have hphi : ∀ j ≤ 0, f.phi j =ᶠ[𝓝 p] g.phi j := by
    intro j hj
    simpa only [Nat.eq_zero_of_le_zero hj] using hphi0
  have hz := nominal_zero_coefficients W hX hinner (M.subset heta)
  exact ⟨(SlowResidualMatching.angularCoefficient_congr_germ F.data.h 0 hv hu hphi).trans hz.1,
    (SlowResidualMatching.axialCoefficient_congr_germ F.data.h 0 hv hu hp0).trans hz.2⟩

theorem modifiedZeroOrder : ZeroOrderSolved (modifiedScheme W Q M) (nominalInner W) :=
  ⟨fun _ hx hi he => (modified_zero_coefficients W Q M hx hi he).1,
   fun _ hx hi he => (modified_zero_coefficients W Q M hx hi he).2⟩

/-- All positive profiles, canonical stress primitives, and global smooth
extensions are rebuilt from the actual finite modified profile. -/
noncomputable def modifiedCoefficients : SlowBorelBase.Coefficients :=
  coefficients (modifiedLocalization W Q M) (modifiedBaseAgreement W Q M) (modifiedZeroOrder W Q M)
      M.contains

theorem modifiedCoefficients_smooth : SlowBorelBase.SmoothCoefficients (modifiedCoefficients W Q M)
    :=
  coefficients_smooth (modifiedLocalization W Q M) (modifiedBaseAgreement W Q M) (modifiedZeroOrder
      W Q M) M.contains

theorem modifiedCoefficients_zero_fields {p : ℝ × ℝ} (hX : 0 ≤ p.1) (heta : |p.2| ≤ 1) :
    (modifiedCoefficients W Q M).phi 0 p = W.axis.normalization * Q.f p ∧
    (modifiedCoefficients W Q M).axial 0 p = Q.U p ∧
    (modifiedCoefficients W Q M).pressure 0 p = Q.pressure p := by
  have he := coefficients_fields_eq (modifiedLocalization W Q M) (modifiedBaseAgreement W Q M)
    (modifiedZeroOrder W Q M) M.contains 0 hX heta
  refine ⟨he.1.trans ?_, he.2.1.trans ?_, he.2.2.trans ?_⟩
  · change xProfile (profiles (modifiedScheme W Q M) 0).phi p = _
    rw [profiles_zero]
    exact baseFields_phi (modifiedDomain W Q M) W.axis.normalization Q M.halfPlane hX
  · change xProfile (profiles (modifiedScheme W Q M) 0).axial p = _
    rw [profiles_zero]
    exact baseFields_axial (modifiedDomain W Q M) W.axis.normalization Q M.halfPlane hX
  · change xProfile (profiles (modifiedScheme W Q M) 0).pressure p = _
    rw [profiles_zero]
    exact baseFields_pressure (modifiedDomain W Q M) W.axis.normalization Q M.halfPlane hX

theorem modifiedCoefficients_axis {n : ℕ} (hn : 0 < n) {eta : ℝ} (heta : |eta| ≤ 1) :
    (modifiedCoefficients W Q M).phi n (0, eta) = 0 ∧
    (modifiedCoefficients W Q M).axial n (0, eta) = 0 ∧
    (modifiedCoefficients W Q M).pressure n (0, eta) = 0 :=
  ⟨extendedCoefficient_axis (modifiedLocalization W Q M) (modifiedBaseAgreement W Q M) M.contains
      hn 0 heta,
   extendedCoefficient_axis (modifiedLocalization W Q M) (modifiedBaseAgreement W Q M) M.contains
       hn 1 heta,
   extendedCoefficient_axis (modifiedLocalization W Q M) (modifiedBaseAgreement W Q M) M.contains
       hn 3 heta⟩

theorem modified_extended_flux (n : ℕ) {p : ℝ × ℝ} (hX : 0 ≤ p.1) (heta : |p.2| ≤ 1) :
    p.1 * extendedCoefficient (modifiedScheme W Q M) M.contains n 2 p =
      SlowDivergence.radialFlux F.data.h (AxisSourceRegularity.slowOrder F.data.h n)
        ((modifiedCoefficients W Q M).axial n) p := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have h := extended_flux_zero (modifiedScheme W Q M) M.contains rfl hX heta
    simp only [AxisSourceRegularity.slowOrder, Nat.cast_zero, mul_zero, zero_mul] at h ⊢
    exact h
  · exact extended_flux (modifiedScheme W Q M) M.contains hn hX heta

theorem modified_divergenceCoefficient (n : ℕ) {p : ℝ × ℝ}
    (hX : 0 < p.1) (heta : p.2 ∈ S) :
    SlowExpansionResidual.divergenceCoefficient F.data.h (asSlowProfiles (modifiedScheme W Q M)) n
        p = 0 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · change SimilarityProfile.partialX
        (AxisSourceRegularity.axisFactor (xProfile (profiles (modifiedScheme W Q M) 0).beta)) p +
      SimilarityProfile.Z F.data.h
        (SlowExpansionResidual.axialExponent F.data.h + SlowExpansionResidual.slowOrder F.data.h 0)
        (xProfile (profiles (modifiedScheme W Q M) 0).axial) p = 0
    rw [profiles_zero]
    have h := betaFromU_x_divergence (modifiedDomain W Q M) 0 (modifiedScheme W Q M).base.axial hX
        heta
    simp only [SlowExpansionResidual.axialExponent, SlowExpansionResidual.slowOrder,
      Nat.cast_zero, mul_zero, zero_mul] at h ⊢
    exact h
  · exact profiles_divergenceCoefficient (modifiedScheme W Q M) hn hX heta

theorem modified_pressureCoefficient (n : ℕ) {p : ℝ × ℝ}
    (hX : 0 < p.1) (heta : p.2 ∈ S) :
    SlowExpansionResidual.pressureCoefficient F.data.h W.axis.normalization
      (asSlowProfiles (modifiedScheme W Q M)) n p = 0 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hpg : (asSlowProfiles (modifiedScheme W Q M)).pressure 0 =ᶠ[𝓝 p] Q.pressure := by
      filter_upwards [continuous_fst.continuousAt (Ioi_mem_nhds hX)] with y hy
      change xProfile (profiles (modifiedScheme W Q M) 0).pressure y = _
      rw [profiles_zero]
      exact baseFields_pressure (modifiedDomain W Q M) W.axis.normalization Q M.halfPlane hy.le
    have hpr : SimilarityProfile.partialX ((asSlowProfiles (modifiedScheme W Q M)).pressure 0) p =
        Q.f p ^ 2 := by
      rw [SimilarityProfile.partialX, hpg.fderiv_eq]
      exact Q.radialPartial_pressure (M.halfPlane p.1 hX.le p.2 heta)
    have hphi : (asSlowProfiles (modifiedScheme W Q M)).phi 0 p = W.axis.normalization * Q.f p := by
      change xProfile (profiles (modifiedScheme W Q M) 0).phi p = _
      rw [profiles_zero]
      exact baseFields_phi (modifiedDomain W Q M) W.axis.normalization Q M.halfPlane hX.le
    simp only [SlowExpansionResidual.pressureCoefficient, SlowExpansionResidual.previous,
      SlowExpansionResidual.convolution, Finset.Nat.antidiagonal_zero, Finset.sum_singleton,
      hpr, hphi, zero_div, add_zero]
    field_simp [W.axis.normalization_pos.ne']; ring
  · exact profiles_pressureCoefficient (modifiedScheme W Q M) hn hX heta

theorem modified_exists_base (lower upper : ℝ) (N : ℕ) :
    ∃ a : ℕ → ℕ, N ≤ a 0 ∧
      SlowBorelBase.AdmissibleScales F.data.h
        (SlowBorelBase.coefficientBundle W.axis.normalization (modifiedCoefficients W Q M))
        (SlowBorelBase.innerBox lower upper) a ∧
      ContDiffOn ℝ ∞ (SlowBorelBase.baseVelocity a F.data.h W.axis.normalization
          (modifiedCoefficients W Q M))
        (Iio 1 ×ˢ (univ : Set ProblemStatement.Space)) ∧
      ∀ t : ℝ, t < 1 → ∀ x : ProblemStatement.Space,
        ProblemStatement.spatialDivergence
          (SlowBorelBase.baseVelocity a F.data.h W.axis.normalization (modifiedCoefficients W Q M))
              t x = 0 :=
  SlowBorelBase.exists_base_fields W.axis.small.h_pos (by linarith [W.axis.small.h_le])
    (modifiedCoefficients_smooth W Q M) W.axis.normalization lower upper N

end ModifiedBase

end NavierStokes.AssembledSlowBase
