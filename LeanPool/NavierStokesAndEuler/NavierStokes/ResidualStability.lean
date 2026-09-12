/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.NavierStokes.SpatialCurl
import LeanPool.NavierStokesAndEuler.NavierStokes.JetBounds
import LeanPool.NavierStokesAndEuler.NavierStokes.ResidualCalculus
import LeanPool.NavierStokesAndEuler.NavierStokes.ResidualRegularity
import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Group.Continuity

/-!
# Stability of the actual Navier--Stokes residual under flat perturbations

Flatness and power growth below are bounds on norms of actual iterated
Fréchet derivatives. The differential and bilinear closure lemmas are proved
from the derivative identities and Leibniz estimates, not assumed.
-/

section

/-!
# Scalar flatness and fixed power losses

This file isolates the scalar asymptotic argument used in Lemmas 11.2--11.5
of the candidate manuscript. It proves neither the asserted bounds for physical
jets nor the existence, compatibility, or smooth extension of those jets.

All powers here have natural exponents. Constants and neighborhoods may depend
on the requested power, as they do in a flatness statement.
-/

@[expose] public section

open Filter Topology

namespace NavierStokes.Flatness

variable {α : Type*} {l : Filter α} {q f g : α → ℝ}

/-- Along `l`, `f` is eventually bounded by a constant times every natural
power of the absolute value of the scale `q`. -/
def PowerFlat (l : Filter α) (q f : α → ℝ) : Prop :=
  ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ x in l, |f x| ≤ C * |q x| ^ n

/-- An exact scalar estimate: `n + loss` powers of smallness absorb `loss`
powers in a nonzero denominator. No assumption that the scale is small is
needed for this algebraic step. -/
theorem fixed_power_loss_bound {x scale C : ℝ} {n loss : ℕ}
    (hscale : scale ≠ 0) (hx : |x| ≤ C * |scale| ^ (n + loss)) :
    |x / scale ^ loss| ≤ C * |scale| ^ n := by
  rw [abs_div, abs_pow]
  apply (div_le_iff₀ (pow_pos (abs_pos.mpr hscale) loss)).2
  simpa only [pow_add, mul_assoc] using hx

/-- Arbitrary power decay persists after any fixed inverse-power loss. -/
theorem PowerFlat.div_pow (hf : PowerFlat l q f)
    (hq : ∀ᶠ x in l, q x ≠ 0) (loss : ℕ) :
    PowerFlat l q (fun x => f x / q x ^ loss) := by
  intro n
  obtain ⟨C, hC, hbound⟩ := hf (n + loss)
  refine ⟨C, hC, ?_⟩
  filter_upwards [hq, hbound] with x hx hfx
  exact fixed_power_loss_bound hx hfx

/-- Flat estimates are stable under finite addition. -/
theorem PowerFlat.add (hf : PowerFlat l q f) (hg : PowerFlat l q g) :
    PowerFlat l q (fun x => f x + g x) := by
  intro n
  obtain ⟨C, hC, hfb⟩ := hf n
  obtain ⟨D, hD, hgb⟩ := hg n
  refine ⟨C + D, add_nonneg hC hD, ?_⟩
  filter_upwards [hfb, hgb] with x hfx hgx
  calc
    |f x + g x| ≤ |f x| + |g x| := abs_add_le _ _
    _ ≤ C * |q x| ^ n + D * |q x| ^ n := add_le_add hfx hgx
    _ = (C + D) * |q x| ^ n := (add_mul _ _ _).symm

/-- Flat estimates are stable under multiplication. Only boundedness of the
second factor, the `n = 0` case of its flatness, is used. -/
theorem PowerFlat.mul (hf : PowerFlat l q f) (hg : PowerFlat l q g) :
    PowerFlat l q (fun x => f x * g x) := by
  intro n
  obtain ⟨C, hC, hfb⟩ := hf n
  obtain ⟨D, hD, hgb⟩ := hg 0
  refine ⟨C * D, mul_nonneg hC hD, ?_⟩
  filter_upwards [hfb, hgb] with x hfx hgx
  have hgx' : |g x| ≤ D := by simpa only [pow_zero, mul_one] using hgx
  calc
    |f x * g x| = |f x| * |g x| := abs_mul _ _
    _ ≤ (C * |q x| ^ n) * D :=
      mul_le_mul hfx hgx' (abs_nonneg _) (mul_nonneg hC (pow_nonneg (abs_nonneg _) _))
    _ = (C * D) * |q x| ^ n := by ring

/-- A flat scalar times a scalar with a fixed power loss remains flat. This
models one factor in the residual product estimates, provided the stated
bounds have already been established for the actual factors. -/
theorem PowerFlat.mul_of_power_bound (hf : PowerFlat l q f)
    (hq : ∀ᶠ x in l, q x ≠ 0) (loss : ℕ) {D : ℝ} (hD : 0 ≤ D)
    (hg : ∀ᶠ x in l, |g x| ≤ D / |q x| ^ loss) :
    PowerFlat l q (fun x => f x * g x) := by
  intro n
  obtain ⟨C, hC, hfb⟩ := hf (n + loss)
  refine ⟨C * D, mul_nonneg hC hD, ?_⟩
  filter_upwards [hq, hfb, hg] with x hqx hfx hgx
  have hden : |q x| ^ loss ≠ 0 := pow_ne_zero _ (abs_ne_zero.mpr hqx)
  calc
    |f x * g x| = |f x| * |g x| := abs_mul _ _
    _ ≤ (C * |q x| ^ (n + loss)) * (D / |q x| ^ loss) :=
      mul_le_mul hfx hgx (abs_nonneg _)
        (mul_nonneg hC (pow_nonneg (abs_nonneg _) _))
    _ = ((C * D) * |q x| ^ n) * (|q x| ^ loss / |q x| ^ loss) := by
      rw [pow_add]
      ring
    _ = (C * D) * |q x| ^ n := by rw [div_self hden, mul_one]

/-- Stage bounds with unbounded natural exponents imply flatness even after
subtracting a fixed natural loss. Each stage has its own constant and eventual
neighborhood; no uniformity of these quantities in the stage is assumed. -/
theorem powerFlat_of_stage_bounds {exponent : ℕ → ℕ} (loss : ℕ)
    (hexponent : ∀ n : ℕ, ∃ j : ℕ, n ≤ exponent j)
    (hq : ∀ᶠ x in l, |q x| ≤ 1)
    (hstage : ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ x in l, |f x| ≤ C * |q x| ^ (exponent j - loss)) :
    PowerFlat l q f := by
  intro n
  obtain ⟨j, hj⟩ := hexponent (n + loss)
  obtain ⟨C, hC, hb⟩ := hstage j
  have hn : n ≤ exponent j - loss := Nat.le_sub_of_add_le hj
  refine ⟨C, hC, ?_⟩
  filter_upwards [hq, hb] with x hqx hfx
  exact hfx.trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_of_le_one (abs_nonneg _) hqx hn) hC)

/-- Flatness gives an actual zero limit when the scale tends to zero.
This is a scalar limit theorem, not a theorem about differentiability. -/
theorem PowerFlat.tendsto_zero (hf : PowerFlat l q f)
    (hq : Tendsto q l (𝓝 0)) : Tendsto f l (𝓝 0) := by
  obtain ⟨C, _, hb⟩ := hf 1
  apply squeeze_zero_norm' (f := f) (a := fun x => C * |q x|)
  · simpa only [Real.norm_eq_abs, pow_one] using hb
  · simpa only [abs_zero, mul_zero] using hq.abs.const_mul C

/-- The zero limit survives every fixed inverse-power loss. -/
theorem PowerFlat.div_pow_tendsto_zero (hf : PowerFlat l q f)
    (hq : Tendsto q l (𝓝 0)) (hq_ne : ∀ᶠ x in l, q x ≠ 0) (loss : ℕ) :
    Tendsto (fun x => f x / q x ^ loss) l (𝓝 0) :=
  (hf.div_pow hq_ne loss).tendsto_zero hq

end NavierStokes.Flatness

end

end

@[expose] public section

noncomputable section

namespace NavierStokes.ResidualStability

open Set Filter Function
open scoped Topology BigOperators ContDiff

section Scalar

variable {X : Type*} {l : Filter X} {q f g : X → ℝ}

theorem scalarFlat_mono (hf : Flatness.PowerFlat l q f)
    (hgf : ∀ᶠ x in l, |g x| ≤ |f x|) : Flatness.PowerFlat l q g := by
  intro N
  obtain ⟨C, hC, hb⟩ := hf N
  exact ⟨C, hC, by filter_upwards [hgf, hb] with x h₁ h₂; exact h₁.trans h₂⟩

theorem scalarFlat_const_mul (c : ℝ) (hf : Flatness.PowerFlat l q f) :
    Flatness.PowerFlat l q (fun x => c * f x) := by
  intro N
  obtain ⟨C, hC, hb⟩ := hf N
  refine ⟨|c| * C, mul_nonneg (abs_nonneg c) hC, ?_⟩
  filter_upwards [hb] with x hx
  simpa only [abs_mul, mul_assoc] using mul_le_mul_of_nonneg_left hx (abs_nonneg c)

theorem scalarFlat_zero : Flatness.PowerFlat l q (fun _ => 0) := by
  intro N
  exact ⟨0, le_rfl, Filter.Eventually.of_forall (fun _ => by simp)⟩

theorem scalarFlat_sum {ι : Type*} (s : Finset ι) (f : ι → X → ℝ)
    (hf : ∀ i ∈ s, Flatness.PowerFlat l q (f i)) :
    Flatness.PowerFlat l q (fun x => ∑ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (scalarFlat_zero (l := l) (q := q))
  | @insert i s hi ih =>
      simpa only [Finset.sum_insert hi] using
        (hf i (Finset.mem_insert_self _ _)).add
          (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

end Scalar

section Jets

variable {D E F G : Type*}
  [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- Every actual derivative decays faster than each fixed natural power. -/
def AllJetsFlat (l : Filter D) (q : D → ℝ) (f : D → E) : Prop :=
  ∀ m : ℕ, Flatness.PowerFlat l q (fun x => ‖iteratedFDeriv ℝ m f x‖)

/-- Each actual derivative has a fixed inverse-power bound. The power and
constant may depend on the derivative order, but not on the point. -/
def AllJetsGrowth (l : Filter D) (q : D → ℝ) (f : D → E) : Prop :=
  ∀ m : ℕ, ∃ K : ℕ, ∃ C : ℝ, 0 ≤ C ∧
    ∀ᶠ x in l, ‖iteratedFDeriv ℝ m f x‖ ≤ C / |q x| ^ K

variable {l : Filter D} {q : D → ℝ} {f : D → E} {g : D → F} {U : Set D}

theorem AllJetsFlat.fderiv (hf : AllJetsFlat l q f) : AllJetsFlat l q (fderiv ℝ f) := by
  intro m
  simpa only [norm_iteratedFDeriv_fderiv] using hf (m + 1)

theorem AllJetsGrowth.fderiv (hf : AllJetsGrowth l q f) :
    AllJetsGrowth l q (fderiv ℝ f) := by
  intro m
  simpa only [norm_iteratedFDeriv_fderiv] using hf (m + 1)

theorem AllJetsFlat.growth (hf : AllJetsFlat l q f) : AllJetsGrowth l q f := by
  intro m
  obtain ⟨C, hC, hb⟩ := hf m 0
  exact ⟨0, C, hC, by simpa only [abs_norm, pow_zero, mul_one, div_one] using hb⟩

theorem iteratedFDeriv_eqOn {f g : D → E} (hU : IsOpen U) (hfg : EqOn f g U)
    (m : ℕ) : EqOn (iteratedFDeriv ℝ m f) (iteratedFDeriv ℝ m g) U := by
  intro x hx
  have h : f =ᶠ[𝓝 x] g := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact hfg hy
  have h' : f =ᶠ[𝓝[univ] x] g := by simpa only [nhdsWithin_univ] using h
  simpa only [iteratedFDerivWithin_univ] using
    h'.iteratedFDerivWithin_eq h.self_of_nhds m

theorem AllJetsFlat.congr_on {g : D → E} (hf : AllJetsFlat l q f)
    (hU : IsOpen U) (hl : ∀ᶠ x in l, x ∈ U) (hfg : EqOn f g U) :
    AllJetsFlat l q g := by
  intro m
  apply scalarFlat_mono (hf m)
  filter_upwards [hl] with x hx
  rw [iteratedFDeriv_eqOn hU hfg m hx]

theorem AllJetsGrowth.congr_on {g : D → E} (hf : AllJetsGrowth l q f)
    (hU : IsOpen U) (hl : ∀ᶠ x in l, x ∈ U) (hfg : EqOn f g U) :
    AllJetsGrowth l q g := by
  intro m
  obtain ⟨K, C, hC, hb⟩ := hf m
  refine ⟨K, C, hC, ?_⟩
  filter_upwards [hl, hb] with x hx hbound
  rwa [iteratedFDeriv_eqOn hU hfg m hx] at hbound

theorem norm_jet_linear_map (L : E →L[ℝ] F) (hU : IsOpen U)
    (hf : ContDiffOn ℝ ∞ f U) {x : D} (hx : x ∈ U) (m : ℕ) :
    ‖iteratedFDeriv ℝ m (fun y => L (f y)) x‖ ≤ ‖L‖ * ‖iteratedFDeriv ℝ m f x‖ := by
  change ‖iteratedFDeriv ℝ m (L ∘ f) x‖ ≤ _
  rw [L.iteratedFDeriv_comp_left (hf.contDiffAt (hU.mem_nhds hx))
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl m)]
  exact L.norm_compContinuousMultilinearMap_le _

theorem AllJetsFlat.linear_map (hf : AllJetsFlat l q f) (L : E →L[ℝ] F)
    (hU : IsOpen U) (hl : ∀ᶠ x in l, x ∈ U) (hs : ContDiffOn ℝ ∞ f U) :
    AllJetsFlat l q (fun x => L (f x)) := by
  intro m
  apply scalarFlat_mono (scalarFlat_const_mul ‖L‖ (hf m))
  filter_upwards [hl] with x hx
  rw [abs_norm]
  exact (norm_jet_linear_map L hU hs hx m).trans (le_abs_self _)

theorem AllJetsGrowth.linear_map (hf : AllJetsGrowth l q f) (L : E →L[ℝ] F)
    (hU : IsOpen U) (hl : ∀ᶠ x in l, x ∈ U) (hs : ContDiffOn ℝ ∞ f U) :
    AllJetsGrowth l q (fun x => L (f x)) := by
  intro m
  obtain ⟨K, C, hC, hb⟩ := hf m
  refine ⟨K, ‖L‖ * C, mul_nonneg (norm_nonneg _) hC, ?_⟩
  filter_upwards [hl, hb] with x hx hbound
  calc
    _ ≤ ‖L‖ * ‖iteratedFDeriv ℝ m f x‖ := norm_jet_linear_map L hU hs hx m
    _ ≤ ‖L‖ * (C / |q x| ^ K) := mul_le_mul_of_nonneg_left hbound (norm_nonneg _)
    _ = (‖L‖ * C) / |q x| ^ K := by ring

theorem AllJetsFlat.add {g : D → E} (hf : AllJetsFlat l q f) (hg : AllJetsFlat l q g)
    (hU : IsOpen U) (hl : ∀ᶠ x in l, x ∈ U)
    (hsf : ContDiffOn ℝ ∞ f U) (hsg : ContDiffOn ℝ ∞ g U) :
    AllJetsFlat l q (fun x => f x + g x) := by
  intro m
  apply scalarFlat_mono ((hf m).add (hg m))
  filter_upwards [hl] with x hx
  have hfm := (hsf.contDiffAt (hU.mem_nhds hx)).of_le
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl m)
  have hgm := (hsg.contDiffAt (hU.mem_nhds hx)).of_le
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl m)
  rw [abs_norm, fun_iteratedFDeriv_add_apply hfm hgm]
  exact (norm_add_le _ _).trans (le_abs_self _)

theorem AllJetsFlat.neg (hf : AllJetsFlat l q f)
    (hU : IsOpen U) (hl : ∀ᶠ x in l, x ∈ U) (hs : ContDiffOn ℝ ∞ f U) :
    AllJetsFlat l q (fun x => -f x) := by
  simpa using hf.linear_map (-ContinuousLinearMap.id ℝ E) hU hl hs

theorem AllJetsFlat.sub {g : D → E} (hf : AllJetsFlat l q f) (hg : AllJetsFlat l q g)
    (hU : IsOpen U) (hl : ∀ᶠ x in l, x ∈ U)
    (hsf : ContDiffOn ℝ ∞ f U) (hsg : ContDiffOn ℝ ∞ g U) :
    AllJetsFlat l q (fun x => f x - g x) := by
  simpa only [sub_eq_add_neg] using hf.add (hg.neg hU hl hsg) hU hl hsf hsg.neg

theorem AllJetsFlat.zero : AllJetsFlat l q (fun _ : D => (0 : E)) := by
  intro m
  simpa only [iteratedFDeriv_fun_zero, Pi.zero_apply, norm_zero] using
    (scalarFlat_zero (l := l) (q := q))

theorem AllJetsFlat.sum {ι : Type*} (s : Finset ι) (f : ι → D → E)
    (hU : IsOpen U) (hl : ∀ᶠ x in l, x ∈ U)
    (hs : ∀ i ∈ s, ContDiffOn ℝ ∞ (f i) U) (hf : ∀ i ∈ s, AllJetsFlat l q (f i)) :
    AllJetsFlat l q (fun x => ∑ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (AllJetsFlat.zero (l := l) (q := q) (E := E))
  | @insert i s hi ih =>
      simpa only [Finset.sum_insert hi] using
        (hf i (Finset.mem_insert_self _ _)).add
          (ih (fun j hj => hs j (Finset.mem_insert_of_mem hj))
            (fun j hj => hf j (Finset.mem_insert_of_mem hj))) hU hl
          (hs i (Finset.mem_insert_self _ _))
          (ContDiffOn.sum (fun j hj => hs j (Finset.mem_insert_of_mem hj)))

/-- Leibniz plus a fixed power loss in one factor gives flatness of the actual
bilinear product. The bound uses only jets through the requested order. -/
theorem AllJetsFlat.bilinear_growth_left (hg : AllJetsFlat l q g)
    (hf : AllJetsGrowth l q f) (L : E →L[ℝ] F →L[ℝ] G)
    (hU : IsOpen U) (hl : ∀ᶠ x in l, x ∈ U) (hq : ∀ᶠ x in l, q x ≠ 0)
    (hsf : ContDiffOn ℝ ∞ f U) (hsg : ContDiffOn ℝ ∞ g U) :
    AllJetsFlat l q (fun x => L (f x) (g x)) := by
  intro m
  have hterm (i : ℕ) : Flatness.PowerFlat l q (fun x => (m.choose i : ℝ) *
      ‖iteratedFDeriv ℝ i f x‖ * ‖iteratedFDeriv ℝ (m - i) g x‖) := by
    obtain ⟨K, C, hC, hb⟩ := hf i
    have hprod := (hg (m - i)).mul_of_power_bound
      (g := fun x => ‖iteratedFDeriv ℝ i f x‖) hq K hC
      (by simpa only [abs_norm] using hb)
    have hscale := scalarFlat_const_mul (m.choose i : ℝ) hprod
    convert! hscale using 1
    ext x
    ring
  apply scalarFlat_mono (scalarFlat_const_mul ‖L‖
    (scalarFlat_sum (Finset.range (m + 1)) _ (fun i _ => hterm i)))
  filter_upwards [hl] with x hx
  rw [abs_norm]
  exact (JetBounds.norm_iteratedFDeriv_bilinear_le_on L hU hsf hsg hx
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl m)).trans (le_abs_self _)

theorem AllJetsFlat.bilinear_growth_right (hf : AllJetsFlat l q f)
    (hg : AllJetsGrowth l q g) (L : E →L[ℝ] F →L[ℝ] G)
    (hU : IsOpen U) (hl : ∀ᶠ x in l, x ∈ U) (hq : ∀ᶠ x in l, q x ≠ 0)
    (hsf : ContDiffOn ℝ ∞ f U) (hsg : ContDiffOn ℝ ∞ g U) :
    AllJetsFlat l q (fun x => L (f x) (g x)) :=
  hf.bilinear_growth_left hg L.flip hU hl hq hsg hsf

end Jets

section PhysicalOperators

open ProblemStatement

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Restrict a full spacetime derivative to the spatial directions. -/
def spaceRestriction (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] :
    (SpaceTime →L[ℝ] V) →L[ℝ] (Space →L[ℝ] V) :=
  (ContinuousLinearMap.compL ℝ Space SpaceTime V).flip (ContinuousLinearMap.inr ℝ ℝ Space)

theorem space_fderiv_eq_full {f : SpaceTime → V} {z : SpaceTime}
    (hf : DifferentiableAt ℝ f z) :
    fderiv ℝ (fun y : Space => f (z.1, y)) z.2 = spaceRestriction V (fderiv ℝ f z) :=
  (hf.hasFDerivAt.comp z.2 (hasFDerivAt_prodMk_right z.1 z.2)).fderiv

theorem temporalDerivative_eq_full {f : VelocityField} {z : SpaceTime}
    (hf : DifferentiableAt ℝ f z) :
    temporalDerivative f z.1 z.2 = fderiv ℝ f z (1, 0) := by
  have h : fderiv ℝ (fun t : ℝ => f (t, z.2)) z.1 =
      (fderiv ℝ f z).comp (ContinuousLinearMap.inl ℝ ℝ Space) :=
    (hf.hasFDerivAt.comp z.1 (hasFDerivAt_prodMk_left (𝕜 := ℝ) z.1 z.2)).fderiv
  exact congrArg (fun L : ℝ →L[ℝ] Space => L 1) h

variable {l : Filter SpaceTime} {q : SpaceTime → ℝ} {U : Set SpaceTime}

theorem AllJetsFlat.space_fderiv {f : SpaceTime → V} (hf : AllJetsFlat l q f)
    (hU : IsOpen U) (hl : ∀ᶠ z in l, z ∈ U) (hs : ContDiffOn ℝ ∞ f U) :
    AllJetsFlat l q (fun z => _root_.fderiv ℝ (fun y : Space => f (z.1, y)) z.2) := by
  have hfull : ContDiffOn ℝ ∞ (_root_.fderiv ℝ f) U := hs.fderiv_of_isOpen hU (by simp)
  apply (hf.fderiv.linear_map (spaceRestriction V) hU hl hfull).congr_on hU hl
  intro z hz
  exact (space_fderiv_eq_full ((hs.contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp))).symm

theorem AllJetsGrowth.space_fderiv {f : SpaceTime → V} (hf : AllJetsGrowth l q f)
    (hU : IsOpen U) (hl : ∀ᶠ z in l, z ∈ U) (hs : ContDiffOn ℝ ∞ f U) :
    AllJetsGrowth l q (fun z => _root_.fderiv ℝ (fun y : Space => f (z.1, y)) z.2) := by
  have hfull : ContDiffOn ℝ ∞ (_root_.fderiv ℝ f) U := hs.fderiv_of_isOpen hU (by simp)
  apply (hf.fderiv.linear_map (spaceRestriction V) hU hl hfull).congr_on hU hl
  intro z hz
  exact (space_fderiv_eq_full ((hs.contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp))).symm

theorem AllJetsFlat.temporalDerivative {f : VelocityField} (hf : AllJetsFlat l q f)
    (hU : IsOpen U) (hl : ∀ᶠ z in l, z ∈ U) (hs : ContDiffOn ℝ ∞ f U) :
    AllJetsFlat l q (fun z => temporalDerivative f z.1 z.2) := by
  have hfull : ContDiffOn ℝ ∞ (_root_.fderiv ℝ f) U := hs.fderiv_of_isOpen hU (by simp)
  apply (hf.fderiv.linear_map (ContinuousLinearMap.apply ℝ Space (1, 0)) hU hl hfull).congr_on hU hl
  intro z hz
  exact (temporalDerivative_eq_full
    ((hs.contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp))).symm

theorem AllJetsFlat.pressureGradient {p : PressureField} (hp : AllJetsFlat l q p)
    (hU : IsOpen U) (hl : ∀ᶠ z in l, z ∈ U) (hs : ContDiffOn ℝ ∞ p U) :
    AllJetsFlat l q (fun z => pressureGradient p z.1 z.2) := by
  have hD := ResidualRegularity.contDiffOn_space_fderiv hU hs (m := ∞) (by simp)
  have hflatD := hp.space_fderiv hU hl hs
  unfold ProblemStatement.pressureGradient
  apply AllJetsFlat.sum Finset.univ _ hU hl
  · intro i _
    exact (hD.clm_apply contDiffOn_const).smul contDiffOn_const
  · intro i _
    have hi := hflatD.linear_map (ContinuousLinearMap.apply ℝ ℝ (coordinateVector i)) hU hl hD
    exact hi.linear_map ((ContinuousLinearMap.id ℝ ℝ).smulRight (coordinateVector i))
      hU hl (hD.clm_apply contDiffOn_const)

theorem AllJetsFlat.spatialLaplacian {f : VelocityField} (hf : AllJetsFlat l q f)
    (hU : IsOpen U) (hl : ∀ᶠ z in l, z ∈ U) (hs : ContDiffOn ℝ ∞ f U) :
    AllJetsFlat l q (fun z => spatialLaplacian f z.1 z.2) := by
  have hD := ResidualRegularity.contDiffOn_spatialDerivative hU hs
  have hflatD := hf.space_fderiv hU hl hs
  unfold ProblemStatement.spatialLaplacian
  apply AllJetsFlat.sum Finset.univ _ hU hl
  · intro i _
    exact (ResidualRegularity.contDiffOn_space_fderiv hU
      (hD.clm_apply contDiffOn_const) (m := ∞) (by simp)).clm_apply contDiffOn_const
  · intro i _
    have hi := hflatD.linear_map (ContinuousLinearMap.apply ℝ Space (coordinateVector i)) hU hl hD
    have his : ContDiffOn ℝ ∞
        (fun z => spatialDerivative f z.1 z.2 (coordinateVector i)) U :=
      hD.clm_apply contDiffOn_const
    exact (hi.space_fderiv hU hl his).linear_map
      (ContinuousLinearMap.apply ℝ Space (coordinateVector i)) hU hl
      (ResidualRegularity.contDiffOn_space_fderiv hU his (m := ∞) (by simp))

theorem spatialSlice_differentiable {f : SpaceTime → V}
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) {z : SpaceTime} (hz : z ∈ U) :
    DifferentiableAt ℝ (fun y : Space => f (z.1, y)) z.2 :=
  ((hf.contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp)).comp z.2
    (hasFDerivAt_prodMk_right z.1 z.2).differentiableAt

theorem timeSlice_differentiable {f : SpaceTime → V}
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) {z : SpaceTime} (hz : z ∈ U) :
    DifferentiableAt ℝ (fun t : ℝ => f (t, z.2)) z.1 :=
  ((hf.contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp)).comp z.1
    (hasFDerivAt_prodMk_left z.1 z.2).differentiableAt

/-- Local version of the Laplacian additivity used in `ResidualCalculus`.
Only smoothness on the open domain is needed, not on an entire spatial slice. -/
theorem spatialLaplacian_add_on {u w : VelocityField} (hU : IsOpen U)
    (hu : ContDiffOn ℝ ∞ u U) (hw : ContDiffOn ℝ ∞ w U)
    {z : SpaceTime} (hz : z ∈ U) :
    spatialLaplacian (fun y => u y + w y) z.1 z.2 =
      spatialLaplacian u z.1 z.2 + spatialLaplacian w z.1 z.2 := by
  unfold spatialLaplacian
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have heq : (fun y : Space => spatialDerivative (fun z => u z + w z) z.1 y (coordinateVector i))
      =ᶠ[𝓝 z.2] (fun y => spatialDerivative u z.1 y (coordinateVector i) +
        spatialDerivative w z.1 y (coordinateVector i)) := by
    have hmem : ∀ᶠ y : Space in 𝓝 z.2, (z.1, y) ∈ U :=
      (continuousAt_const.prodMk continuousAt_id) (hU.mem_nhds hz)
    filter_upwards [hmem] with y hy
    rw [ResidualCalculus.spatialDerivative_add u w z.1 y
      (spatialSlice_differentiable hU hu hy) (spatialSlice_differentiable hU hw hy)]
    rfl
  have hdu : ContDiffOn ℝ ∞
      (fun y => spatialDerivative u y.1 y.2 (coordinateVector i)) U :=
    (ResidualRegularity.contDiffOn_spatialDerivative hU hu).clm_apply contDiffOn_const
  have hdw : ContDiffOn ℝ ∞
      (fun y => spatialDerivative w y.1 y.2 (coordinateVector i)) U :=
    (ResidualRegularity.contDiffOn_spatialDerivative hU hw).clm_apply contDiffOn_const
  rw [heq.fderiv_eq, fderiv_fun_add
    (spatialSlice_differentiable hU hdu hz) (spatialSlice_differentiable hU hdw hz)]
  rfl

/-- The exact perturbation identity now holds on an arbitrary open spacetime
domain, using the concrete first-order identities from `ResidualCalculus`. -/
theorem residual_add_sub_on {u w : VelocityField} {p r : PressureField}
    (hU : IsOpen U) (hu : ContDiffOn ℝ ∞ u U) (hw : ContDiffOn ℝ ∞ w U)
    (hp : ContDiffOn ℝ ∞ p U) (hr : ContDiffOn ℝ ∞ r U)
    {z : SpaceTime} (hz : z ∈ U) :
    navierStokesResidual (fun y => u y + w y) (fun y => p y + r y) z.1 z.2 -
      navierStokesResidual u p z.1 z.2 =
        temporalDerivative w z.1 z.2 - spatialLaplacian w z.1 z.2 + pressureGradient r z.1 z.2 +
          spatialDerivative u z.1 z.2 (w z) + spatialDerivative w z.1 z.2 (u z) +
          spatialDerivative w z.1 z.2 (w z) := by
  unfold navierStokesResidual
  rw [ResidualCalculus.temporalDerivative_add u w z.1 z.2
      (timeSlice_differentiable hU hu hz) (timeSlice_differentiable hU hw hz),
    ResidualCalculus.advection_add u w z.1 z.2
      (spatialSlice_differentiable hU hu hz) (spatialSlice_differentiable hU hw hz),
    spatialLaplacian_add_on hU hu hw hz,
    ResidualCalculus.pressureGradient_add p r z.1 z.2
      (spatialSlice_differentiable hU hp hz) (spatialSlice_differentiable hU hr hz)]
  unfold advection
  abel

/-- The difference of the two actual viscosity-one Navier--Stokes residuals. -/
def residualDifference (u w : VelocityField) (p r : PressureField) : VelocityField :=
  fun z => navierStokesResidual (fun y => u y + w y) (fun y => p y + r y) z.1 z.2 -
    navierStokesResidual u p z.1 z.2

/-- Flat perturbations preserve all-jet residual flatness relative to any
smooth background with fixed-power jet growth. No residual estimate is an
input. The linear terms use at most two extra derivatives of the perturbation;
the transport products use at most one extra derivative. -/
theorem allJetsFlat_residualDifference {u w : VelocityField} {p r : PressureField}
    (hU : IsOpen U) (hl : ∀ᶠ z in l, z ∈ U) (hq : ∀ᶠ z in l, q z ≠ 0)
    (hu : ContDiffOn ℝ ∞ u U) (hw : ContDiffOn ℝ ∞ w U)
    (hp : ContDiffOn ℝ ∞ p U) (hr : ContDiffOn ℝ ∞ r U)
    (hgrowth : AllJetsGrowth l q u) (hwflat : AllJetsFlat l q w)
    (hrflat : AllJetsFlat l q r) : AllJetsFlat l q (residualDifference u w p r) := by
  let L : (Space →L[ℝ] Space) →L[ℝ] Space →L[ℝ] Space :=
    (ContinuousLinearMap.apply ℝ Space).flip
  have hDu := ResidualRegularity.contDiffOn_spatialDerivative hU hu
  have hDw := ResidualRegularity.contDiffOn_spatialDerivative hU hw
  have hDug := hgrowth.space_fderiv hU hl hu
  have hDwf := hwflat.space_fderiv hU hl hw
  have hcross₁ : AllJetsFlat l q (fun z => spatialDerivative u z.1 z.2 (w z)) :=
    hwflat.bilinear_growth_left hDug L hU hl hq hDu hw
  have hcross₂ : AllJetsFlat l q (fun z => spatialDerivative w z.1 z.2 (u z)) :=
    hDwf.bilinear_growth_right hgrowth L hU hl hq hDw hu
  have hself : AllJetsFlat l q (fun z => spatialDerivative w z.1 z.2 (w z)) :=
    hwflat.bilinear_growth_left hDwf.growth L hU hl hq hDw hw
  have htime := ResidualRegularity.contDiffOn_temporalDerivative hU hw
  have hlap := ResidualRegularity.contDiffOn_spatialLaplacian hU hw
  have hgrad := ResidualRegularity.contDiffOn_pressureGradient hU hr
  have hlinear := ((hwflat.temporalDerivative hU hl hw).sub
    (hwflat.spatialLaplacian hU hl hw) hU hl htime hlap).add
      (hrflat.pressureGradient hU hl hr) hU hl (htime.sub hlap) hgrad
  have hfirst := hlinear.add hcross₁ hU hl ((htime.sub hlap).add hgrad) (hDu.clm_apply hw)
  have hsecond := hfirst.add hcross₂ hU hl
    (((htime.sub hlap).add hgrad).add (hDu.clm_apply hw)) (hDw.clm_apply hu)
  have hall := hsecond.add hself hU hl
    ((((htime.sub hlap).add hgrad).add (hDu.clm_apply hw)).add (hDw.clm_apply hu))
    (hDw.clm_apply hw)
  apply hall.congr_on hU hl
  intro z hz
  exact (residual_add_sub_on hU hu hw hp hr hz).symm

end PhysicalOperators

section QuantitativeJetAlgebra

variable {D E F G : Type*}
  [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem norm_jet_add_le {U : Set D} {f g : D → E} (hU : IsOpen U)
    (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U) {x : D} (hx : x ∈ U) (m : ℕ) :
    ‖iteratedFDeriv ℝ m (fun y => f y + g y) x‖ ≤
      ‖iteratedFDeriv ℝ m f x‖ + ‖iteratedFDeriv ℝ m g x‖ := by
  rw [fun_iteratedFDeriv_add_apply
    ((hf.contDiffAt (hU.mem_nhds hx)).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl m))
    ((hg.contDiffAt (hU.mem_nhds hx)).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl m))]
  exact norm_add_le _ _

theorem norm_jet_neg (f : D → E) (x : D) (m : ℕ) :
    ‖iteratedFDeriv ℝ m (fun y => -f y) x‖ = ‖iteratedFDeriv ℝ m f x‖ := by
  change ‖iteratedFDeriv ℝ m (-f) x‖ = _
  rw [iteratedFDeriv_neg_apply, norm_neg]

theorem norm_jet_sub_le {U : Set D} {f g : D → E} (hU : IsOpen U)
    (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U) {x : D} (hx : x ∈ U) (m : ℕ) :
    ‖iteratedFDeriv ℝ m (fun y => f y - g y) x‖ ≤
      ‖iteratedFDeriv ℝ m f x‖ + ‖iteratedFDeriv ℝ m g x‖ := by
  simpa only [sub_eq_add_neg, norm_jet_neg] using norm_jet_add_le hU hf hg.neg hx m

theorem norm_jet_linear_map_fderiv (L : (D →L[ℝ] E) →L[ℝ] F)
    {U : Set D} {f : D → E} (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U)
    {x : D} (hx : x ∈ U) (m : ℕ) :
    ‖iteratedFDeriv ℝ m (fun y => L (fderiv ℝ f y)) x‖ ≤
      ‖L‖ * ‖iteratedFDeriv ℝ (m + 1) f x‖ := by
  have h := norm_jet_linear_map L hU (hf.fderiv_of_isOpen hU (by simp)) hx m
  simpa only [norm_iteratedFDeriv_fderiv] using h

/-- The pointwise finite-order form of the Leibniz estimate. The majorants
need only bound jets at this point; they may depend on the point and stage. -/
theorem norm_jet_bilinear_bound (L : E →L[ℝ] F →L[ℝ] G) {U : Set D}
    {f : D → E} {g : D → F} (hU : IsOpen U)
    (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U)
    {x : D} (hx : x ∈ U) (m : ℕ) {A B : ℝ}
    (hA : ∀ k : ℕ, k ≤ m → ‖iteratedFDeriv ℝ k f x‖ ≤ A)
    (hB : ∀ k : ℕ, k ≤ m → ‖iteratedFDeriv ℝ k g x‖ ≤ B) :
    ‖iteratedFDeriv ℝ m (fun y => L (f y) (g y)) x‖ ≤ ‖L‖ * (2 : ℝ) ^ m * A * B := by
  have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA 0 (Nat.zero_le _))
  have hsum : (∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) *
      ‖iteratedFDeriv ℝ i f x‖ * ‖iteratedFDeriv ℝ (m - i) g x‖) ≤
      (2 : ℝ) ^ m * A * B := by
    calc
      _ ≤ ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * A * B := by
        apply Finset.sum_le_sum
        intro i hi
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left (hA i (Nat.le_of_lt_succ (Finset.mem_range.mp hi)))
            (Nat.cast_nonneg _))
          (hB (m - i) (Nat.sub_le _ _)) (norm_nonneg _)
          (mul_nonneg (Nat.cast_nonneg _) hA0)
      _ = (2 : ℝ) ^ m * A * B := by
        rw [← Finset.sum_mul, ← Finset.sum_mul]
        congr 2
        exact_mod_cast Nat.sum_range_choose m
  exact (JetBounds.norm_iteratedFDeriv_bilinear_le_on L hU hf hg hx
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl m)).trans
      ((mul_le_mul_of_nonneg_left hsum (norm_nonneg L)).trans_eq (by ring))

end QuantitativeJetAlgebra

-- The norm of a linear functional on the second-derivative space has three
-- nested continuous-linear-map types.

section FullJetExpression

open ProblemStatement

/-- Cache the standard `NormedAddCommGroup (SpaceTime →L[ℝ] SpaceTime →L[ℝ] Space)` instance to
shorten typeclass synthesis. -/
local instance instResidualStability1 : NormedAddCommGroup (SpaceTime →L[ℝ] SpaceTime →L[ℝ] Space)
    :=
  inferInstance
/-- Cache the standard `NormedSpace ℝ (SpaceTime →L[ℝ] SpaceTime →L[ℝ] Space)` instance to
shorten typeclass synthesis. -/
local instance instResidualStability2 : NormedSpace ℝ (SpaceTime →L[ℝ] SpaceTime →L[ℝ] Space) :=
  inferInstance

theorem norm_iteratedFDeriv_spatialCurl_le {U : Set SpaceTime} {A : VelocityField}
    (hU : IsOpen U) (hA : ContDiffOn ℝ ∞ A U) {z : SpaceTime} (hz : z ∈ U) (m : ℕ) :
    ‖iteratedFDeriv ℝ m (SpatialCurl.spatialCurl A) z‖ ≤
      ‖SpatialCurl.curlLinear.comp (spaceRestriction Space)‖ *
        ‖iteratedFDeriv ℝ (m + 1) A z‖ := by
  have heq : EqOn (SpatialCurl.spatialCurl A)
      (fun y => (SpatialCurl.curlLinear.comp (spaceRestriction Space)) (fderiv ℝ A y)) U := by
    intro y hy
    unfold SpatialCurl.spatialCurl SpatialCurl.curl
    rw [space_fderiv_eq_full ((hA.contDiffAt (hU.mem_nhds hy)).differentiableAt (by simp))]
    rfl
  rw [iteratedFDeriv_eqOn hU heq m hz]
  exact norm_jet_linear_map_fderiv _ hU hA hz m

/-- Time jet, given by `ContinuousLinearMap.apply ℝ Space (1, 0)`. -/
def timeJet : (SpaceTime →L[ℝ] Space) →L[ℝ] Space :=
  ContinuousLinearMap.apply ℝ Space (1, 0)

/-- Laplace jet as an element of `(SpaceTime →L[ℝ] SpaceTime →L[ℝ] Space) →L[ℝ] Space`. -/
def laplaceJet : (SpaceTime →L[ℝ] SpaceTime →L[ℝ] Space) →L[ℝ] Space :=
  ∑ i : Fin 3,
    (ContinuousLinearMap.apply ℝ Space (0, coordinateVector i)).comp
      (ContinuousLinearMap.apply ℝ (SpaceTime →L[ℝ] Space) (0, coordinateVector i))

/-- Pressure jet as an element of `(SpaceTime →L[ℝ] ℝ) →L[ℝ] Space`. -/
def pressureJet : (SpaceTime →L[ℝ] ℝ) →L[ℝ] Space :=
  ∑ i : Fin 3,
    ((ContinuousLinearMap.id ℝ ℝ).smulRight (coordinateVector i)).comp
      (ContinuousLinearMap.apply ℝ ℝ (0, coordinateVector i))

@[simp] theorem laplaceJet_apply (L : SpaceTime →L[ℝ] SpaceTime →L[ℝ] Space) :
    laplaceJet L = ∑ i : Fin 3, L (0, coordinateVector i) (0, coordinateVector i) := by
  simp [laplaceJet]

@[simp] theorem pressureJet_apply (L : SpaceTime →L[ℝ] ℝ) :
    pressureJet L = ∑ i : Fin 3, L (0, coordinateVector i) • coordinateVector i := by
  simp [pressureJet]

theorem spatialLaplacian_eq_full {U : Set SpaceTime} {w : VelocityField}
    (hU : IsOpen U) (hw : ContDiffOn ℝ ∞ w U) {z : SpaceTime} (hz : z ∈ U) :
    spatialLaplacian w z.1 z.2 = laplaceJet (fderiv ℝ (fderiv ℝ w) z) := by
  rw [laplaceJet_apply]
  unfold spatialLaplacian
  apply Finset.sum_congr rfl
  intro i _
  have heq : (fun y : SpaceTime => spatialDerivative w y.1 y.2 (coordinateVector i))
      =ᶠ[𝓝 z] (fun y => fderiv ℝ w y (0, coordinateVector i)) := by
    filter_upwards [hU.mem_nhds hz] with y hy
    unfold spatialDerivative
    rw [space_fderiv_eq_full ((hw.contDiffAt (hU.mem_nhds hy)).differentiableAt (by simp))]
    rfl
  have hD : ContDiffOn ℝ ∞ (fderiv ℝ w) U := hw.fderiv_of_isOpen hU (by simp)
  have hfirst : HasFDerivAt (fun y : SpaceTime => fderiv ℝ w y (0, coordinateVector i))
      ((ContinuousLinearMap.apply ℝ Space (0, coordinateVector i)).comp
        (fderiv ℝ (fderiv ℝ w) z)) z := by
    let ev : (SpaceTime →L[ℝ] Space) →L[ℝ] Space :=
      ContinuousLinearMap.apply ℝ Space (0, coordinateVector i)
    change HasFDerivAt (ev ∘ fderiv ℝ w) (ev.comp (fderiv ℝ (fderiv ℝ w) z)) z
    exact ev.hasFDerivAt.comp z
      ((hD.contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp)).hasFDerivAt
  have hslice := hfirst.comp z.2 (hasFDerivAt_prodMk_right (𝕜 := ℝ) z.1 z.2)
  rw [ResidualRegularity.space_fderiv_congr heq]
  simpa only [Function.comp_def, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.apply_apply, ContinuousLinearMap.inr_apply] using
    congrArg (fun L : Space →L[ℝ] Space => L (coordinateVector i)) hslice.fderiv

theorem pressureGradient_eq_full {U : Set SpaceTime} {r : PressureField}
    (hU : IsOpen U) (hr : ContDiffOn ℝ ∞ r U) {z : SpaceTime} (hz : z ∈ U) :
    pressureGradient r z.1 z.2 = pressureJet (fderiv ℝ r z) := by
  rw [pressureJet_apply]
  unfold pressureGradient
  rw [space_fderiv_eq_full ((hr.contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp))]
  rfl

/-- Residual jet expression as an element of `VelocityField`. -/
def residualJetExpression (u w : VelocityField) (r : PressureField) : VelocityField :=
  fun z => timeJet (fderiv ℝ w z) - laplaceJet (fderiv ℝ (fderiv ℝ w) z) +
    pressureJet (fderiv ℝ r z) +
    spaceRestriction Space (fderiv ℝ u z) (w z) +
    spaceRestriction Space (fderiv ℝ w z) (u z) +
    spaceRestriction Space (fderiv ℝ w z) (w z)

theorem residualDifference_eq_jetExpression {U : Set SpaceTime}
    {u w : VelocityField} {p r : PressureField} (hU : IsOpen U)
    (hu : ContDiffOn ℝ ∞ u U) (hw : ContDiffOn ℝ ∞ w U)
    (hp : ContDiffOn ℝ ∞ p U) (hr : ContDiffOn ℝ ∞ r U) :
    EqOn (residualDifference u w p r) (residualJetExpression u w r) U := by
  intro z hz
  unfold residualDifference residualJetExpression
  rw [residual_add_sub_on hU hu hw hp hr hz,
    temporalDerivative_eq_full ((hw.contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp)),
    spatialLaplacian_eq_full hU hw hz, pressureGradient_eq_full hU hr hz]
  unfold spatialDerivative
  rw [space_fderiv_eq_full ((hu.contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp)),
    space_fderiv_eq_full ((hw.contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp))]
  rfl

/-- Quantitative fixed-order stability, with only pointwise hypotheses on the
actual jets. The background needs `m+1` derivatives, the velocity perturbation
`m+2`, and the pressure perturbation `m+1`. The three majorants may depend on
the point and on a truncation stage. Every displayed operator norm is fixed
independently of the fields, stage, and physical scale. -/
theorem residualDifference_jet_bound {U : Set SpaceTime}
    {u w : VelocityField} {p r : PressureField} (hU : IsOpen U)
    (hu : ContDiffOn ℝ ∞ u U) (hw : ContDiffOn ℝ ∞ w U)
    (hp : ContDiffOn ℝ ∞ p U) (hr : ContDiffOn ℝ ∞ r U)
    {z : SpaceTime} (hz : z ∈ U) (m : ℕ) {A W P : ℝ}
    (huBound : ∀ k : ℕ, k ≤ m + 1 → ‖iteratedFDeriv ℝ k u z‖ ≤ A)
    (hwBound : ∀ k : ℕ, k ≤ m + 2 → ‖iteratedFDeriv ℝ k w z‖ ≤ W)
    (hrBound : ∀ k : ℕ, k ≤ m + 1 → ‖iteratedFDeriv ℝ k r z‖ ≤ P) :
    ‖iteratedFDeriv ℝ m (residualDifference u w p r) z‖ ≤
      ‖timeJet‖ * W + ‖laplaceJet‖ * W + ‖pressureJet‖ * P +
      ‖spaceRestriction Space‖ * (2 : ℝ) ^ m * A * W +
      ‖spaceRestriction Space‖ * (2 : ℝ) ^ m * W * A +
      ‖spaceRestriction Space‖ * (2 : ℝ) ^ m * W * W := by
  let T : VelocityField := fun y => timeJet (fderiv ℝ w y)
  let L : VelocityField := fun y => laplaceJet (fderiv ℝ (fderiv ℝ w) y)
  let R : VelocityField := fun y => pressureJet (fderiv ℝ r y)
  let C₁ : VelocityField := fun y => spaceRestriction Space (fderiv ℝ u y) (w y)
  let C₂ : VelocityField := fun y => spaceRestriction Space (fderiv ℝ w y) (u y)
  let C₃ : VelocityField := fun y => spaceRestriction Space (fderiv ℝ w y) (w y)
  have hDu : ContDiffOn ℝ ∞ (fderiv ℝ u) U := hu.fderiv_of_isOpen hU (by simp)
  have hDw : ContDiffOn ℝ ∞ (fderiv ℝ w) U := hw.fderiv_of_isOpen hU (by simp)
  have hDDw : ContDiffOn ℝ ∞ (fderiv ℝ (fderiv ℝ w)) U :=
    hDw.fderiv_of_isOpen hU (by simp)
  have hDr : ContDiffOn ℝ ∞ (fderiv ℝ r) U := hr.fderiv_of_isOpen hU (by simp)
  have hTs : ContDiffOn ℝ ∞ T U := hDw.continuousLinearMap_comp timeJet
  have hLs : ContDiffOn ℝ ∞ L U := hDDw.continuousLinearMap_comp laplaceJet
  have hRs : ContDiffOn ℝ ∞ R U := hDr.continuousLinearMap_comp pressureJet
  have hC₁s : ContDiffOn ℝ ∞ C₁ U :=
    (hDu.continuousLinearMap_comp (spaceRestriction Space)).clm_apply hw
  have hC₂s : ContDiffOn ℝ ∞ C₂ U :=
    (hDw.continuousLinearMap_comp (spaceRestriction Space)).clm_apply hu
  have hC₃s : ContDiffOn ℝ ∞ C₃ U :=
    (hDw.continuousLinearMap_comp (spaceRestriction Space)).clm_apply hw
  have hT : ‖iteratedFDeriv ℝ m T z‖ ≤ ‖timeJet‖ * W := by
    apply (norm_jet_linear_map timeJet hU hDw hz m).trans
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    rw [norm_iteratedFDeriv_fderiv]
    exact hwBound (m + 1) (by omega)
  have hL : ‖iteratedFDeriv ℝ m L z‖ ≤ ‖laplaceJet‖ * W := by
    apply (norm_jet_linear_map laplaceJet hU hDDw hz m).trans
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    rw [norm_iteratedFDeriv_fderiv, norm_iteratedFDeriv_fderiv]
    exact hwBound (m + 1 + 1) (by omega)
  have hR : ‖iteratedFDeriv ℝ m R z‖ ≤ ‖pressureJet‖ * P := by
    apply (norm_jet_linear_map pressureJet hU hDr hz m).trans
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    rw [norm_iteratedFDeriv_fderiv]
    exact hrBound (m + 1) le_rfl
  have hu₀ : ∀ k : ℕ, k ≤ m → ‖iteratedFDeriv ℝ k u z‖ ≤ A :=
    fun k hk => huBound k (by omega)
  have hw₀ : ∀ k : ℕ, k ≤ m → ‖iteratedFDeriv ℝ k w z‖ ≤ W :=
    fun k hk => hwBound k (by omega)
  have hu₁ : ∀ k : ℕ, k ≤ m → ‖iteratedFDeriv ℝ k (fderiv ℝ u) z‖ ≤ A := by
    intro k hk
    rw [norm_iteratedFDeriv_fderiv]
    exact huBound (k + 1) (by omega)
  have hw₁ : ∀ k : ℕ, k ≤ m → ‖iteratedFDeriv ℝ k (fderiv ℝ w) z‖ ≤ W := by
    intro k hk
    rw [norm_iteratedFDeriv_fderiv]
    exact hwBound (k + 1) (by omega)
  have hC₁ : ‖iteratedFDeriv ℝ m C₁ z‖ ≤
      ‖spaceRestriction Space‖ * (2 : ℝ) ^ m * A * W :=
    norm_jet_bilinear_bound (spaceRestriction Space) hU hDu hw hz m hu₁ hw₀
  have hC₂ : ‖iteratedFDeriv ℝ m C₂ z‖ ≤
      ‖spaceRestriction Space‖ * (2 : ℝ) ^ m * W * A :=
    norm_jet_bilinear_bound (spaceRestriction Space) hU hDw hu hz m hw₁ hu₀
  have hC₃ : ‖iteratedFDeriv ℝ m C₃ z‖ ≤
      ‖spaceRestriction Space‖ * (2 : ℝ) ^ m * W * W :=
    norm_jet_bilinear_bound (spaceRestriction Space) hU hDw hw hz m hw₁ hw₀
  have hTL := (norm_jet_sub_le hU hTs hLs hz m).trans (add_le_add hT hL)
  have hTLR := (norm_jet_add_le hU (hTs.sub hLs) hRs hz m).trans (add_le_add hTL hR)
  have h₁ := (norm_jet_add_le hU ((hTs.sub hLs).add hRs) hC₁s hz m).trans
    (add_le_add hTLR hC₁)
  have h₂ := (norm_jet_add_le hU (((hTs.sub hLs).add hRs).add hC₁s) hC₂s hz m).trans
    (add_le_add h₁ hC₂)
  have h₃ := (norm_jet_add_le hU ((((hTs.sub hLs).add hRs).add hC₁s).add hC₂s) hC₃s hz m).trans
    (add_le_add h₂ hC₃)
  rw [iteratedFDeriv_eqOn hU (residualDifference_eq_jetExpression hU hu hw hp hr) m hz]
  exact h₃

end FullJetExpression

section ScaleDomain

open ProblemStatement

/-- Approach `q = 0` through positive scales while staying in the domain. -/
def scaleFilter (U : Set SpaceTime) (q : SpaceTime → ℝ) : Filter SpaceTime :=
  Filter.principal U ⊓ Filter.comap q (𝓝[>] (0 : ℝ))

theorem eventually_mem_scaleFilter (U : Set SpaceTime) (q : SpaceTime → ℝ) :
    ∀ᶠ z in scaleFilter U q, z ∈ U :=
  (show ∀ᶠ z in Filter.principal U, z ∈ U from by simp).filter_mono inf_le_left

theorem tendsto_scaleFilter (U : Set SpaceTime) (q : SpaceTime → ℝ) :
    Tendsto q (scaleFilter U q) (𝓝[>] (0 : ℝ)) :=
  tendsto_comap.mono_left inf_le_right

/-- Domain/scale form of the actual nonlinear stability theorem. All
asymptotics concern the displayed norms of actual physical derivatives. -/
theorem residualDifference_flat_at_scale {U : Set SpaceTime} {q : SpaceTime → ℝ}
    {u w : VelocityField} {p r : PressureField} (hU : IsOpen U)
    (hq : ∀ z ∈ U, 0 < q z)
    (hu : ContDiffOn ℝ ∞ u U) (hw : ContDiffOn ℝ ∞ w U)
    (hp : ContDiffOn ℝ ∞ p U) (hr : ContDiffOn ℝ ∞ r U)
    (hgrowth : AllJetsGrowth (scaleFilter U q) q u)
    (hwflat : AllJetsFlat (scaleFilter U q) q w)
    (hrflat : AllJetsFlat (scaleFilter U q) q r) :
    AllJetsFlat (scaleFilter U q) q (residualDifference u w p r) := by
  apply allJetsFlat_residualDifference hU (eventually_mem_scaleFilter U q) _
    hu hw hp hr hgrowth hwflat hrflat
  filter_upwards [eventually_mem_scaleFilter U q] with z hz
  exact ne_of_gt (hq z hz)

end ScaleDomain

end NavierStokes.ResidualStability
