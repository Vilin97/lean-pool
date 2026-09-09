/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.SmoothPathFamily
import LeanPool.NavierStokesAndEuler.NavierStokes.ViscousPropagator
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Topology.Algebra.Module.PerfectSpace

/-!
# Weighted estimates for actual parameter derivatives of linear ODE solutions

Parameter derivatives are genuine iterated Fréchet derivatives in prescribed
directions. The differentiated Volterra equation gives a triangular system;
the energy estimate, rather than an uncontrolled inverse norm, estimates it.
-/

@[expose] public section


namespace NavierStokes.WeightedODEJets

noncomputable section

open Set Filter Function MeasureTheory
open scoped Topology ContDiff InnerProductSpace

variable {P E F : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- One actual parameter derivative in a fixed direction. -/
noncomputable def directional (f : P → E) (v : P) : P → E :=
  fun p => fderiv ℝ f p v

/-- Successive actual directional Fréchet derivatives. Directions are applied
from the head of the word to its tail; the empty word means order zero. -/
noncomputable def jet (f : P → E) (l : List P) : P → E :=
  l.foldl (fun g v => directional g v) f

@[simp] theorem jet_nil (f : P → E) : jet f [] = f := rfl

@[simp] theorem jet_cons (f : P → E) (v : P) (l : List P) :
    jet f (v :: l) = jet (directional f v) l := rfl

/-- Restricting all directions to the unit ball converts the estimates to
uniform bounds for all mixed parameter derivatives of a given order. -/
def UnitWord (l : List P) : Prop := ∀ v ∈ l, ‖v‖ ≤ 1

omit [NormedSpace ℝ P] in
@[simp] theorem unitWord_nil : UnitWord ([] : List P) := by simp [UnitWord]

omit [NormedSpace ℝ P] in
@[simp] theorem unitWord_cons (v : P) (l : List P) :
    UnitWord (v :: l) ↔ ‖v‖ ≤ 1 ∧ UnitWord l := by simp [UnitWord]

theorem contDiffOn_directional {U : Set P} (hU : IsOpen U) {f : P → E}
    (hf : ContDiffOn ℝ ∞ f U) (v : P) :
    ContDiffOn ℝ ∞ (directional f v) U := by
  exact ((contDiffOn_infty_iff_fderiv_of_isOpen hU).mp hf).2.clm_apply contDiffOn_const

theorem contDiffOn_jet {U : Set P} (hU : IsOpen U) {f : P → E}
    (hf : ContDiffOn ℝ ∞ f U) (l : List P) : ContDiffOn ℝ ∞ (jet f l) U := by
  induction l generalizing f with
  | nil => exact hf
  | cons v l ih => exact ih (contDiffOn_directional hU hf v)

theorem directional_congr {U : Set P} (hU : IsOpen U) {f g : P → E}
    (heq : EqOn f g U) (v : P) : EqOn (directional f v) (directional g v) U := by
  intro p hp
  apply congrArg (fun L : P →L[ℝ] E => L v)
  apply Filter.EventuallyEq.fderiv_eq
  filter_upwards [hU.mem_nhds hp] with q hq
  exact heq hq

theorem jet_congr {U : Set P} (hU : IsOpen U) {f g : P → E}
    (heq : EqOn f g U) (l : List P) : EqOn (jet f l) (jet g l) U := by
  induction l generalizing f g with
  | nil => exact heq
  | cons v l ih => exact ih (directional_congr hU heq v)

theorem directional_add {U : Set P} (hU : IsOpen U) {f g : P → E}
    (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U) (v : P) :
    EqOn (directional (fun p => f p + g p) v)
      (fun p => directional f v p + directional g v p) U := by
  intro p hp
  have hdf := (hf p hp).contDiffAt (hU.mem_nhds hp)
  have hdg := (hg p hp).contDiffAt (hU.mem_nhds hp)
  exact congrArg (fun L : P →L[ℝ] E => L v)
    (fderiv_fun_add (hdf.differentiableAt (by simp)) (hdg.differentiableAt (by simp)))

theorem jet_add {U : Set P} (hU : IsOpen U) {f g : P → E}
    (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U) (l : List P) :
    EqOn (jet (fun p => f p + g p) l) (fun p => jet f l p + jet g l p) U := by
  induction l generalizing f g with
  | nil => intro p hp; rfl
  | cons v l ih =>
    exact (jet_congr hU (directional_add hU hf hg v) l).trans
      (ih (contDiffOn_directional hU hf v) (contDiffOn_directional hU hg v))

theorem directional_clm {U : Set P} (hU : IsOpen U) {f : P → E}
    (hf : ContDiffOn ℝ ∞ f U) (L : E →L[ℝ] F) (v : P) :
    EqOn (directional (fun p => L (f p)) v) (fun p => L (directional f v p)) U := by
  intro p hp
  have hdf := ((hf p hp).contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)
  exact congrArg (fun M : P →L[ℝ] F => M v) (L.hasFDerivAt.comp p hdf.hasFDerivAt).fderiv

theorem jet_clm {U : Set P} (hU : IsOpen U) {f : P → E}
    (hf : ContDiffOn ℝ ∞ f U) (L : E →L[ℝ] F) (l : List P) :
    EqOn (jet (fun p => L (f p)) l) (fun p => L (jet f l p)) U := by
  induction l generalizing f with
  | nil => intro p hp; rfl
  | cons v l ih =>
    exact (jet_congr hU (directional_clm hU hf L v) l).trans
      (ih (contDiffOn_directional hU hf v))

/-- The word formulation is exactly Mathlib's iterated Fréchet derivative,
with the reversal dictated by its convention for the order of arguments. -/
theorem jet_ofFn_reverse {U : Set P} (hU : IsOpen U) {f : P → E}
    (hf : ContDiffOn ℝ ∞ f U) (n : ℕ) (v : Fin n → P) {p : P} (hp : p ∈ U) :
    jet f (List.ofFn v).reverse p = iteratedFDeriv ℝ n f p v := by
  induction n generalizing f with
  | zero => simp [jet]
  | succ n ih =>
    rw [List.ofFn_succ', List.concat_eq_append, List.reverse_concat, jet_cons]
    rw [ih (contDiffOn_directional hU hf (v (Fin.last n))) (fun i => v i.castSucc)]
    rw [iteratedFDeriv_succ_apply_right]
    have hdf := (contDiffOn_infty_iff_fderiv_of_isOpen hU).mp hf |>.2
    have hh := iteratedFDerivWithin_clm_apply_const_apply hU.uniqueDiffOn hdf
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl n) hp
      (u := v (Fin.last n)) (m := Fin.init v)
    simp only [iteratedFDerivWithin_of_isOpen n hU hp] at hh
    exact hh

/-- A bound for the ordinary multilinear derivative controls every word of
unit directions, including the empty word. -/
theorem norm_jet_le_iteratedFDeriv {U : Set P} (hU : IsOpen U) {f : P → E}
    (hf : ContDiffOn ℝ ∞ f U) (l : List P) {p : P} (hp : p ∈ U) (hl : UnitWord l) :
    ‖jet f l p‖ ≤ ‖iteratedFDeriv ℝ l.length f p‖ := by
  have hv : ‖l.reverse.get‖ ≤ 1 := by
    apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).mpr
    intro i
    exact hl _ (List.mem_reverse.mp (l.reverse.get_mem i))
  have hnorm := (iteratedFDeriv ℝ l.reverse.length f p).unit_le_opNorm hv
  rw [← jet_ofFn_reverse hU hf l.reverse.length l.reverse.get hp] at hnorm
  have hh : ‖jet f l p‖ ≤ ‖iteratedFDeriv ℝ l.reverse.length f p‖ := by
    simpa only [List.ofFn_get, List.reverse_reverse] using hnorm
  exact hh.trans_eq (congrArg (fun k : ℕ => ‖iteratedFDeriv ℝ k f p‖)
    (show l.reverse.length = l.length from List.length_reverse))

/-- Unit-direction bounds control the full multilinear norm, also at order zero. -/
theorem multilinear_norm_le_of_unit {n : ℕ} (T : P [×n]→L[ℝ] E)
    {B : ℝ} (hB : 0 ≤ B)
    (hT : ∀ v : Fin n → P, (∀ i, ‖v i‖ ≤ 1) → ‖T v‖ ≤ B) : ‖T‖ ≤ B := by
  apply T.opNorm_le_bound hB
  intro v
  let w : Fin n → P := fun i => ‖v i‖⁻¹ • v i
  have hw (i : Fin n) : ‖w i‖ ≤ 1 := by
    by_cases hz : v i = 0
    · simp [w, hz]
    · simp [w, norm_smul,
        inv_mul_cancel₀ (norm_ne_zero_iff.mpr hz)]
  have hv : (fun i => ‖v i‖ • w i) = v := by
    funext i
    by_cases hz : v i = 0
    · simp [w, hz]
    · simp [w, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hz)]
  have hp : 0 ≤ ∏ i, ‖v i‖ := Finset.prod_nonneg (fun i _ => norm_nonneg _)
  calc
    ‖T v‖ = ‖(∏ i, ‖v i‖) • T w‖ := by rw [← T.map_smul_univ, hv]
    _ = (∏ i, ‖v i‖) * ‖T w‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hp]
    _ ≤ (∏ i, ‖v i‖) * B := mul_le_mul_of_nonneg_left (hT w hw) hp
    _ = B * ∏ i, ‖v i‖ := mul_comm _ _

section Products

open ParametricODE

variable {a b : ℝ}

/-- The full Leibniz expansion, retaining ordered differentiation and therefore
automatically retaining every mixed-term multiplicity. -/
noncomputable def productJet (A : P → Coefficient a b E) (u : P → Curve a b E)
    (l : List P) : P → Curve a b E :=
  (List.rec
    (motive := fun _ : List P =>
      (P → Coefficient a b E) → (P → Curve a b E) → P → Curve a b E)
    (fun B z p => applyCoefficient (B p) (z p))
    (fun v _ rec B z p => rec (directional B v) z p + rec B (directional z v) p) l) A u

/-- The proper Leibniz terms: at least one derivative hits the coefficient,
so every solution derivative in this expression has strictly lower order. -/
noncomputable def crossJet (A : P → Coefficient a b E) (u : P → Curve a b E)
    (l : List P) : P → Curve a b E :=
  (List.rec
    (motive := fun _ : List P =>
      (P → Coefficient a b E) → (P → Curve a b E) → P → Curve a b E)
    (fun _ _ _ => 0)
    (fun v tail rec B z p => productJet (directional B v) z tail p +
      rec B (directional z v) p) l) A u

theorem productJet_split (A : P → Coefficient a b E) (u : P → Curve a b E)
    (l : List P) (p : P) :
    productJet A u l p = applyCoefficient (A p) (jet u l p) + crossJet A u l p := by
  induction l generalizing A u with
  | nil => simp [productJet, crossJet]
  | cons v l ih =>
    change productJet (directional A v) u l p + productJet A (directional u v) l p =
      applyCoefficient (A p) (jet (directional u v) l p) +
        (productJet (directional A v) u l p + crossJet A (directional u v) l p)
    rw [ih A (directional u v)]
    abel

theorem directional_product {U : Set P} (hU : IsOpen U)
    {A : P → Coefficient a b E} {u : P → Curve a b E}
    (hA : ContDiffOn ℝ ∞ A U) (hu : ContDiffOn ℝ ∞ u U) (v : P) :
    EqOn (directional (fun p => applyCoefficient (A p) (u p)) v)
      (fun p => applyCoefficient (directional A v p) (u p) +
        applyCoefficient (A p) (directional u v p)) U := by
  intro p hp
  have hdA := ((hA p hp).contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)
  have hdu := ((hu p hp).contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)
  have hmap : HasFDerivAt (coefficientAction (E := E) (a := a) (b := b))
      (coefficientAction (E := E)) (A p) :=
    ContinuousLinearMap.hasFDerivAt (𝕜 := ℝ)
      (E := Coefficient a b E) (F := Curve a b E →L[ℝ] Curve a b E)
      (coefficientAction (E := E))
  have hlin : HasFDerivAt
      (fun q => coefficientAction (E := E) (A q))
      ((coefficientAction (E := E)).comp (fderiv ℝ A p)) p :=
    HasFDerivAt.comp (𝕜 := ℝ) (E := P) (F := Coefficient a b E)
      (G := Curve a b E →L[ℝ] Curve a b E) p hmap hdA.hasFDerivAt
  have h := congrArg (fun M : P →L[ℝ] Curve a b E => M v)
    (hlin.clm_apply hdu.hasFDerivAt).fderiv
  simp only [_root_.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, add_comm] at h
  convert! h using 1; apply add_comm

theorem jet_product {U : Set P} (hU : IsOpen U)
    {A : P → Coefficient a b E} {u : P → Curve a b E}
    (hA : ContDiffOn ℝ ∞ A U) (hu : ContDiffOn ℝ ∞ u U) (l : List P) :
    EqOn (jet (fun p => applyCoefficient (A p) (u p)) l) (productJet A u l) U := by
  induction l generalizing A u with
  | nil => intro p hp; rfl
  | cons v l ih =>
    have hdA := contDiffOn_directional hU hA v
    have hdu := contDiffOn_directional hU hu v
    have hcoeff : ContDiff ℝ ∞ (coefficientAction (E := E) (a := a) (b := b)) :=
      ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := ∞)
        (E := Coefficient a b E) (F := Curve a b E →L[ℝ] Curve a b E)
        (coefficientAction (E := E))
    have hleft : ContDiffOn ℝ ∞ (fun p => applyCoefficient (directional A v p) (u p)) U :=
      (hcoeff.comp_contDiffOn hdA).clm_apply hu
    have hright : ContDiffOn ℝ ∞ (fun p => applyCoefficient (A p) (directional u v p)) U :=
      (hcoeff.comp_contDiffOn hA).clm_apply hdu
    intro p hp
    calc
      jet (fun p => applyCoefficient (A p) (u p)) (v :: l) p =
          jet (fun p => applyCoefficient (directional A v p) (u p) +
            applyCoefficient (A p) (directional u v p)) l p :=
        jet_congr hU (directional_product hU hA hu v) l hp
      _ = jet (fun p => applyCoefficient (directional A v p) (u p)) l p +
          jet (fun p => applyCoefficient (A p) (directional u v p)) l p :=
        jet_add hU hleft hright l hp
      _ = productJet A u (v :: l) p := by
        rw [ih hdA hu hp, ih hA hdu hp]
        rfl

/-- Every term in the full Leibniz expansion has the product estimate. There
are `2^length` ordered choices of which factor receives each derivative. -/
theorem norm_productJet_le
    (A : P → Coefficient a b E) (u : P → Curve a b E) (l : List P)
    (p : P) (t : Icc a b) {M B : ℝ} (hM : 0 ≤ M) (_hB : 0 ≤ B)
    (hA : ∀ k : List P, k.length ≤ l.length → UnitWord k → ‖jet A k p t‖ ≤ M)
    (hu : ∀ k : List P, k.length ≤ l.length → UnitWord k → ‖jet u k p t‖ ≤ B)
    (hl : UnitWord l) :
    ‖productJet A u l p t‖ ≤ (2 : ℝ) ^ l.length * M * B := by
  induction l generalizing A u with
  | nil =>
    change ‖A p t (u p t)‖ ≤ 2 ^ 0 * M * B
    simpa only [pow_zero, one_mul] using
      ((A p t).le_opNorm (u p t)).trans
        (mul_le_mul (hA [] le_rfl unitWord_nil) (hu [] le_rfl unitWord_nil)
          (norm_nonneg _) hM)
  | cons v l ih =>
    obtain ⟨hv, hl⟩ := unitWord_cons v l |>.mp hl
    have hDA (k : List P) (hk : k.length ≤ l.length) (hku : UnitWord k) :
        ‖jet (directional A v) k p t‖ ≤ M :=
      hA (v :: k) (by simpa using hk) ((unitWord_cons v k).mpr ⟨hv, hku⟩)
    have hDu (k : List P) (hk : k.length ≤ l.length) (hku : UnitWord k) :
        ‖jet (directional u v) k p t‖ ≤ B :=
      hu (v :: k) (by simpa using hk) ((unitWord_cons v k).mpr ⟨hv, hku⟩)
    have hA0 (k : List P) (hk : k.length ≤ l.length) (hku : UnitWord k) :
        ‖jet A k p t‖ ≤ M := hA k (by simp only [List.length_cons]; omega) hku
    have hu0 (k : List P) (hk : k.length ≤ l.length) (hku : UnitWord k) :
        ‖jet u k p t‖ ≤ B := hu k (by simp only [List.length_cons]; omega) hku
    change ‖productJet (directional A v) u l p t + productJet A (directional u v) l p t‖ ≤ _
    calc
      _ ≤ ‖productJet (directional A v) u l p t‖ +
          ‖productJet A (directional u v) l p t‖ := norm_add_le _ _
      _ ≤ 2 ^ l.length * M * B + 2 ^ l.length * M * B :=
        add_le_add (ih _ _ hDA hu0 hl) (ih _ _ hA0 hDu hl)
      _ = _ := by simp only [List.length_cons, pow_succ]; ring

/-- The proper Leibniz expansion only requires solution jets of strictly lower
order. This is the triangular property used by the weighted induction. -/
theorem norm_crossJet_le
    (A : P → Coefficient a b E) (u : P → Curve a b E) (l : List P)
    (p : P) (t : Icc a b) {M B : ℝ} (hM : 0 ≤ M) (hB : 0 ≤ B)
    (hA : ∀ k : List P, k.length ≤ l.length → UnitWord k → ‖jet A k p t‖ ≤ M)
    (hu : ∀ k : List P, k.length < l.length → UnitWord k → ‖jet u k p t‖ ≤ B)
    (hl : UnitWord l) :
    ‖crossJet A u l p t‖ ≤ (2 : ℝ) ^ l.length * M * B := by
  induction l generalizing A u with
  | nil => simpa [crossJet] using mul_nonneg hM hB
  | cons v l ih =>
    obtain ⟨hv, hl⟩ := unitWord_cons v l |>.mp hl
    have hDA (k : List P) (hk : k.length ≤ l.length) (hku : UnitWord k) :
        ‖jet (directional A v) k p t‖ ≤ M :=
      hA (v :: k) (by simpa using hk) ((unitWord_cons v k).mpr ⟨hv, hku⟩)
    have hDu (k : List P) (hk : k.length < l.length) (hku : UnitWord k) :
        ‖jet (directional u v) k p t‖ ≤ B :=
      hu (v :: k) (by simpa using hk) ((unitWord_cons v k).mpr ⟨hv, hku⟩)
    have hA0 (k : List P) (hk : k.length ≤ l.length) (hku : UnitWord k) :
        ‖jet A k p t‖ ≤ M := hA k (by simp only [List.length_cons]; omega) hku
    have hu0 (k : List P) (hk : k.length ≤ l.length) (hku : UnitWord k) :
        ‖jet u k p t‖ ≤ B := hu k (by simp only [List.length_cons]; omega) hku
    change ‖productJet (directional A v) u l p t + crossJet A (directional u v) l p t‖ ≤ _
    calc
      _ ≤ ‖productJet (directional A v) u l p t‖ +
          ‖crossJet A (directional u v) l p t‖ := norm_add_le _ _
      _ ≤ 2 ^ l.length * M * B + 2 ^ l.length * M * B :=
        add_le_add (norm_productJet_le _ _ _ _ _ hM hB hDA hu0 hl) (ih _ _ hA0 hDu hl)
      _ = _ := by simp only [List.length_cons, pow_succ]; ring

/-- The actual inhomogeneity of the differentiated equation. -/
noncomputable def jetSource (A : P → Coefficient a b E) (f u : P → Curve a b E)
    (l : List P) (p : P) : Curve a b E := jet f l p + crossJet A u l p

variable [CompleteSpace E]

/-- Every actual parameter jet of the constructed solution is itself the
constructed solution of the corresponding triangular variational equation.
No existence or smoothness of solution jets is assumed. -/
theorem jet_solution_eq_solution (hab : a ≤ b) {U : Set P} (hU : IsOpen U)
    (A : P → Coefficient a b E) (x₀ : P → E) (f : P → Curve a b E)
    (hA : ContDiffOn ℝ ∞ A U) (hx₀ : ContDiffOn ℝ ∞ x₀ U)
    (hf : ContDiffOn ℝ ∞ f U) (l : List P) {p : P} (hp : p ∈ U) :
    jet (fun q => solution hab (A q) (x₀ q) (f q)) l p =
      solution hab (A p) (jet x₀ l p)
        (jetSource A f (fun q => solution hab (A q) (x₀ q) (f q)) l p) := by
  let u : P → Curve a b E := fun q => solution hab (A q) (x₀ q) (f q)
  have hu : ContDiffOn ℝ ∞ u U := contDiffOn_solution_family hab A x₀ f hA hx₀ hf
  have hcoeff : ContDiff ℝ ∞ (coefficientAction (E := E) (a := a) (b := b)) :=
    ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := ∞)
      (E := Coefficient a b E) (F := Curve a b E →L[ℝ] Curve a b E)
      (coefficientAction (E := E))
  have hAu : ContDiffOn ℝ ∞ (fun q => applyCoefficient (A q) (u q)) U :=
    (hcoeff.comp_contDiffOn hA).clm_apply hu
  have hright : EqOn u
      (fun q => constantCurve (x₀ q) + integrator hab (applyCoefficient (A q) (u q) + f q)) U :=
    fun q _ => solution_integralEquation hab (A q) (x₀ q) (f q)
  have hC : ContDiffOn ℝ ∞ (fun q => (constantCurve (a := a) (b := b)) (x₀ q)) U :=
    (constantCurve (E := E)).contDiff.comp_contDiffOn hx₀
  have hI : ContDiffOn ℝ ∞
      (fun q => integrator hab (applyCoefficient (A q) (u q) + f q)) U :=
    (integrator (E := E) hab).contDiff.comp_contDiffOn (hAu.add hf)
  have hj : jet u l p = constantCurve (jet x₀ l p) +
      integrator hab (applyCoefficient (A p) (jet u l p) + jetSource A f u l p) := by
    calc
      jet u l p = jet
          (fun q => constantCurve (x₀ q) + integrator hab (applyCoefficient (A q) (u q) + f q)) l p
              :=
        jet_congr hU hright l hp
      _ = jet (fun q => constantCurve (x₀ q)) l p +
          jet (fun q => integrator hab (applyCoefficient (A q) (u q) + f q)) l p :=
        jet_add hU hC hI l hp
      _ = constantCurve (jet x₀ l p) +
          integrator hab (jet (fun q => applyCoefficient (A q) (u q) + f q) l p) := by
        rw [jet_clm hU hx₀ (constantCurve (E := E)) l hp,
          jet_clm hU (hAu.add hf) (integrator (E := E) hab) l hp]
      _ = constantCurve (jet x₀ l p) +
          integrator hab (applyCoefficient (A p) (jet u l p) + jetSource A f u l p) := by
        rw [jet_add hU hAu hf l hp]
        dsimp only
        rw [jet_product hU hA hu l hp, productJet_split]
        congr 2
        unfold jetSource
        abel
  change jet u l p = (equationOperator hab (A p)).inverse
    (constantCurve (jet x₀ l p) + integrator hab (jetSource A f u l p))
  symm
  apply (equationOperator_isInvertible hab (A p)).inverse_apply_eq.mpr
  change constantCurve (jet x₀ l p) + integrator hab (jetSource A f u l p) =
    jet u l p - integrator hab (applyCoefficient (A p) (jet u l p))
  rw [(integrator hab).map_add] at hj
  exact (eq_sub_iff_add_eq.mpr (by simpa only [add_assoc, add_comm, add_left_comm] using hj.symm))

/-- The time derivative of each actual parameter jet is its triangular
variational equation on the original closed interval. -/
theorem jet_solution_hasDerivWithinAt (hab : a ≤ b) {U : Set P} (hU : IsOpen U)
    (A : P → Coefficient a b E) (x₀ : P → E) (f : P → Curve a b E)
    (hA : ContDiffOn ℝ ∞ A U) (hx₀ : ContDiffOn ℝ ∞ x₀ U)
    (hf : ContDiffOn ℝ ∞ f U) (l : List P) {p : P} (hp : p ∈ U) (t : Icc a b) :
    let u := fun q => solution hab (A q) (x₀ q) (f q)
    HasDerivWithinAt (extend hab (jet u l p))
      (A p t (jet u l p t) + jetSource A f u l p t) (Icc a b) t := by
  dsimp only
  rw [jet_solution_eq_solution hab hU A x₀ f hA hx₀ hf l hp]
  exact solution_hasDerivWithinAt hab _ _ _ t

end Products

section Weighted

open ParametricODE

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  {a b : ℝ}

/-- The constructed solution retains a positive reference envelope. A uniform
bound for the error exponential gives a factor linear in the slot length.
The estimate follows from the proved energy inequality for the actual ODE. -/
theorem norm_solution_le_envelope (hab : a ≤ b)
    (A : Coefficient a b H) (x₀ : H) (f : Curve a b H)
    (rate W : ℝ → ℝ) {μ C X F₀ : ℝ} (hμ : 0 ≤ μ)
    (hW : ∀ t, 0 < W t) (hdW : ∀ t, HasDerivAt W (rate t * W t) t)
    (henergy : ∀ t : Icc a b, ∀ x : H, ⟪x, A t x⟫_ℝ ≤ (rate t + μ) * ‖x‖ ^ 2)
    (hC : Real.exp (μ * (b - a)) ≤ C) (hX : 0 ≤ X) (hF : 0 ≤ F₀)
    (hx₀ : ‖x₀‖ ≤ X * W a) (hf : ∀ t : Icc a b, ‖f t‖ ≤ F₀ * W t)
    (t : Icc a b) :
    ‖solution hab A x₀ f t‖ ≤ C * (X + (b - a) * F₀) * W t := by
  let u : Curve a b H := solution hab A x₀ f
  have hode (s : ℝ) (hs : s ∈ Ico a b) :
      HasDerivWithinAt (extend hab u)
        (extend hab A s (extend hab u s) + extend hab f s) (Ici s) s := by
    have hscc := Ico_subset_Icc_self hs
    have hh := (solution_hasDerivWithinAt hab A x₀ f ⟨s, hscc⟩).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem hs)
    simpa only [u, ParametricODE.extend, projIcc_of_mem hab hscc] using hh
  have he (s : ℝ) (hs : s ∈ Ico a b) (x : H) :
      ⟪x, extend hab A s x⟫_ℝ ≤ (rate s + μ) * ‖x‖ ^ 2 := by
    simpa only [ParametricODE.extend, projIcc_of_mem hab (Ico_subset_Icc_self hs)]
      using henergy ⟨s, Ico_subset_Icc_self hs⟩ x
  have hbase := ViscousPropagator.norm_le_envelope_mul_integral_on (extend hab A)
    rate W hμ hW hdW (continuous_extend hab u).continuousOn
    (continuous_extend hab f).continuousOn hode he
  have hua : extend hab u a = x₀ := by
    simpa only [ParametricODE.extend, projIcc_of_mem hab (show a ∈ Icc a b from ⟨le_rfl, hab⟩)]
      using solution_initial hab A x₀ f
  have hstart : ‖extend hab u a‖ / W a ≤ X := by
    rw [hua]
    exact (div_le_iff₀ (hW a)).mpr hx₀
  have hcW : Continuous W := continuous_iff_continuousAt.mpr fun s => (hdW s).continuousAt
  have hcq : Continuous (fun s => ‖extend hab f s‖ / W s) :=
    (continuous_extend hab f).norm.div hcW (fun s => ne_of_gt (hW s))
  have hint : (∫ s in a..(t : ℝ), ‖extend hab f s‖ / W s) ≤ (b - a) * F₀ := by
    have hm := intervalIntegral.integral_mono_on (μ := volume) t.2.1
      (hcq.intervalIntegrable a t) (continuous_const.intervalIntegrable a t)
      (show ∀ s ∈ Icc a (t : ℝ), ‖extend hab f s‖ / W s ≤ F₀ from by
        intro s hs
        have hscc : s ∈ Icc a b := ⟨hs.1, hs.2.trans t.2.2⟩
        apply (div_le_iff₀ (hW s)).mpr
        simpa only [ParametricODE.extend, projIcc_of_mem hab hscc] using hf ⟨s, hscc⟩)
    calc
      _ ≤ ((t : ℝ) - a) * F₀ := by
        simpa only [intervalIntegral.integral_const, smul_eq_mul] using hm
      _ ≤ (b - a) * F₀ := mul_le_mul_of_nonneg_right (sub_le_sub_right t.2.2 a) hF
  have hExp : Real.exp (μ * ((t : ℝ) - a)) ≤ C :=
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (sub_le_sub_right t.2.2 a) hμ)).trans hC
  have hnonneg : 0 ≤ X + (b - a) * F₀ := add_nonneg hX (mul_nonneg (sub_nonneg.mpr hab) hF)
  calc
    ‖solution hab A x₀ f t‖ ≤ Real.exp (μ * ((t : ℝ) - a)) * W t *
        (‖extend hab u a‖ / W a + ∫ s in a..(t : ℝ), ‖extend hab f s‖ / W s) := by
      simpa only [extend_coe, u] using hbase t t.2
    _ ≤ Real.exp (μ * ((t : ℝ) - a)) * W t * (X + (b - a) * F₀) :=
      mul_le_mul_of_nonneg_left (add_le_add hstart hint)
        (mul_nonneg (Real.exp_pos _).le (hW t).le)
    _ ≤ C * W t * (X + (b - a) * F₀) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hExp (hW t).le) hnonneg
    _ = C * (X + (b - a) * F₀) * W t := by ring

/-- A finite-order weighted estimate for every actual mixed parameter jet.
Only input jets are bounded in the hypotheses. The factor multiplying each
successive derivative is polynomial in the slot length and coefficient bound. -/
theorem norm_jet_solution_le (hab : a ≤ b) {U : Set P} (hU : IsOpen U)
    (A : P → Coefficient a b H) (x₀ : P → H) (f : P → Curve a b H)
    (hA : ContDiffOn ℝ ∞ A U) (hx₀ : ContDiffOn ℝ ∞ x₀ U)
    (hf : ContDiffOn ℝ ∞ f U) {p : P} (hp : p ∈ U)
    (rate W : ℝ → ℝ) {μ C M X F₀ : ℝ} (hμ : 0 ≤ μ)
    (hW : ∀ t, 0 < W t) (hdW : ∀ t, HasDerivAt W (rate t * W t) t)
    (henergy : ∀ t : Icc a b, ∀ x : H, ⟪x, A p t x⟫_ℝ ≤ (rate t + μ) * ‖x‖ ^ 2)
    (hC : Real.exp (μ * (b - a)) ≤ C) (hM : 0 ≤ M) (hX : 0 ≤ X) (hF : 0 ≤ F₀)
    (N : ℕ)
    (hAj : ∀ l : List P, l.length ≤ N → UnitWord l → ∀ t : Icc a b, ‖jet A l p t‖ ≤ M)
    (hxj : ∀ l : List P, l.length ≤ N → UnitWord l → ‖jet x₀ l p‖ ≤ X * W a)
    (hfj : ∀ l : List P, l.length ≤ N → UnitWord l → ∀ t : Icc a b,
      ‖jet f l p t‖ ≤ F₀ * W t)
    (l : List P) (hlN : l.length ≤ N) (hl : UnitWord l) (t : Icc a b) :
    ‖jet (fun q => solution hab (A q) (x₀ q) (f q)) l p t‖ ≤
      C * (X + (b - a) * F₀) * (1 + C * (b - a) * ((2 : ℝ) ^ N * M)) ^ l.length * W t := by
  let u : P → Curve a b H := fun q => solution hab (A q) (x₀ q) (f q)
  let L := b - a
  let B₀ := C * (X + L * F₀)
  let K := (2 : ℝ) ^ N * M
  let Q := 1 + C * L * K
  have hL : 0 ≤ L := sub_nonneg.mpr hab
  have hC0 : 0 ≤ C := (Real.exp_pos _).le.trans hC
  have hB : 0 ≤ B₀ := mul_nonneg hC0 (add_nonneg hX (mul_nonneg hL hF))
  have hK : 0 ≤ K := mul_nonneg (pow_nonneg (by norm_num) _) hM
  have hQ : 1 ≤ Q := le_add_of_nonneg_right (mul_nonneg (mul_nonneg hC0 hL) hK)
  have hQ0 : 0 ≤ Q := zero_le_one.trans hQ
  have hbound : ∀ n : ℕ, n ≤ N → ∀ k : List P, k.length = n → UnitWord k →
      ∀ s : Icc a b, ‖jet u k p s‖ ≤ B₀ * Q ^ n * W s := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro hn k hk hku s
      cases n with
      | zero =>
        have hk0 : k = [] := List.length_eq_zero_iff.mp hk
        subst k
        have hh := norm_solution_le_envelope hab (A p) (x₀ p) (f p) rate W hμ hW hdW
          henergy hC hX hF (hxj [] (by simp) unitWord_nil)
          (hfj [] (by simp) unitWord_nil) s
        simpa only [jet_nil, pow_zero, mul_one, B₀, L, u] using hh
      | succ n =>
        have hlower (r : List P) (hr : r.length < k.length) (hru : UnitWord r)
            (z : Icc a b) : ‖jet u r p z‖ ≤ B₀ * Q ^ n * W z := by
          have hrn : r.length ≤ n := by omega
          have hhi := ih r.length (by omega) (hrn.trans (Nat.le_of_succ_le hn)) r rfl hru z
          exact hhi.trans (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hQ hrn) hB) (hW z).le)
        have hforce (z : Icc a b) :
            ‖jetSource A f u k p z‖ ≤ (F₀ + K * B₀ * Q ^ n) * W z := by
          have hjA (r : List P) (hr : r.length ≤ k.length) (hru : UnitWord r) :
              ‖jet A r p z‖ ≤ M := hAj r (by omega) hru z
          have hcross := norm_crossJet_le A u k p z hM
            (mul_nonneg (mul_nonneg hB (pow_nonneg hQ0 _)) (hW z).le)
            hjA (fun r hr hru => hlower r hr hru z) hku
          have hpow : (2 : ℝ) ^ k.length ≤ (2 : ℝ) ^ N :=
            pow_le_pow_right₀ (by norm_num) (by omega)
          calc
            ‖jetSource A f u k p z‖ ≤ ‖jet f k p z‖ + ‖crossJet A u k p z‖ := norm_add_le _ _
            _ ≤ F₀ * W z + (2 : ℝ) ^ k.length * M * (B₀ * Q ^ n * W z) :=
              add_le_add (hfj k (by omega) hku z) hcross
            _ ≤ F₀ * W z + (2 : ℝ) ^ N * M * (B₀ * Q ^ n * W z) := by
              exact add_le_add_right (mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_right hpow hM)
                (mul_nonneg (mul_nonneg hB (pow_nonneg hQ0 _)) (hW z).le)) _
            _ = (F₀ + K * B₀ * Q ^ n) * W z := by dsimp [K]; ring
        have hforce0 : 0 ≤ F₀ + K * B₀ * Q ^ n := by positivity
        have hh := norm_solution_le_envelope hab (A p) (jet x₀ k p) (jetSource A f u k p)
          rate W hμ hW hdW henergy hC hX hforce0 (hxj k (by omega) hku) hforce s
        have hBpow : B₀ ≤ B₀ * Q ^ n := by
          simpa only [mul_one] using mul_le_mul_of_nonneg_left (one_le_pow₀ hQ) hB
        have hamp : C * (X + L * (F₀ + K * B₀ * Q ^ n)) ≤ B₀ * Q ^ (n + 1) := by
          calc
            _ = B₀ + (C * L * K) * (B₀ * Q ^ n) := by dsimp [B₀]; ring
            _ ≤ B₀ * Q ^ n + (C * L * K) * (B₀ * Q ^ n) := add_le_add_left hBpow _
            _ = B₀ * Q ^ (n + 1) := by rw [pow_succ]; dsimp [Q]; ring
        calc
          ‖jet u k p s‖ = ‖solution hab (A p) (jet x₀ k p) (jetSource A f u k p) s‖ := by
            rw [jet_solution_eq_solution hab hU A x₀ f hA hx₀ hf k hp]
          _ ≤ C * (X + L * (F₀ + K * B₀ * Q ^ n)) * W s := hh
          _ ≤ B₀ * Q ^ (n + 1) * W s := mul_le_mul_of_nonneg_right hamp (hW s).le
  exact hbound l.length hlN l rfl hl t

/-- Explicit polynomial bookkeeping. The nonnegative factor `w` appears only
once and is therefore preserved by every fixed differentiation order. -/
theorem amplitude_le_polynomial {S K w L : ℝ} (hS : 1 ≤ S) (hK : 1 ≤ K)
    (hw : 0 ≤ w) (hL : 0 ≤ L) (hLS : L ≤ K * S) (m N n : ℕ) :
    K * (w * K * S ^ m + L * (w * K * S ^ m)) *
        (1 + K * L * ((2 : ℝ) ^ N * (K * S ^ m))) ^ n ≤
      w * ((2 : ℝ) ^ (N + 1) * K ^ 3) ^ (n + 1) * S ^ ((m + 1) * (n + 1)) := by
  let T := S ^ (m + 1)
  let D := (2 : ℝ) ^ (N + 1) * K ^ 3
  let B := K * (w * K * S ^ m + L * (w * K * S ^ m))
  let Q := 1 + K * L * ((2 : ℝ) ^ N * (K * S ^ m))
  have hS0 : 0 ≤ S := zero_le_one.trans hS
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  have hT : 1 ≤ T := one_le_pow₀ hS
  have hT0 : 0 ≤ T := zero_le_one.trans hT
  have hD0 : 0 ≤ D := by dsimp [D]; positivity
  have hB0 : 0 ≤ B := by dsimp [B]; positivity
  have hQ0 : 0 ≤ Q := by dsimp [Q]; positivity
  have hKS : 1 ≤ K * S := one_le_mul_of_one_le_of_one_le hK hS
  have htwopow : (2 : ℝ) ≤ (2 : ℝ) ^ (N + 1) := by
    simpa only [pow_one] using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
      (show 1 ≤ N + 1 by omega)
  have hbase : B ≤ w * D * T := by
    calc
      B = (w * K ^ 2 * S ^ m) * (1 + L) := by dsimp [B]; ring
      _ ≤ (w * K ^ 2 * S ^ m) * (2 * K * S) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = w * (2 * K ^ 3) * T := by dsimp [T]; rw [pow_succ]; ring
      _ ≤ w * D * T := by dsimp [D]; gcongr
  have hprod : 1 ≤ (2 : ℝ) ^ N * K ^ 3 * T :=
    one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))
        (one_le_pow₀ hK)) hT
  have hstep : Q ≤ D * T := by
    calc
      Q ≤ 1 + K * (K * S) * ((2 : ℝ) ^ N * (K * S ^ m)) := by dsimp [Q]; gcongr
      _ = 1 + (2 : ℝ) ^ N * K ^ 3 * T := by dsimp [T]; rw [pow_succ]; ring
      _ ≤ 2 * ((2 : ℝ) ^ N * K ^ 3 * T) := by linarith
      _ = D * T := by dsimp [D]; rw [pow_succ]; ring
  calc
    B * Q ^ n ≤ (w * D * T) * (D * T) ^ n :=
      mul_le_mul hbase (pow_le_pow_left₀ hQ0 hstep n) (pow_nonneg hQ0 _) (by positivity)
    _ = w * D ^ (n + 1) * T ^ (n + 1) := by
      rw [mul_pow]
      simp only [pow_succ]
      ring
    _ = w * D ^ (n + 1) * S ^ ((m + 1) * (n + 1)) := by dsimp [T]; rw [pow_mul]

/-- An error of order `1/S` on a slot of length at most `d*S` has a uniform
exponential factor, independent of `S`. -/
theorem exp_error_le_of_inv_scale {μ S L c d : ℝ} (hS : 0 < S)
    (hc : 0 ≤ c) (hμ : μ ≤ c / S) (hL : 0 ≤ L) (hslot : L ≤ d * S) :
    Real.exp (μ * L) ≤ Real.exp (c * d) := by
  apply Real.exp_le_exp.mpr
  calc
    μ * L ≤ (c / S) * L := mul_le_mul_of_nonneg_right hμ hL
    _ ≤ (c / S) * (d * S) := mul_le_mul_of_nonneg_left hslot (div_nonneg hc hS.le)
    _ = c * d := by field_simp

/-- A concrete slot-polynomial estimate. `w` may be a small-scale power times
a slow-variable weight; no loss of its power occurs in the induction. -/
theorem norm_jet_solution_le_polynomial (hab : a ≤ b) {U : Set P} (hU : IsOpen U)
    (A : P → Coefficient a b H) (x₀ : P → H) (f : P → Curve a b H)
    (hA : ContDiffOn ℝ ∞ A U) (hx₀ : ContDiffOn ℝ ∞ x₀ U)
    (hf : ContDiffOn ℝ ∞ f U) {p : P} (hp : p ∈ U)
    (rate W : ℝ → ℝ) {μ S K w : ℝ} (hμ : 0 ≤ μ)
    (hW : ∀ t, 0 < W t) (hdW : ∀ t, HasDerivAt W (rate t * W t) t)
    (henergy : ∀ t : Icc a b, ∀ x : H, ⟪x, A p t x⟫_ℝ ≤ (rate t + μ) * ‖x‖ ^ 2)
    (hC : Real.exp (μ * (b - a)) ≤ K) (hS : 1 ≤ S) (hK : 1 ≤ K) (hw : 0 ≤ w)
    (hslot : b - a ≤ K * S) (m N : ℕ)
    (hAj : ∀ l : List P, l.length ≤ N → UnitWord l → ∀ t : Icc a b,
      ‖jet A l p t‖ ≤ K * S ^ m)
    (hxj : ∀ l : List P, l.length ≤ N → UnitWord l → ‖jet x₀ l p‖ ≤ w * K * S ^ m * W a)
    (hfj : ∀ l : List P, l.length ≤ N → UnitWord l → ∀ t : Icc a b,
      ‖jet f l p t‖ ≤ w * K * S ^ m * W t)
    (l : List P) (hlN : l.length ≤ N) (hl : UnitWord l) (t : Icc a b) :
    ‖jet (fun q => solution hab (A q) (x₀ q) (f q)) l p t‖ ≤
      w * ((2 : ℝ) ^ (N + 1) * K ^ 3) ^ (l.length + 1) *
        S ^ ((m + 1) * (l.length + 1)) * W t := by
  have hS0 : 0 ≤ S := zero_le_one.trans hS
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  have hM : 0 ≤ K * S ^ m := by positivity
  have hF : 0 ≤ w * K * S ^ m := by positivity
  exact (norm_jet_solution_le hab hU A x₀ f hA hx₀ hf hp rate W hμ hW hdW henergy
    hC hM hF hF N hAj hxj hfj l hlN hl t).trans
      (mul_le_mul_of_nonneg_right
        (amplitude_le_polynomial hS hK hw (sub_nonneg.mpr hab) hslot m N l.length) (hW t).le)

end Weighted

section Joint

open ParametricODE SmoothPathFamily

universe u

variable {Q G : Type u} [NormedAddCommGroup Q] [NormedSpace ℝ Q]
  [NormedAddCommGroup G] [NormedSpace ℝ G] {a b : ℝ}

/-- Actual directional path jets evaluate to the corresponding jets of the
jointly supplied coefficient or source at each time. -/
theorem jet_pathFamily_apply (U : Set Q) (V : Set ℝ)
    (hU : IsOpen U) (hV : IsOpen V) (hI : Icc a b ⊆ V)
    (F : Q × ℝ → G) (hF : ContDiffOn ℝ ∞ F (U ×ˢ V))
    {p : Q} (hp : p ∈ U) (l : List Q) (t : Icc a b) :
    jet (pathFamily (a := a) (b := b) F) l p t = jet (fun q => F (q, t)) l p := by
  have hpath := contDiffOn_pathFamily_of_joint U V hU hV hI F hF
  have heq : EqOn (fun q => pathFamily (a := a) (b := b) F q t) (fun q => F (q, t)) U := by
    intro q hq
    exact pathFamily_apply F q
      (slice_continuous (hF.continuousOn.mono (Set.prod_mono Subset.rfl hI)) hq) t
  exact (jet_clm hU hpath (ContinuousMap.evalCLM ℝ t) l hp).symm.trans (jet_congr hU heq l hp)

theorem norm_jet_pathFamily_le (U : Set Q) (V : Set ℝ)
    (hU : IsOpen U) (hV : IsOpen V) (hI : Icc a b ⊆ V)
    (F : Q × ℝ → G) (hF : ContDiffOn ℝ ∞ F (U ×ˢ V))
    {p : Q} (hp : p ∈ U) (l : List Q) (hl : UnitWord l) (t : Icc a b) :
    ‖jet (pathFamily (a := a) (b := b) F) l p t‖ ≤
      ‖iteratedFDeriv ℝ l.length (fun q => F (q, t)) p‖ := by
  rw [jet_pathFamily_apply U V hU hV hI F hF hp l t]
  apply norm_jet_le_iteratedFDeriv hU _ l hp hl
  exact hF.comp (contDiffOn_id.prodMk contDiffOn_const) (fun q hq => ⟨hq, hI t.2⟩)

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Jointly smooth physical inputs with polynomial bounds on their actual
Fréchet jets give polynomially bounded jets of the actual ODE solution. The
bound is for the full multilinear norm at each time, retaining the envelope. -/
theorem norm_iteratedFDeriv_odeFamily_le_polynomial (hab : a ≤ b)
    (U : Set Q) (V : Set ℝ) (hU : IsOpen U) (hV : IsOpen V) (hI : Icc a b ⊆ V)
    (A : Q × ℝ → H →L[ℝ] H) (x₀ : Q → H) (f : Q × ℝ → H)
    (hA : ContDiffOn ℝ ∞ A (U ×ˢ V)) (hx₀ : ContDiffOn ℝ ∞ x₀ U)
    (hf : ContDiffOn ℝ ∞ f (U ×ˢ V)) {p : Q} (hp : p ∈ U)
    (rate W : ℝ → ℝ) {μ S K w : ℝ} (hμ : 0 ≤ μ)
    (hW : ∀ t, 0 < W t) (hdW : ∀ t, HasDerivAt W (rate t * W t) t)
    (henergy : ∀ t : Icc a b, ∀ x : H, ⟪x, A (p, t) x⟫_ℝ ≤ (rate t + μ) * ‖x‖ ^ 2)
    (hC : Real.exp (μ * (b - a)) ≤ K) (hS : 1 ≤ S) (hK : 1 ≤ K) (hw : 0 ≤ w)
    (hslot : b - a ≤ K * S) (m N : ℕ)
    (hAj : ∀ j : ℕ, j ≤ N → ∀ t : Icc a b,
      ‖iteratedFDeriv ℝ j (fun q => A (q, t)) p‖ ≤ K * S ^ m)
    (hxj : ∀ j : ℕ, j ≤ N → ‖iteratedFDeriv ℝ j x₀ p‖ ≤ w * K * S ^ m * W a)
    (hfj : ∀ j : ℕ, j ≤ N → ∀ t : Icc a b,
      ‖iteratedFDeriv ℝ j (fun q => f (q, t)) p‖ ≤ w * K * S ^ m * W t)
    (n : ℕ) (hn : n ≤ N) (t : Icc a b) :
    ‖iteratedFDeriv ℝ n (fun q => odeFamily hab A x₀ f q t) p‖ ≤
      w * ((2 : ℝ) ^ (N + 1) * K ^ 3) ^ (n + 1) * S ^ ((m + 1) * (n + 1)) * W t := by
  let u : Q → Curve a b H := odeFamily hab A x₀ f
  have hAc := contDiffOn_pathFamily_of_joint U V hU hV hI A hA
  have hfc := contDiffOn_pathFamily_of_joint U V hU hV hI f hf
  have hu : ContDiffOn ℝ ∞ u U := contDiffOn_odeFamily_of_joint hab U V hU hV hI A x₀ f hA hx₀ hf
  have hslice : ContDiffOn ℝ ∞ (fun q => u q t) U :=
    (ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := ∞) (E := Curve a b H) (F := H)
      (ContinuousMap.evalCLM ℝ t)).comp_contDiffOn hu
  have he : ∀ z : Icc a b, ∀ x : H,
      ⟪x, pathFamily (a := a) (b := b) A p z x⟫_ℝ ≤ (rate z + μ) * ‖x‖ ^ 2 := by
    intro z x
    rw [pathFamily_apply A p
      (slice_continuous (hA.continuousOn.mono (Set.prod_mono Subset.rfl hI)) hp)]
    exact henergy z x
  have hAw (l : List Q) (hlN : l.length ≤ N) (hl : UnitWord l) (z : Icc a b) :
      ‖jet (pathFamily A) l p z‖ ≤ K * S ^ m :=
    (norm_jet_pathFamily_le U V hU hV hI A hA hp l hl z).trans (hAj l.length hlN z)
  have hxw (l : List Q) (hlN : l.length ≤ N) (hl : UnitWord l) :
      ‖jet x₀ l p‖ ≤ w * K * S ^ m * W a :=
    (norm_jet_le_iteratedFDeriv hU hx₀ l hp hl).trans (hxj l.length hlN)
  have hfw (l : List Q) (hlN : l.length ≤ N) (hl : UnitWord l) (z : Icc a b) :
      ‖jet (pathFamily f) l p z‖ ≤ w * K * S ^ m * W z :=
    (norm_jet_pathFamily_le U V hU hV hI f hf hp l hl z).trans (hfj l.length hlN z)
  have hS0 : 0 ≤ S := zero_le_one.trans hS
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  have hWt : 0 ≤ W t := (hW t).le
  apply multilinear_norm_le_of_unit _ (by positivity)
  intro v hv
  let l := (List.ofFn v).reverse
  have hl : UnitWord l := by
    intro z hz
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp (List.mem_reverse.mp hz)
    exact hv i
  have hlen : l.length = n := by simp only [l, List.length_reverse, List.length_ofFn]
  have hbound := norm_jet_solution_le_polynomial hab hU (pathFamily A) x₀ (pathFamily f)
    hAc hx₀ hfc hp rate W hμ hW hdW he hC hS hK hw hslot m N hAw hxw hfw l
    (hlen.trans_le hn) hl t
  have heval : jet (fun q => u q t) l p = jet u l p t :=
    jet_clm hU hu (ContinuousMap.evalCLM ℝ t) l hp
  have hderiv : jet (fun q => u q t) l p = iteratedFDeriv ℝ n (fun q => u q t) p v :=
    jet_ofFn_reverse hU hslice n v hp
  rw [← hderiv, heval]
  simp only [hlen] at hbound
  exact hbound

end Joint

end

end NavierStokes.WeightedODEJets
