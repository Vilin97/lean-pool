/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.DefectIncrementBounds
public import LeanPool.NavierStokesAndEuler.NavierStokes.VariableGaugeMean

@[expose] public section

/-!
# Rank correction on the actual open slow domain

The stream uses the variable similarity gauge.  Its zero weighted mass makes
it equal to the same zero-axis primitive in every containing gauge.  All
moment estimates below use the local physical domain, not global slow data.
-/

noncomputable section

namespace NavierStokes.LocalRankDefect

open Set Function Filter MeasureTheory
open scoped ContDiff Topology Interval
open WeightedClasses MeanIncrementBounds

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

abbrev Point (P : Type) := PressureStream.Lift P
abbrev ScalarField (D : Type) := MeanIncrementBounds.Field D

noncomputable def positiveDomain (U : Set P) : Set (Point P) :=
  DefectIncrementBounds.positiveDomain ∩ PhysicalMeanDomain.slowDomain U

omit [NormedSpace ℝ P] in
theorem positiveDomain_open {U : Set P} (hU : IsOpen U) : IsOpen (positiveDomain U) :=
  DefectIncrementBounds.positiveDomain_open.inter (PhysicalMeanDomain.slowDomain_open hU)

/-- Smoothness and radial support only where the slow parameter is used. -/
structure LocalShell (a b : ℝ) (U : Set P) (f : ScalarField (Point P)) : Prop where
  smooth : SmoothOn (PhysicalMeanDomain.slowDomain U) f
  supported : ∀ n, PhysicalMeanDomain.SupportedOn a b U (f n)

namespace LocalShell

variable {a b : ℝ} {U : Set P} {f g : ScalarField (Point P)}

theorem zero_of_not_mem (hf : LocalShell a b U f) (n : ℕ) (x : Point P)
    (hx : x.2.1 ∈ U) (hr : x.1 ∉ Icc a b) : f n x = 0 := by
  by_contra hn
  exact hr (hf.supported n x hx hn)

theorem zero : LocalShell a b U (0 : ScalarField (Point P)) :=
  ⟨fun _ => contDiffOn_const, fun _ _ _ hn => (hn rfl).elim⟩

theorem add (hf : LocalShell a b U f) (hg : LocalShell a b U g) :
    LocalShell a b U (f + g) := by
  refine ⟨hf.smooth.add hg.smooth, ?_⟩
  intro n x hx hn
  by_contra hr
  exact hn (by simp [hf.zero_of_not_mem n x hx hr, hg.zero_of_not_mem n x hx hr])

theorem neg (hf : LocalShell a b U f) : LocalShell a b U (-f) :=
  ⟨hf.smooth.neg, fun n x hx hn => hf.supported n x hx (neg_ne_zero.mp hn)⟩

theorem sub (hf : LocalShell a b U f) (hg : LocalShell a b U g) :
    LocalShell a b U (f - g) := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

theorem mul (hf : LocalShell a b U f) (hg : LocalShell a b U g) :
    LocalShell a b U (f * g) :=
  ⟨hf.smooth.mul hg.smooth, fun n x hx hn => hf.supported n x hx (left_ne_zero_of_mul hn)⟩

theorem band_mul (hf : LocalShell a b U f) (c : ℕ → ℝ) :
    LocalShell a b U (fun n x => c n * f n x) :=
  ⟨fun n => contDiffOn_const.mul (hf.smooth n),
    fun n x hx hn => hf.supported n x hx (right_ne_zero_of_mul hn)⟩

theorem smul (hf : LocalShell a b U f) (c : ℝ) : LocalShell a b U (c • f) :=
  hf.band_mul (fun _ => c)

theorem directional (hf : LocalShell a b U f) (hU : IsOpen U) (v : Point P) :
    LocalShell a b U (fun n x => fderiv ℝ (f n) x v) := by
  refine ⟨hf.smooth.directional (PhysicalMeanDomain.slowDomain_open hU) v, ?_⟩
  intro n x hx hn
  by_contra hr
  have he : f n =ᶠ[𝓝 x] fun _ => 0 := by
    filter_upwards [(PhysicalMeanDomain.slowDomain_open hU).mem_nhds hx,
      (isClosed_Icc.preimage continuous_fst).isOpen_compl.mem_nhds hr] with y hy hyr
    exact hf.zero_of_not_mem n y hy hyr
  exact hn (by change fderiv ℝ (f n) x v = 0; rw [he.fderiv_eq]; simp)

theorem coefficient_mul (hf : LocalShell a b U f) (ha : 0 < a) (hU : IsOpen U)
    (hg : SmoothOn (positiveDomain U) g) : LocalShell a b U (g * f) := by
  refine ⟨?_, fun n x hx hn => hf.supported n x hx (right_ne_zero_of_mul hn)⟩
  intro n x hx
  apply ContDiffAt.contDiffWithinAt
  by_cases hr : x.1 < a
  · apply (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : Point P => (0 : ℝ)) x).congr_of_eventuallyEq
    filter_upwards [(PhysicalMeanDomain.slowDomain_open hU).mem_nhds hx,
      (isOpen_lt continuous_fst continuous_const).mem_nhds hr] with y hy hyr
    simp only [Pi.mul_apply, hf.zero_of_not_mem n y hy (fun hm => (not_le_of_gt hyr) hm.1),
      mul_zero]
  · have hp : x ∈ positiveDomain U := ⟨ha.trans_le (le_of_not_gt hr), hx⟩
    exact ((hg n).contDiffAt ((positiveDomain_open hU).mem_nhds hp)).mul
      ((hf.smooth n).contDiffAt ((PhysicalMeanDomain.slowDomain_open hU).mem_nhds hx))

theorem mul_coefficient (hf : LocalShell a b U f) (ha : 0 < a) (hU : IsOpen U)
    (hg : SmoothOn (positiveDomain U) g) : LocalShell a b U (f * g) := by
  simpa only [mul_comm] using hf.coefficient_mul ha hU hg

theorem freeze (hf : LocalShell a b U f) (hU : IsOpen U) {x : P} (hx : x ∈ U) :
    DefectIncrementBounds.Shell a b (fun n => PhysicalMeanDomain.freezeSlow x (f n)) := by
  refine ⟨fun n => VariableGaugeMean.freezeSlow_contDiff hU hx (hf.smooth n), ?_⟩
  intro n z hz
  exact hf.supported n (z.1, (x, z.2.2)) hx hz

end LocalShell

structure LocalTriple (a b : ℝ) (U : Set P) (m : Triple (Point P)) : Prop where
  radial : LocalShell a b U m.radial
  angular : LocalShell a b U m.angular
  axial : LocalShell a b U m.axial

theorem LocalTriple.updated {a b : ℝ} {U : Set P} {m h : Triple (Point P)}
    (hm : LocalTriple a b U m) (hh : LocalTriple a b U h) :
    LocalTriple a b U (updated m h) :=
  ⟨hm.radial.add hh.radial, hm.angular.add hh.angular, hm.axial.add hh.axial⟩

theorem LocalTriple.smooth {a b : ℝ} {U : Set P} {m : Triple (Point P)}
    (hm : LocalTriple a b U m) : SmoothTriple (PhysicalMeanDomain.slowDomain U) m :=
  ⟨hm.radial.smooth, hm.angular.smooth, hm.axial.smooth⟩

structure LocalOperators (U : Set P) (o : Operators (Point P)) : Prop where
  radius_eq : o.radius = Prod.fst
  radialProfile : ContDiffOn ℝ ∞ o.radialProfile (positiveDomain U)

theorem LocalOperators.invRadius_smooth {U : Set P} {o : Operators (Point P)}
    (ho : LocalOperators U o) : SmoothOn (positiveDomain U) o.invRadius := by
  intro n
  change ContDiffOn ℝ ∞ (fun x => (o.radius x)⁻¹) (positiveDomain U)
  rw [ho.radius_eq]
  exact contDiffOn_fst.inv (fun _ hx => (ne_of_gt hx.1))

namespace LocalShell

variable {a b : ℝ} {U : Set P} {f : ScalarField (Point P)} {o : Operators (Point P)}

theorem dr (hf : LocalShell a b U f) (ha : 0 < a) (hU : IsOpen U) (ho : LocalOperators U o) :
    LocalShell a b U (o.dr f) := by
  exact (hf.directional hU o.eR).add
    (((hf.directional hU o.vR).coefficient_mul ha hU (fun _ => ho.radialProfile)).band_mul
      o.radialFrequency)

theorem dz (hf : LocalShell a b U f) (hU : IsOpen U) (o : Operators (Point P)) :
    LocalShell a b U (o.dz f) := (hf.directional hU o.eZ).band_mul o.epsilon

theorem time (hf : LocalShell a b U f) (hU : IsOpen U) (o : Operators (Point P)) :
    LocalShell a b U (o.time f) :=
  ((hf.directional hU o.eT).band_mul o.epsilon).neg.add
    ((hf.directional hU o.vT).band_mul o.fastCoefficient)

theorem inv_mul (hf : LocalShell a b U f) (ha : 0 < a) (hU : IsOpen U)
    (ho : LocalOperators U o) : LocalShell a b U (o.invRadius * f) :=
  hf.coefficient_mul ha hU ho.invRadius_smooth

theorem radialDiv (hf : LocalShell a b U f) (ha : 0 < a) (hU : IsOpen U)
    (ho : LocalOperators U o) (c : ℝ) : LocalShell a b U (o.radialDiv c f) :=
  (hf.dr ha hU ho).add ((hf.inv_mul ha hU ho).smul c)

theorem viscosity (hf : LocalShell a b U f) (ha : 0 < a) (hU : IsOpen U)
    (ho : LocalOperators U o) (c : ℝ) : LocalShell a b U (o.viscosity c f) :=
  (((((hf.dr ha hU ho).dr ha hU ho).add ((hf.dr ha hU ho).inv_mul ha hU ho)).add
    ((hf.dz hU o).dz hU o)).sub (((hf.inv_mul ha hU ho).inv_mul ha hU ho).smul c)).band_mul
      o.epsilon

end LocalShell

section FluxSupport

variable {a b : ℝ} (ha : 0 < a) {U : Set P} (hU : IsOpen U)
  {base m h : Triple (Point P)} (hb : SmoothTriple (positiveDomain U) base)
  (hm : LocalTriple a b U m) (hh : LocalTriple a b U h)

include ha hU hb hm in
theorem thetaAxial_localShell : LocalShell a b U (thetaAxial base m) :=
  ((hm.angular.coefficient_mul ha hU hb.axial).add
    (hm.axial.coefficient_mul ha hU hb.angular)).add (hm.axial.mul hm.angular)

include ha hU hb hm in
theorem axialAxial_localShell : LocalShell a b U (axialAxial base m) :=
  ((hm.axial.coefficient_mul ha hU hb.axial).smul 2).add (hm.axial.mul hm.axial)

include ha hU hb hm in
theorem axialRadial_localShell : LocalShell a b U (axialRadial base m) :=
  ((hm.axial.coefficient_mul ha hU hb.radial).add
    (hm.radial.mul_coefficient ha hU hb.axial)).add (hm.radial.mul hm.axial)

include ha hU hb hm in
theorem radialRadial_localShell : LocalShell a b U (radialRadial base m) :=
  ((hm.radial.coefficient_mul ha hU hb.radial).smul 2).add (hm.radial.mul hm.radial)

include ha hU hb hm in
theorem radialAngular_localShell : LocalShell a b U (radialAngular base m) :=
  ((hm.angular.coefficient_mul ha hU hb.angular).smul 2).add (hm.angular.mul hm.angular)

include ha hU hb hm in
theorem gr_localShell {o : Operators (Point P)} (ho : LocalOperators U o)
    (W : Fin 3 → Fin 3 → ScalarField (Point P)) (hW : ∀ i j, LocalShell a b U (W i j)) :
    LocalShell a b U (gr o base m W) :=
  (((((hm.radial.time hU o).add
    (((radialRadial_localShell ha hU hb hm).add (hW 0 0)).radialDiv ha hU ho 1)).add
    (((axialRadial_localShell ha hU hb hm).add (hW 2 0)).dz hU o)).sub
    (((radialAngular_localShell ha hU hb hm).add (hW 1 1)).inv_mul ha hU ho)).sub
    (hm.radial.viscosity ha hU ho 1)).neg

include ha hU hb hh in
theorem leadingRadial_localShell {o : Operators (Point P)} (ho : LocalOperators U o) :
    LocalShell a b U (leadingRadial o base h) :=
  (((hh.angular.coefficient_mul ha hU hb.angular).smul 2).inv_mul ha hU ho)

include hm hh in
theorem thetaQuadratic_localShell : LocalShell a b U (DefectIncrementBounds.thetaQuadratic m h) :=
  ((hm.axial.mul hh.angular).add (hh.axial.mul hm.angular)).add (hh.axial.mul hh.angular)

include hm hh in
theorem axialQuadratic_localShell : LocalShell a b U (DefectIncrementBounds.axialQuadratic m h) :=
  ((hm.axial.mul hh.axial).smul 2).add (hh.axial.mul hh.axial)

include ha hU hb hh in
theorem thetaLeading_localShell : LocalShell a b U (DefectIncrementBounds.thetaLeading base h) :=
  (hh.angular.coefficient_mul ha hU hb.axial).add (hh.axial.coefficient_mul ha hU hb.angular)

include ha hU hb hh in
theorem axialLeading_localShell : LocalShell a b U (DefectIncrementBounds.axialLeading base h) :=
  (hh.axial.coefficient_mul ha hU hb.axial).smul 2

include ha hU hb hm hh in
theorem actualRadialError_localShell {o : Operators (Point P)} (ho : LocalOperators U o)
    (W : Fin 3 → Fin 3 → ScalarField (Point P)) (hW : ∀ i j, LocalShell a b U (W i j)) :
    LocalShell a b U (DefectIncrementBounds.actualRadialError o base m h W) :=
  ((gr_localShell ha hU hb (hm.updated hh) ho W hW).sub
    (gr_localShell ha hU hb hm ho W hW)).sub (leadingRadial_localShell ha hU hb hh ho)

end FluxSupport

open DefectIncrementBounds

theorem LocalShell.barIntegrable {a b : ℝ} {U : Set P} {f : ScalarField (Point P)}
    (hf : LocalShell a b U f) (hU : IsOpen U) (k n : ℕ) {p : P} (hp : p ∈ U) :
    Integrable (fun r => r ^ k * PressureStream.torusAverage (f n) (r, p)) := by
  simpa only [PressureStream.torusAverage, PressureStream.torusInner,
    PhysicalMeanDomain.freezeSlow] using
    (hf.freeze hU hp).barIntegrable k n p

theorem LocalShell.sliceIntegrable {a b : ℝ} {U : Set P} {f : ScalarField (Point P)}
    (hf : LocalShell a b U f) (hU : IsOpen U) (k n : ℕ) {p : P} (hp : p ∈ U) :
    Integrable (fun r => r ^ k * slowSlice f n p r) := by
  simpa only [slowSlice, PhysicalMeanDomain.freezeSlow] using (hf.freeze hU hp).sliceIntegrable k n
    p

theorem barMoment_add_on {a b : ℝ} {U : Set P} (hU : IsOpen U) {f g : ScalarField (Point P)}
    (hf : LocalShell a b U f) (hg : LocalShell a b U g) (k n : ℕ) {p : P} (hp : p ∈ U) :
    barMoment k (f + g) n p = barMoment k f n p + barMoment k g n p := by
  have h := congrFun (congrFun (barMoment_add (hf.freeze hU hp) (hg.freeze hU hp) k) n) p
  simpa only [barMoment_apply, PressureStream.torusAverage, PressureStream.torusInner,
    PhysicalMeanDomain.freezeSlow, Pi.add_apply] using h

theorem barMoment_sub_on {a b : ℝ} {U : Set P} (hU : IsOpen U) {f g : ScalarField (Point P)}
    (hf : LocalShell a b U f) (hg : LocalShell a b U g) (k n : ℕ) {p : P} (hp : p ∈ U) :
    barMoment k (f - g) n p = barMoment k f n p - barMoment k g n p := by
  have h := congrFun (congrFun (barMoment_sub (hf.freeze hU hp) (hg.freeze hU hp) k) n) p
  simpa only [barMoment_apply, PressureStream.torusAverage, PressureStream.torusInner,
    PhysicalMeanDomain.freezeSlow, Pi.sub_apply] using h

theorem barMoment_mem_local [FiniteDimensional ℝ P]
    {a b cL cR : ℝ} (ha : 0 < a) (hab : a < b) (hcL : 0 < cL) (hcR : 0 < cR)
    (ε L : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hεone : ∀ n, ε n ≤ 1) (hL : ∀ n, 1 ≤ L n)
    (U : Set P) (hU : IsOpen U) {α : ℝ} {f : ScalarField (Point P)} (hf : LocalShell a b U f)
    (hclass : MeanClass (PhysicalMeanDomain.localStripData a b cL cR ha hcL hcR ε L hε hεone hL U
      hU) α f)
    (k : ℕ) :
    UnweightedClass (PhysicalMeanDomain.localSlowStripData U hU ε L hε hεone hL) α (barMoment k f)
      := by
  have h := PhysicalMeanDomain.meanClass_radialMoment ha hab hcL hcR ε L hε hεone hL U hU
    hf.smooth hf.supported hclass k
  have he : barMoment k f = fun n =>
      IntegratedMeanBalances.radialMoment k (PressureStream.torusAverage (f n)) := by
    funext n p
    exact barMoment_apply k f n p
  rw [he]
  exact h

section ExactMoments

variable {a b : ℝ} (ha : 0 < a) {U : Set P} (hU : IsOpen U)
  {o : Operators (Point P)} (hop : LocalOperators U o)
  {base m h : Triple (Point P)} (hb : SmoothTriple (positiveDomain U) base)
  (hm : LocalTriple a b U m) (hh : LocalTriple a b U h)
  (W : Fin 3 → Fin 3 → ScalarField (Point P)) (hW : ∀ i j, LocalShell a b U (W i j))

include ha hU hop hb hm hh hW in
theorem pressureDefect_update_on (n : ℕ) {p : P} (hp : p ∈ U) :
    pressureDefect o base (updated m h) W n p = pressureDefect o base m W n p +
      barMoment 0 (leadingRadial o base h) n p + barMoment 0 (actualRadialError o base m h W) n p
        := by
  have h0 := gr_localShell ha hU hb hm hop W hW
  have hl := leadingRadial_localShell ha hU hb hh hop
  have hr := actualRadialError_localShell ha hU hb hm hh hop W hW
  unfold pressureDefect
  rw [radial_update_split, barMoment_add_on hU (h0.add hl) hr 0 n hp,
    barMoment_add_on hU h0 hl 0 n hp]

include ha hU hb hm hh hW in
theorem thetaDefect_update_on (n : ℕ) {p : P} (hp : p ∈ U) :
    thetaDefect base (updated m h) W n p = thetaDefect base m W n p +
      barMoment 2 (thetaLeading base h) n p + barMoment 2 (thetaQuadratic m h) n p := by
  have h0 := (thetaAxial_localShell ha hU hb hm).add (hW 2 1)
  have hl := thetaLeading_localShell ha hU hb hh
  have hr := thetaQuadratic_localShell hm hh
  unfold thetaDefect
  rw [thetaAxial_update_split, barMoment_add_on hU (h0.add hl) hr 2 n hp,
    barMoment_add_on hU h0 hl 2 n hp]

include ha hU hop hb hm hh hW in
theorem axialDefect_update_on (n : ℕ) {p : P} (hp : p ∈ U) :
    axialDefect o base (updated m h) W n p = axialDefect o base m W n p +
      (barMoment 1 (axialLeading base h) n p - (1 / 2) * barMoment 2 (leadingRadial o base h) n p) +
      (barMoment 1 (axialQuadratic m h) n p - (1 / 2) * barMoment 2 (actualRadialError o base m h
        W) n p) := by
  have hz0 := (axialAxial_localShell ha hU hb hm).add (hW 2 2)
  have hzl := axialLeading_localShell ha hU hb hh
  have hzr := axialQuadratic_localShell hm hh
  have hr0 := gr_localShell ha hU hb hm hop W hW
  have hrl := leadingRadial_localShell ha hU hb hh hop
  have hrr := actualRadialError_localShell ha hU hb hm hh hop W hW
  unfold axialDefect
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [axialAxial_update_split, radial_update_split,
    barMoment_add_on hU (hz0.add hzl) hzr 1 n hp, barMoment_add_on hU hz0 hzl 1 n hp,
    barMoment_add_on hU (hr0.add hrl) hrr 2 n hp, barMoment_add_on hU hr0 hrl 2 n hp]
  ring

include ha hU hop hb hm hh hW in
theorem defects_update_on (n : ℕ) {p : P} (hp : p ∈ U) :
    defects o base (updated m h) W n p =
      defects o base m W n p + linearRows o base h n p + remainders o base m h W n p := by
  have hP := pressureDefect_update_on ha hU hop hb hm hh W hW n hp
  have hT := thetaDefect_update_on ha hU hb hm hh W hW n hp
  have hZ := axialDefect_update_on ha hU hop hb hm hh W hW n hp
  funext i
  fin_cases i <;> simp [defects, linearRows, remainders, hP, hT, hZ]

include ha hU hop hb hm hh hW in
theorem defects_after_solved_rows_on (n : ℕ) {p : P} (hp : p ∈ U)
    (hrows : linearRows o base h n p = -defects o base m W n p) :
    defects o base (updated m h) W n p = remainders o base m h W n p := by
  rw [defects_update_on ha hU hop hb hm hh W hW n hp, hrows]
  simp

end ExactMoments

section IntegratedBounds

variable [FiniteDimensional ℝ P]
  {a b cL cR : ℝ} (ha : 0 < a) (hab : a < b) (hcL : 0 < cL) (hcR : 0 < cR)
  (ε L : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hεone : ∀ n, ε n ≤ 1) (hL : ∀ n, 1 ≤ L n)
  (U : Set P) (hU : IsOpen U) {o : Operators (Point P)} {κ H : ℝ}
  {base m h : Triple (Point P)} (hop : LocalOperators U o)
  (hbs : SmoothTriple (positiveDomain U) base)
  (hms : LocalTriple a b U m) (hhs : LocalTriple a b U h)
  (W : Fin 3 → Fin 3 → ScalarField (Point P)) (hW : ∀ i j, LocalShell a b U (W i j))
  (ho : OperatorBounds (PhysicalMeanDomain.localStripData a b cL cR ha hcL hcR ε L hε hεone hL U
    hU) o κ)
  (hb : BaseBounds (PhysicalMeanDomain.localStripData a b cL cR ha hcL hcR ε L hε hεone hL U hU)
    base)
  (hm : CumulativeBounds (PhysicalMeanDomain.localStripData a b cL cR ha hcL hcR ε L hε hεone hL U
    hU) m)
  (hh : IncrementBounds (PhysicalMeanDomain.localStripData a b cL cR ha hcL hcR ε L hε hεone hL U
    hU) H h)
  (hH : 9 / 10 ≤ H)

include ha hab hcL hcR hop hbs hms hhs hW ho hb hm hh hH in
/-- Integration uses actual local moments; the complete equation-(32)
remainder is derived before integration. -/
theorem remainders_mem_local (i : Fin 3) :
    UnweightedClass (PhysicalMeanDomain.localSlowStripData U hU ε L hε hεone hL)
      (H + 9 / 10 - 2 * κ) (fun n p => remainders o base m h W n p i) := by
  have hrc := actualRadialError_mem ho hb hm hh hH W
    (fun i j n => ((hW i j).smooth n).mono (fun _ hp => hp.2))
  have hrs := actualRadialError_localShell ha hU hbs hms hhs hop W hW
  have hr0 := barMoment_mem_local ha hab hcL hcR ε L hε hεone hL U hU hrs hrc 0
  have hr2 := barMoment_mem_local ha hab hcL hcR ε L hε hεone hL U hU hrs hrc 2
  have ht := barMoment_mem_local ha hab hcL hcR ε L hε hεone hL U hU
    (thetaQuadratic_localShell hms hhs) (thetaQuadratic_mem ho hm hh hH) 2
  have hz := barMoment_mem_local ha hab hcL hcR ε L hε hεone hL U hU
    (axialQuadratic_localShell hms hhs) (axialQuadratic_mem ho hm hh hH) 1
  fin_cases i
  · exact hr0
  · exact ht
  · exact unweighted_sub hz (unweighted_smul hr2 (1 / 2))

end IntegratedBounds

noncomputable def IsSlowOn (U : Set P) (f : ScalarField (Point P)) : Prop :=
  ∀ n R p, p ∈ U → ∀ Y, f n (R, (p, Y)) = slowSlice f n p R

namespace IsSlowOn

variable {U : Set P} {f g : ScalarField (Point P)}

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
theorem add (hf : IsSlowOn U f) (hg : IsSlowOn U g) : IsSlowOn U (f + g) := by
  intro n R p hp Y
  simp only [Pi.add_apply, slowSlice, hf n R p hp Y, hg n R p hp Y]

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
theorem mul (hf : IsSlowOn U f) (hg : IsSlowOn U g) : IsSlowOn U (f * g) := by
  intro n R p hp Y
  simp only [Pi.mul_apply, slowSlice, hf n R p hp Y, hg n R p hp Y]

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
theorem smul (hf : IsSlowOn U f) (c : ℝ) : IsSlowOn U (c • f) := by
  intro n R p hp Y
  simp only [Pi.smul_apply, smul_eq_mul, slowSlice, hf n R p hp Y]

end IsSlowOn

theorem LocalOperators.invRadius_slow {U : Set P} {o : Operators (Point P)}
    (ho : LocalOperators U o) : IsSlowOn U o.invRadius := by
  intro n R p hp Y
  simp only [Operators.invRadius, slowSlice, ho.radius_eq]

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
theorem barMoment_slow_on {U : Set P} {f : ScalarField (Point P)}
    (hf : IsSlowOn U f) (k n : ℕ) {p : P} (hp : p ∈ U) :
    barMoment k f n p = ∫ R, R ^ k * slowSlice f n p R := by
  rw [barMoment_apply]
  apply integral_congr_ae
  filter_upwards [] with R
  congr 1
  simp [PressureStream.torusAverage, PressureStream.torusInner, hf n R p hp]

theorem linearRows_eq_neg_of_fiveRows_on {a b : ℝ} (ha : 0 < a) {U : Set P} (hU : IsOpen U)
    {o : Operators (Point P)} (hop : LocalOperators U o) {base m h : Triple (Point P)}
    (hb : SmoothTriple (positiveDomain U) base) (hh : LocalTriple a b U h)
    (hV : IsSlowOn U base.angular) (hG : IsSlowOn U base.axial)
    (hv : IsSlowOn U h.angular) (hg : IsSlowOn U h.axial)
    (W : Fin 3 → Fin 3 → ScalarField (Point P)) (n : ℕ) {p : P} (hp : p ∈ U)
    (hrows : FiveRowRank.FiveRows (slowSlice base.angular n p) (slowSlice base.axial n p)
      (defects o base m W n p) (slowSlice h.angular n p) (slowSlice h.axial n p)) :
    linearRows o base h n p = -defects o base m W n p := by
  have hrslow : IsSlowOn U (leadingRadial o base h) :=
    hop.invRadius_slow.mul ((hV.mul hv).smul 2)
  have htslow : IsSlowOn U (thetaLeading base h) := (hG.mul hv).add (hV.mul hg)
  have hzslow : IsSlowOn U (axialLeading base h) := (hG.mul hg).smul 2
  have hrs := leadingRadial_localShell ha hU hb hh hop
  have hzs := axialLeading_localShell ha hU hb hh
  funext i
  fin_cases i
  · change barMoment 0 (leadingRadial o base h) n p = -(defects o base m W n p 0)
    rw [barMoment_slow_on hrslow 0 n hp]
    calc
      _ = ∫ R, (2 * slowSlice base.angular n p R / R) * slowSlice h.angular n p R := by
        apply integral_congr_ae
        filter_upwards [] with R
        simp only [slowSlice, leadingRadial, Operators.invRadius, hop.radius_eq,
          Pi.mul_apply, Pi.smul_apply, smul_eq_mul, pow_zero, one_mul, div_eq_mul_inv]
        ring
      _ = _ := hrows.2.2.1
  · change barMoment 2 (thetaLeading base h) n p = -(defects o base m W n p 1)
    rw [barMoment_slow_on htslow 2 n hp]
    exact hrows.2.2.2.1
  · change barMoment 1 (axialLeading base h) n p - (1 / 2) * barMoment 2 (leadingRadial o base h) n
    p =
        -(defects o base m W n p 2)
    rw [barMoment_slow_on hzslow 1 n hp, barMoment_slow_on hrslow 2 n hp]
    calc
      _ = ∫ R, R ^ (1 : ℕ) * slowSlice (axialLeading base h) n p R -
          (1 / 2) * (R ^ (2 : ℕ) * slowSlice (leadingRadial o base h) n p R) := by
        rw [integral_sub (hzs.sliceIntegrable hU 1 n hp) ((hrs.sliceIntegrable hU 2 n hp).const_mul
          (1 / 2)),
          integral_const_mul]
      _ = ∫ R, 2 * R * slowSlice base.axial n p R * slowSlice h.axial n p R -
          R * slowSlice base.angular n p R * slowSlice h.angular n p R := by
        apply integral_congr_ae
        filter_upwards [] with R
        simp only [slowSlice, axialLeading, leadingRadial, Operators.invRadius, hop.radius_eq,
          Pi.mul_apply, Pi.smul_apply, smul_eq_mul, pow_one]
        by_cases hr : R = 0
        · simp [hr]
        · field_simp
      _ = _ := hrows.2.2.2.2

/-! ## The constructed rank source and the variable gauge -/

theorem gauge_streamPotential_eq_fixed (d a b M : ℝ) (ell : P → ℝ)
    (v : PressureStream.Plane) (f : Point P → ℝ) (p : Point P) :
    VariableGaugeMean.streamPotential d a b M ell v f p =
      PressureStream.streamPotential d (ell p.2.1 * a) (ell p.2.1 * b) M ((0 : P), v) f p := by
  simp only [VariableGaugeMean.streamPotential, PressureStream.streamPotential,
    PressureStream.divideRadius, VariableGaugeMean.compactPrimitive]

/-- A zero-mass slow source removes the actual variable gauge cutoff. -/
theorem slow_gaugePotential_eq_scaledPrimitive {a b d M : ℝ} (ha : 0 < a) (hab : a < b)
    (hd : 0 < d) (ell : P → ℝ) (v : PressureStream.Plane) (f : ℝ × P → ℝ)
    (p : Point P) (hl : 0 < ell p.2.1)
    (hf : ContDiff ℝ ∞ (fun R => f (R, p.2.1)))
    (hs : support (fun R => f (R, p.2.1)) ⊆ Icc (ell p.2.1 * a) (ell p.2.1 * b))
    (hm : (∫ R, R * f (R, p.2.1)) = 0) :
    VariableGaugeMean.streamPotential d a b M ell v (MeanRankUpdate.slowLift f) p =
      MeanRankUpdate.scaledPrimitive (fun R => f (R, p.2.1)) p.1 := by
  rw [gauge_streamPotential_eq_fixed d a b M ell v (MeanRankUpdate.slowLift f) p]
  exact MeanRankUpdate.slow_streamPotential_eq_scaledPrimitive_slice (M := M)
    (mul_pos hl ha) (mul_lt_mul_of_pos_left hab hl) hd v f p hf hs hm

theorem rankDesired_slice_smooth (r : CorrectionState.RankData P)
    (c : CorrectionState.Context (Point P)) (u : CorrectionState.State (Point P)) (n : ℕ) (x : P) :
    ContDiff ℝ ∞ (fun R => CorrectionState.rankDesiredAxial r c u n (R, x)) :=
  MeanRankUpdate.desiredAxialIncrement_smooth r.lambda (r.coefficient n x) r.inner r.outer
    (r.length n x) (r.velocity n x) (CorrectionState.debt c u n x)

/-- Primitive rank data and the actual base patch model, restricted to the
open physical slow domain.  Invertibility, masses, and rows are conclusions. -/
structure RankGeometry (g : VariableGaugeMean.GaugeData P) (r : CorrectionState.RankData P)
    (U : Set P) (c : CorrectionState.Context (Point P)) (u : CorrectionState.State (Point P)) :
      Prop where
  primitive_inner_pos : 0 < g.radial.inner
  exponent_pos : 0 < g.radial.exponent
  lambda_pos : 0 < r.lambda
  inner_pos : 0 < r.inner
  inner_lt_outer : r.inner < r.outer
  coefficient_ne : ∀ n x, x ∈ U → r.coefficient n x ≠ 0
  length_pos : ∀ n x, x ∈ U → 0 < r.length n x
  velocity_ne : ∀ n x, x ∈ U → r.velocity n x ≠ 0
  coefficient_smooth : ∀ n, ContDiffOn ℝ ∞ (r.coefficient n) U
  length_smooth : ∀ n, ContDiffOn ℝ ∞ (r.length n) U
  velocity_smooth : ∀ n, ContDiffOn ℝ ∞ (r.velocity n) U
  debt_smooth : ∀ n, ContDiffOn ℝ ∞ (CorrectionState.debt c u n) U
  gauge_length_pos : ∀ n x, x ∈ U → 0 < g.length n x
  gauge_left : ∀ n x, x ∈ U → g.length n x * g.radial.inner ≤ r.length n x * r.inner
  gauge_right : ∀ n x, x ∈ U → r.length n x * r.outer ≤ g.length n x * g.radial.outer
  angular_model : ∀ n x, x ∈ U → ∀ R ∈ Ioo (r.length n x * r.inner) (r.length n x * r.outer),
    c.base.angular n (R, (x, 0)) =
      MeanRankUpdate.background r.lambda (r.coefficient n x) (r.length n x) (r.velocity n x) R
  axial_model : ∀ n x, x ∈ U → ∀ R ∈ Ioo (r.length n x * r.inner) (r.length n x * r.outer),
    c.base.axial n (R, (x, 0)) = 0

namespace RankGeometry

variable {g : VariableGaugeMean.GaugeData P} {r : CorrectionState.RankData P} {U : Set P}
  {c : CorrectionState.Context (Point P)} {u : CorrectionState.State (Point P)}
  (hg : RankGeometry g r U c u)

include hg

theorem angular_smooth (n : ℕ) :
    ContDiffOn ℝ ∞ (CorrectionState.rankAngular r c u n) (univ ×ˢ U) :=
  MeanRankUpdate.angularFamily_contDiffOn r.lambda r.inner r.outer
    (hg.length_smooth n) (hg.velocity_smooth n) (hg.coefficient_smooth n) (hg.debt_smooth n)
    (fun x hx => (hg.length_pos n x hx).ne') (hg.velocity_ne n) (hg.coefficient_ne n)

theorem desired_smooth (n : ℕ) :
    ContDiffOn ℝ ∞ (CorrectionState.rankDesiredAxial r c u n) (univ ×ˢ U) :=
  MeanRankUpdate.desiredAxialFamily_contDiffOn r.lambda r.inner r.outer
    (hg.length_smooth n) (hg.velocity_smooth n) (hg.coefficient_smooth n) (hg.debt_smooth n)
    (fun x hx => (hg.length_pos n x hx).ne') (hg.velocity_ne n) (hg.coefficient_ne n)

theorem angular_lift_smooth (n : ℕ) :
    ContDiffOn ℝ ∞ (MeanRankUpdate.slowLift (CorrectionState.rankAngular r c u n))
      (PhysicalMeanDomain.slowDomain U) :=
  (hg.angular_smooth n).comp (contDiffOn_fst.prodMk contDiffOn_snd.fst)
    (fun _ hp => ⟨mem_univ _, hp⟩)

theorem desired_lift_smooth (n : ℕ) :
    ContDiffOn ℝ ∞ (MeanRankUpdate.slowLift (CorrectionState.rankDesiredAxial r c u n))
      (PhysicalMeanDomain.slowDomain U) :=
  (hg.desired_smooth n).comp (contDiffOn_fst.prodMk contDiffOn_snd.fst)
    (fun _ hp => ⟨mem_univ _, hp⟩)

theorem desired_slice_support (n : ℕ) {x : P} (hx : x ∈ U) {lo hi : ℝ}
    (hlo : lo ≤ r.length n x * r.inner) (hhi : r.length n x * r.outer ≤ hi) :
    support (fun R => CorrectionState.rankDesiredAxial r c u n (R, x)) ⊆ Icc lo hi := by
  intro R hR
  change MeanRankUpdate.desiredAxialIncrement r.lambda (r.coefficient n x) r.inner r.outer
    (r.length n x) (r.velocity n x) (CorrectionState.debt c u n x) R ≠ 0 at hR
  have h := MeanRankUpdate.desiredAxialIncrement_tsupport r.lambda (r.coefficient n x)
    r.inner r.outer (r.velocity n x) (hg.length_pos n x hx) hg.inner_lt_outer
    (CorrectionState.debt c u n x) (subset_tsupport _ hR)
  exact ⟨hlo.trans h.1.le, h.2.le.trans hhi⟩

theorem desired_supported {a b : ℝ}
    (hleft : ∀ n x, x ∈ U → a ≤ r.length n x * r.inner)
    (hright : ∀ n x, x ∈ U → r.length n x * r.outer ≤ b) (n : ℕ) :
    PhysicalMeanDomain.SupportedOn a b U
      (MeanRankUpdate.slowLift (CorrectionState.rankDesiredAxial r c u n)) := by
  intro p hp hn
  exact hg.desired_slice_support n hp (hleft n _ hp) (hright n _ hp) hn

theorem angular_supported {a b : ℝ}
    (hleft : ∀ n x, x ∈ U → a ≤ r.length n x * r.inner)
    (hright : ∀ n x, x ∈ U → r.length n x * r.outer ≤ b) (n : ℕ) :
    PhysicalMeanDomain.SupportedOn a b U
      (MeanRankUpdate.slowLift (CorrectionState.rankAngular r c u n)) := by
  intro p hp hn
  change MeanRankUpdate.angularIncrement r.lambda (r.coefficient n p.2.1) r.inner r.outer
    (r.length n p.2.1) (r.velocity n p.2.1) (CorrectionState.debt c u n p.2.1) p.1 ≠ 0 at hn
  have h := MeanRankUpdate.angularIncrement_tsupport r.lambda (r.coefficient n p.2.1)
    r.inner r.outer (r.velocity n p.2.1) (hg.length_pos n p.2.1 hp) hg.inner_lt_outer
    (CorrectionState.debt c u n p.2.1) (subset_tsupport _ hn)
  exact ⟨(hleft n _ hp).trans h.1.le, h.2.le.trans (hright n _ hp)⟩

theorem desired_mass_zero (n : ℕ) {x : P} (hx : x ∈ U) :
    (∫ R, R * CorrectionState.rankDesiredAxial r c u n (R, x)) = 0 :=
  (CorrectionState.rank_model_rows r c u n x hg.lambda_pos (hg.coefficient_ne n x hx)
    hg.inner_pos hg.inner_lt_outer (hg.length_pos n x hx) (hg.velocity_ne n x hx)).2.1

theorem potential_eq_scaledPrimitive (n : ℕ) {p : Point P} (hp : p.2.1 ∈ U) :
    VariableGaugeMean.rankPotential g r c u n p =
      MeanRankUpdate.scaledPrimitive (fun R => CorrectionState.rankDesiredAxial r c u n (R, p.2.1))
        p.1 := by
  exact slow_gaugePotential_eq_scaledPrimitive (M := g.radial.frequency n)
    hg.primitive_inner_pos g.radial.inner_lt_outer
    hg.exponent_pos (g.length n) g.radial.radialDirection (CorrectionState.rankDesiredAxial r c u
      n) p
    (hg.gauge_length_pos n _ hp)
    (rankDesired_slice_smooth r c u n p.2.1)
    (hg.desired_slice_support n hp (hg.gauge_left n _ hp) (hg.gauge_right n _ hp))
    (hg.desired_mass_zero n hp)

theorem potential_eq_fixed {a b : ℝ} (ha : 0 < a) (hab : a < b)
    (hleft : ∀ n x, x ∈ U → a ≤ r.length n x * r.inner)
    (hright : ∀ n x, x ∈ U → r.length n x * r.outer ≤ b)
    (n : ℕ) {p : Point P} (hp : p.2.1 ∈ U) :
    VariableGaugeMean.rankPotential g r c u n p =
      PressureStream.streamPotential g.radial.exponent a b (g.radial.frequency n)
        ((0 : P), g.radial.radialDirection)
        (MeanRankUpdate.slowLift (CorrectionState.rankDesiredAxial r c u n)) p := by
  rw [hg.potential_eq_scaledPrimitive n hp]
  exact (MeanRankUpdate.slow_streamPotential_eq_scaledPrimitive_slice (M := g.radial.frequency n)
    ha hab hg.exponent_pos g.radial.radialDirection (CorrectionState.rankDesiredAxial r c u n) p
    (rankDesired_slice_smooth r c u n p.2.1)
    (hg.desired_slice_support n hp (hleft n _ hp) (hright n _ hp)) (hg.desired_mass_zero n hp)).symm

theorem potential_eventuallyEq_fixed {a b : ℝ} (ha : 0 < a) (hab : a < b) (hU : IsOpen U)
    (hleft : ∀ n x, x ∈ U → a ≤ r.length n x * r.inner)
    (hright : ∀ n x, x ∈ U → r.length n x * r.outer ≤ b)
    (n : ℕ) {p : Point P} (hp : p.2.1 ∈ U) :
    VariableGaugeMean.rankPotential g r c u n =ᶠ[𝓝 p]
      PressureStream.streamPotential g.radial.exponent a b (g.radial.frequency n)
        ((0 : P), g.radial.radialDirection)
        (MeanRankUpdate.slowLift (CorrectionState.rankDesiredAxial r c u n)) := by
  filter_upwards [(PhysicalMeanDomain.slowDomain_open hU).mem_nhds hp] with z hz
  exact hg.potential_eq_fixed ha hab hleft hright n hz

variable [FiniteDimensional ℝ P]

theorem potential_localShell {a b : ℝ} (ha : 0 < a) (hab : a < b) (hU : IsOpen U)
    (hleft : ∀ n x, x ∈ U → a ≤ r.length n x * r.inner)
    (hright : ∀ n x, x ∈ U → r.length n x * r.outer ≤ b) :
    LocalShell a b U (VariableGaugeMean.rankPotential g r c u) := by
  constructor
  · intro n
    exact (PhysicalMeanDomain.streamPotential_contDiffOn (M := g.radial.frequency n)
      ha hab hg.exponent_pos g.radial.radialDirection hU (hg.desired_lift_smooth n)
      (hg.desired_supported hleft hright n)).congr
        (fun p hp => hg.potential_eq_fixed ha hab hleft hright n hp)
  · intro n p hp hn
    rw [hg.potential_eq_fixed ha hab hleft hright n hp] at hn
    exact ((PhysicalMeanDomain.streamPotential_fiberLocal g.radial.exponent a b (g.radial.frequency
      n)
      g.radial.radialDirection).supportedOn
        (fun _ hf hs => PressureStream.streamPotential_supported ha hab hg.exponent_pos _ hf hs)
        hU (hg.desired_lift_smooth n) (hg.desired_supported hleft hright n)) p hp hn

/-- The actual variable-gauge axial stream is the desired rank source. -/
theorem axial_exact {a b : ℝ} (ha : 0 < a) (hab : a < b) (hU : IsOpen U)
    (hleft : ∀ n x, x ∈ U → a ≤ r.length n x * r.inner)
    (hright : ∀ n x, x ∈ U → r.length n x * r.outer ≤ b)
    (axial : P × PressureStream.Plane) (n : ℕ) {p : Point P} (hp : p.2.1 ∈ U) :
    (VariableGaugeMean.rankIncrementState g r axial c u).axial n p =
      CorrectionState.rankDesiredAxial r c u n (p.1, p.2.1) := by
  have he := hg.potential_eventuallyEq_fixed ha hab hU hleft hright n hp
  have hF := PhysicalMeanDomain.streamPotential_contDiffOn (M := g.radial.frequency n)
    ha hab hg.exponent_pos g.radial.radialDirection hU (hg.desired_lift_smooth n)
    (hg.desired_supported hleft hright n)
  have h := MeanRankUpdate.slow_streamGamma_eq_desired_slice (M := g.radial.frequency n) ha hab
    hg.exponent_pos
    g.radial.radialDirection (CorrectionState.rankDesiredAxial r c u n) p
    (rankDesired_slice_smooth r c u n p.2.1)
    (hg.desired_slice_support n hp (hleft n _ hp) (hright n _ hp))
    (hg.desired_mass_zero n hp)
    ((hF.contDiffAt ((PhysicalMeanDomain.slowDomain_open hU).mem_nhds hp)).differentiableAt (by
      simp))
  simpa only [VariableGaugeMean.rankIncrementState, PressureStream.streamGamma,
    PressureStream.graphDr,
    PressureStream.divideRadius, he.fderiv_eq, he.self_of_nhds] using h

end RankGeometry

theorem streamBeta_smul (a : ℝ) (w : P × PressureStream.Plane) (F : Point P → ℝ) :
    PressureStream.streamBeta (a • w) F = fun p => a * PressureStream.streamBeta w F p := by
  funext p
  have he : ((0 : ℝ), a • w) = a • ((0 : ℝ), w) := by simp
  simp only [PressureStream.streamBeta, PressureStream.graphDz, he, map_smul, smul_eq_mul]
  ring

theorem rankStage_covariance (g : VariableGaugeMean.GaugeData P) (r : CorrectionState.RankData P)
    (axial : P × PressureStream.Plane) (c : CorrectionState.Context (Point P))
    (u : CorrectionState.State (Point P)) :
    (VariableGaugeMean.rankStageState g r axial c u).covariance = u.covariance := by
  funext i j
  change CorrectionState.bilinearCovariance (u.oscillation + 0) (u.oscillation + 0) i j = _
  rw [add_zero]
  rfl

theorem rankStage_debt_eq (g : VariableGaugeMean.GaugeData P) (r : CorrectionState.RankData P)
    (axial : P × PressureStream.Plane) (c : CorrectionState.Context (Point P))
    (u : CorrectionState.State (Point P)) :
    CorrectionState.debt c (VariableGaugeMean.rankStageState g r axial c u) =
      defects c.operators c.base (updated u.mean (VariableGaugeMean.rankIncrementState g r axial c
        u))
        u.covariance := by
  rw [← defects_eq_stateDebt, rankStage_covariance]
  rfl

theorem rank_angular_slow (g : VariableGaugeMean.GaugeData P) (r : CorrectionState.RankData P)
    (axial : P × PressureStream.Plane) (U : Set P) (c : CorrectionState.Context (Point P))
    (u : CorrectionState.State (Point P)) :
    IsSlowOn U (VariableGaugeMean.rankIncrementState g r axial c u).angular := by
  intro n R p hp Y
  rfl

namespace RankGeometry

variable [FiniteDimensional ℝ P]
  {g : VariableGaugeMean.GaugeData P} {r : CorrectionState.RankData P} {U : Set P}
  {c : CorrectionState.Context (Point P)} {u : CorrectionState.State (Point P)}
  (hg : RankGeometry g r U c u)

include hg

theorem increment_localTriple {a b : ℝ} (ha : 0 < a) (hab : a < b) (hU : IsOpen U)
    (hleft : ∀ n x, x ∈ U → a ≤ r.length n x * r.inner)
    (hright : ∀ n x, x ∈ U → r.length n x * r.outer ≤ b)
    (axial : P × PressureStream.Plane) :
    LocalTriple a b U (VariableGaugeMean.rankIncrementState g r axial c u) := by
  have hp := hg.potential_localShell ha hab hU hleft hright
  constructor
  · have hr := ((hp.directional hU (0, axial)).neg).band_mul c.operators.epsilon
    simpa only [VariableGaugeMean.rankIncrementState, streamBeta_smul,
      PressureStream.streamBeta, PressureStream.graphDz, Pi.neg_apply] using hr
  · exact ⟨hg.angular_lift_smooth, hg.angular_supported hleft hright⟩
  · constructor
    · intro n
      exact (hg.desired_lift_smooth n).congr
        (fun p hp => hg.axial_exact ha hab hU hleft hright axial n hp)
    · intro n p hp hn
      rw [hg.axial_exact ha hab hU hleft hright axial n hp] at hn
      exact hg.desired_supported hleft hright n p hp hn

theorem axial_slow {a b : ℝ} (ha : 0 < a) (hab : a < b) (hU : IsOpen U)
    (hleft : ∀ n x, x ∈ U → a ≤ r.length n x * r.inner)
    (hright : ∀ n x, x ∈ U → r.length n x * r.outer ≤ b)
    (axial : P × PressureStream.Plane) :
    IsSlowOn U (VariableGaugeMean.rankIncrementState g r axial c u).axial := by
  intro n R p hp Y
  change (VariableGaugeMean.rankIncrementState g r axial c u).axial n (R, (p, Y)) =
    (VariableGaugeMean.rankIncrementState g r axial c u).axial n (R, (p, 0))
  rw [hg.axial_exact ha hab hU hleft hright axial n hp,
    hg.axial_exact ha hab hU hleft hright axial n hp]

theorem divergence_zero {a b : ℝ} (ha : 0 < a) (hab : a < b) (hU : IsOpen U)
    (hleft : ∀ n x, x ∈ U → a ≤ r.length n x * r.inner)
    (hright : ∀ n x, x ∈ U → r.length n x * r.outer ≤ b)
    (axial : P × PressureStream.Plane) (n : ℕ) {p : Point P} (hp : p.2.1 ∈ U) (hr : p.1 ≠ 0) :
    PressureStream.graphDivergence
      (PressureStream.physicalSpeed g.radial.exponent (g.radial.frequency n))
      ((0 : P), g.radial.radialDirection) (c.operators.epsilon n • axial)
      ((VariableGaugeMean.rankIncrementState g r axial c u).radial n)
      ((VariableGaugeMean.rankIncrementState g r axial c u).axial n) p = 0 := by
  have hpot := ((hg.potential_localShell ha hab hU hleft hright).smooth n).contDiffAt
    ((PhysicalMeanDomain.slowDomain_open hU).mem_nhds hp)
  exact PressureStream.stream_divergence_zero _ _
    (hpot.of_le (ENat.natCast_lt_of_coe_top_le_withTop le_rfl 2).le)
    ((PressureStream.physicalSpeed_smooth _ _ hr).differentiableAt (by simp)) hr

theorem fiveRows {a b : ℝ} (ha : 0 < a) (hab : a < b) (hU : IsOpen U)
    (hleft : ∀ n x, x ∈ U → a ≤ r.length n x * r.inner)
    (hright : ∀ n x, x ∈ U → r.length n x * r.outer ≤ b)
    (axial : P × PressureStream.Plane) (n : ℕ) {x : P} (hx : x ∈ U) :
    FiveRowRank.FiveRows (slowSlice c.base.angular n x) (slowSlice c.base.axial n x)
      (CorrectionState.debt c u n x)
      (slowSlice (VariableGaugeMean.rankIncrementState g r axial c u).angular n x)
      (slowSlice (VariableGaugeMean.rankIncrementState g r axial c u).axial n x) := by
  have hax : slowSlice (VariableGaugeMean.rankIncrementState g r axial c u).axial n x =
      fun R => CorrectionState.rankDesiredAxial r c u n (R, x) := by
    funext R
    exact hg.axial_exact ha hab hU hleft hright axial n hx
  rw [hax]
  exact CorrectionState.rank_rows_on_patch r c u n x 0 hg.lambda_pos (hg.coefficient_ne n x hx)
    hg.inner_pos hg.inner_lt_outer (hg.length_pos n x hx) (hg.velocity_ne n x hx)
    (hg.angular_model n x hx) (hg.axial_model n x hx)

theorem solved_rows {a b : ℝ} (ha : 0 < a) (hab : a < b) (hU : IsOpen U)
    (hleft : ∀ n x, x ∈ U → a ≤ r.length n x * r.inner)
    (hright : ∀ n x, x ∈ U → r.length n x * r.outer ≤ b)
    (axial : P × PressureStream.Plane) (hop : LocalOperators U c.operators)
    (hb : SmoothTriple (positiveDomain U) c.base)
    (hV : IsSlowOn U c.base.angular) (hG : IsSlowOn U c.base.axial)
    (n : ℕ) {x : P} (hx : x ∈ U) :
    linearRows c.operators c.base (VariableGaugeMean.rankIncrementState g r axial c u) n x =
      -CorrectionState.debt c u n x :=
  linearRows_eq_neg_of_fiveRows_on ha hU hop hb (hg.increment_localTriple ha hab hU hleft hright
    axial)
    hV hG (rank_angular_slow g r axial U c u) (hg.axial_slow ha hab hU hleft hright axial)
    u.covariance n hx (hg.fiveRows ha hab hU hleft hright axial n hx)

theorem preserve_masses {a b : ℝ} (ha : 0 < a) (hab : a < b) (hU : IsOpen U)
    (hleft : ∀ n x, x ∈ U → a ≤ r.length n x * r.inner)
    (hright : ∀ n x, x ∈ U → r.length n x * r.outer ≤ b)
    (axial : P × PressureStream.Plane) (hm : LocalTriple a b U u.mean)
    (n : ℕ) {x : P} (hx : x ∈ U) :
    CorrectionState.radialMoment 2 (VariableGaugeMean.rankStageState g r axial c u).mean.angular n
      x =
        CorrectionState.radialMoment 2 u.mean.angular n x ∧
      CorrectionState.radialMoment 1 (VariableGaugeMean.rankStageState g r axial c u).mean.axial n
        x =
        CorrectionState.radialMoment 1 u.mean.axial n x := by
  have hh := hg.increment_localTriple ha hab hU hleft hright axial
  have hrows := hg.fiveRows ha hab hU hleft hright axial n hx
  have hv : barMoment 2 (VariableGaugeMean.rankIncrementState g r axial c u).angular n x = 0 := by
    rw [barMoment_slow_on (rank_angular_slow g r axial U c u) 2 n hx]
    exact hrows.1
  have hz : barMoment 1 (VariableGaugeMean.rankIncrementState g r axial c u).axial n x = 0 := by
    rw [barMoment_slow_on (hg.axial_slow ha hab hU hleft hright axial) 1 n hx]
    simpa only [pow_one] using hrows.2.1
  change barMoment 2 (u.mean.angular + (VariableGaugeMean.rankIncrementState g r axial c
    u).angular) n x = _ ∧
    barMoment 1 (u.mean.axial + (VariableGaugeMean.rankIncrementState g r axial c u).axial) n x = _
  rw [barMoment_add_on hU hm.angular hh.angular 2 n hx,
    barMoment_add_on hU hm.axial hh.axial 1 n hx, hv, hz]
  exact ⟨add_zero _, add_zero _⟩

theorem debt_eq_remainders {a b : ℝ} (ha : 0 < a) (hab : a < b) (hU : IsOpen U)
    (hleft : ∀ n x, x ∈ U → a ≤ r.length n x * r.inner)
    (hright : ∀ n x, x ∈ U → r.length n x * r.outer ≤ b)
    (axial : P × PressureStream.Plane) (hop : LocalOperators U c.operators)
    (hb : SmoothTriple (positiveDomain U) c.base) (hm : LocalTriple a b U u.mean)
    (hW : ∀ i j, LocalShell a b U (u.covariance i j))
    (hV : IsSlowOn U c.base.angular) (hG : IsSlowOn U c.base.axial)
    (n : ℕ) {x : P} (hx : x ∈ U) :
    CorrectionState.debt c (VariableGaugeMean.rankStageState g r axial c u) n x =
      remainders c.operators c.base u.mean (VariableGaugeMean.rankIncrementState g r axial c u)
        u.covariance n x := by
  rw [rankStage_debt_eq]
  exact defects_after_solved_rows_on ha hU hop hb hm (hg.increment_localTriple ha hab hU hleft
    hright axial)
    u.covariance hW n hx (hg.solved_rows ha hab hU hleft hright axial hop hb hV hG n hx)

end RankGeometry


section ConstructedBounds

variable [FiniteDimensional ℝ P]
  {a b cL cR : ℝ} (ha : 0 < a) (hab : a < b) (hcL : 0 < cL) (hcR : 0 < cR)
  (ε L : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hεone : ∀ n, ε n ≤ 1) (hL : ∀ n, 1 ≤ L n)
  (U : Set P) (hU : IsOpen U)
  {g : VariableGaugeMean.GaugeData P} {r : CorrectionState.RankData P}
  {c : CorrectionState.Context (Point P)} {u : CorrectionState.State (Point P)}
  (hg : RankGeometry g r U c u)
  (hleft : ∀ n x, x ∈ U → a ≤ r.length n x * r.inner)
  (hright : ∀ n x, x ∈ U → r.length n x * r.outer ≤ b)
  (axial : P × PressureStream.Plane) {H : ℝ}

include ha hab hcL hcR hg hleft hright in
theorem RankGeometry.potential_class
    (hsource : MeanClass (PhysicalMeanDomain.localStripData a b cL cR ha hcL hcR ε L hε hεone hL U
      hU) H
      (fun n => MeanRankUpdate.slowLift (CorrectionState.rankDesiredAxial r c u n))) :
    MeanClass (PhysicalMeanDomain.localStripData a b cL cR ha hcL hcR ε L hε hεone hL U hU) H
      (VariableGaugeMean.rankPotential g r c u) := by
  have h := PhysicalMeanDomain.meanClass_streamPotential ha hab hg.exponent_pos hcL hcR
    ε L hε hεone hL U hU hg.desired_lift_smooth (hg.desired_supported hleft hright) hsource
    g.radial.frequency (fun _ => g.radial.radialDirection)
  apply class_congr h
  intro n p hp
  exact hg.potential_eq_fixed ha hab hleft hright n hp.2

include ha hab hcL hcR hg hleft hright in
/-- The extra epsilon in the actual radial stream yields `M_(H+1)`.
Both source classes refer to the already constructed rank inverse. -/
theorem RankGeometry.increment_bounds
    (hangular : MeanClass (PhysicalMeanDomain.localStripData a b cL cR ha hcL hcR ε L hε hεone hL U
      hU) H
      (fun n => MeanRankUpdate.slowLift (CorrectionState.rankAngular r c u n)))
    (haxial : MeanClass (PhysicalMeanDomain.localStripData a b cL cR ha hcL hcR ε L hε hεone hL U
      hU) H
      (fun n => MeanRankUpdate.slowLift (CorrectionState.rankDesiredAxial r c u n)))
    (heps : BandBound (PhysicalMeanDomain.localStripData a b cL cR ha hcL hcR ε L hε hεone hL U hU)
      1
      c.operators.epsilon) :
    IncrementBounds (PhysicalMeanDomain.localStripData a b cL cR ha hcL hcR ε L hε hεone hL U hU) H
      (VariableGaugeMean.rankIncrementState g r axial c u) := by
  have hp := RankGeometry.potential_class ha hab hcL hcR ε L hε hεone hL U hU hg hleft hright haxial
  have hb : MeanClass (PhysicalMeanDomain.localStripData a b cL cR ha hcL hcR ε L hε hεone hL U hU)
    H
      (fun n => PressureStream.streamBeta axial (VariableGaugeMean.rankPotential g r c u n)) := by
    have he := (hp.directional (0, axial)).map (-ContinuousLinearMap.id ℝ ℝ)
    simp only [
      _root_.neg_apply, ContinuousLinearMap.id_apply] at he ⊢
    exact he
  constructor
  · simpa only [VariableGaugeMean.rankIncrementState, streamBeta_smul, smul_eq_mul] using
    hb.band_smul heps
  · exact hangular
  · apply class_congr haxial
    intro n p hp
    exact hg.axial_exact ha hab hU hleft hright axial n hp.2

variable {κ : ℝ}
  (hop : LocalOperators U c.operators)
  (hbs : SmoothTriple (positiveDomain U) c.base)
  (hms : LocalTriple a b U u.mean)
  (hW : ∀ i j, LocalShell a b U (u.covariance i j))
  (hV : IsSlowOn U c.base.angular) (hG : IsSlowOn U c.base.axial)
  (ho : OperatorBounds (PhysicalMeanDomain.localStripData a b cL cR ha hcL hcR ε L hε hεone hL U hU)
    c.operators κ)
  (hb : BaseBounds (PhysicalMeanDomain.localStripData a b cL cR ha hcL hcR ε L hε hεone hL U hU)
    c.base)
  (hm : CumulativeBounds (PhysicalMeanDomain.localStripData a b cL cR ha hcL hcR ε L hε hεone hL U
    hU) u.mean)
  (hangular : MeanClass (PhysicalMeanDomain.localStripData a b cL cR ha hcL hcR ε L hε hεone hL U
    hU) H
    (fun n => MeanRankUpdate.slowLift (CorrectionState.rankAngular r c u n)))
  (haxial : MeanClass (PhysicalMeanDomain.localStripData a b cL cR ha hcL hcR ε L hε hεone hL U hU)
    H
    (fun n => MeanRankUpdate.slowLift (CorrectionState.rankDesiredAxial r c u n)))
  (hH : 9 / 10 ≤ H)

include ha hab hcL hcR hg hleft hright axial hop hbs hms hW hV hG ho hb hm hangular haxial hH in
/-- The actual variable-gauge rank stage cancels the measured linear debt.
Only local primitive/source bounds are inputs. -/
theorem rankStage_defect_class (i : Fin 3) :
    UnweightedClass (PhysicalMeanDomain.localSlowStripData U hU ε L hε hεone hL)
      (H + 9 / 10 - 2 * κ)
      (fun n x => CorrectionState.debt c (VariableGaugeMean.rankStageState g r axial c u) n x i) :=
        by
  have hhs := hg.increment_localTriple ha hab hU hleft hright axial
  have hh := RankGeometry.increment_bounds ha hab hcL hcR ε L hε hεone hL U hU hg hleft hright
    axial hangular haxial ho.epsilon
  have hr := remainders_mem_local ha hab hcL hcR ε L hε hεone hL U hU hop hbs hms hhs
    u.covariance hW ho hb hm hh hH i
  apply class_congr hr
  intro n x hx
  exact congrFun (hg.debt_eq_remainders ha hab hU hleft hright axial hop hbs hms hW hV hG n hx) i

include ha hab hcL hcR hg hleft hright axial hop hbs hms hW hV hG ho hb hm hangular haxial hH in
theorem rankStage_defectBounds {σ : ℝ} (hσ : 1 + σ ≤ H + 9 / 10 - 2 * κ) :
    CorrectionState.DefectBounds (PhysicalMeanDomain.localSlowStripData U hU ε L hε hεone hL) σ c
      (VariableGaugeMean.rankStageState g r axial c u) := by
  intro i
  exact (rankStage_defect_class ha hab hcL hcR ε L hε hεone hL U hU hg hleft hright axial hop hbs
    hms hW
    hV hG ho hb hm hangular haxial hH i).mono_exponent hσ

end ConstructedBounds


/-! ## Support retained in the reserved moving patch -/

/-- Derivatives retain the moving support when its length is continuous on
the open slow domain. No global continuation of the length is needed. -/
theorem supportedGauge_directional {a b : ℝ} {ell : P → ℝ} {U : Set P}
    (hU : IsOpen U) (hell : ContinuousOn ell U) {f : Point P → ℝ}
    (hs : VariableGaugeMean.SupportedGauge a b ell U f) (v : Point P) :
    VariableGaugeMean.SupportedGauge a b ell U (fun p => fderiv ℝ f p v) := by
  classical
  intro p hp hn
  by_contra hr
  let F : Point P → ℝ × ℝ × ℝ := fun z => (z.1, (ell z.2.1 * a, ell z.2.1 * b))
  have he : ContinuousAt (fun z : Point P => ell z.2.1) p :=
    (hell.continuousAt (hU.mem_nhds hp)).comp (f := fun z : Point P => z.2.1)
      continuous_snd.fst.continuousAt
  have hF : ContinuousAt F p := ContinuousAt.prodMk continuousAt_fst
    (ContinuousAt.prodMk (he.mul continuousAt_const) (he.mul continuousAt_const))
  let O : Set (ℝ × ℝ × ℝ) := {q | q.1 < q.2.1 ∨ q.2.2 < q.1}
  have hO : IsOpen O :=
    (isOpen_lt continuous_fst continuous_snd.fst).union
      (isOpen_lt continuous_snd.snd continuous_fst)
  have hFp : F p ∈ O := by
    change p.1 < ell p.2.1 * a ∨ ell p.2.1 * b < p.1
    simpa only [mem_Icc, not_and_or, not_le] using hr
  have hzero : f =ᶠ[𝓝 p] fun _ => 0 := by
    filter_upwards [(PhysicalMeanDomain.slowDomain_open hU).mem_nhds hp,
      hF.eventually (hO.mem_nhds hFp)] with z hz hzo
    by_contra hf
    have hsz := hs z hz hf
    rcases hzo with hlo | hhi
    · exact (not_lt_of_ge hsz.1) hlo
    · exact (not_lt_of_ge hsz.2) hhi
  exact hn (by change fderiv ℝ f p v = 0; rw [hzero.fderiv_eq]; simp)

namespace RankGeometry

variable {g : VariableGaugeMean.GaugeData P} {r : CorrectionState.RankData P} {U : Set P}
  {c : CorrectionState.Context (Point P)} {u : CorrectionState.State (Point P)}
  (hg : RankGeometry g r U c u)

include hg

theorem desired_supportedGauge (n : ℕ) :
    VariableGaugeMean.SupportedGauge r.inner r.outer (r.length n) U
      (MeanRankUpdate.slowLift (CorrectionState.rankDesiredAxial r c u n)) := by
  intro p hp hn
  exact hg.desired_slice_support n hp le_rfl le_rfl hn

theorem angular_supportedGauge (axial : P × PressureStream.Plane) (n : ℕ) :
    VariableGaugeMean.SupportedGauge r.inner r.outer (r.length n) U
      ((VariableGaugeMean.rankIncrementState g r axial c u).angular n) := by
  intro p hp hn
  have h := MeanRankUpdate.angularIncrement_tsupport r.lambda (r.coefficient n p.2.1)
    r.inner r.outer (r.velocity n p.2.1) (hg.length_pos n p.2.1 hp) hg.inner_lt_outer
    (CorrectionState.debt c u n p.2.1) (subset_tsupport _ hn)
  exact ⟨h.1.le, h.2.le⟩

/-- The zero weighted mass prevents the primitive from spreading beyond
the actual reserved rank patch. -/
theorem potential_supportedGauge (n : ℕ) :
    VariableGaugeMean.SupportedGauge r.inner r.outer (r.length n) U
      (VariableGaugeMean.rankPotential g r c u n) := by
  intro p hp hn
  by_contra hr
  apply hn
  rw [hg.potential_eq_scaledPrimitive n hp]
  have hsupport := MeanRankUpdate.desiredAxialIncrement_tsupport r.lambda (r.coefficient n p.2.1)
    r.inner r.outer (r.velocity n p.2.1) (hg.length_pos n p.2.1 hp) hg.inner_lt_outer
    (CorrectionState.debt c u n p.2.1)
  exact MeanRankUpdate.scaledPrimitive_zero_of_support
    (mul_pos (hg.length_pos n p.2.1 hp) hg.inner_pos)
    (mul_lt_mul_of_pos_left hg.inner_lt_outer (hg.length_pos n p.2.1 hp))
    hsupport (hg.desired_mass_zero n hp) (fun hi => hr ⟨hi.1.le, hi.2.le⟩)

theorem radial_supportedGauge (hU : IsOpen U) (axial : P × PressureStream.Plane) (n : ℕ) :
    VariableGaugeMean.SupportedGauge r.inner r.outer (r.length n) U
      ((VariableGaugeMean.rankIncrementState g r axial c u).radial n) := by
  have h := supportedGauge_directional hU (hg.length_smooth n).continuousOn
    (hg.potential_supportedGauge n) ((0 : ℝ), c.operators.epsilon n • axial)
  intro p hp hn
  exact h p hp (neg_ne_zero.mp hn)

variable [FiniteDimensional ℝ P]

/-- All three actual rank components retain the same reserved moving
support, including the radial derivative of the stream potential. -/
theorem increment_supportedGauge {a b : ℝ} (ha : 0 < a) (hab : a < b) (hU : IsOpen U)
    (hleft : ∀ n x, x ∈ U → a ≤ r.length n x * r.inner)
    (hright : ∀ n x, x ∈ U → r.length n x * r.outer ≤ b)
    (axial : P × PressureStream.Plane) (n : ℕ) :
    VariableGaugeMean.SupportedGauge r.inner r.outer (r.length n) U
        ((VariableGaugeMean.rankIncrementState g r axial c u).radial n) ∧
      VariableGaugeMean.SupportedGauge r.inner r.outer (r.length n) U
        ((VariableGaugeMean.rankIncrementState g r axial c u).angular n) ∧
      VariableGaugeMean.SupportedGauge r.inner r.outer (r.length n) U
        ((VariableGaugeMean.rankIncrementState g r axial c u).axial n) := by
  refine ⟨hg.radial_supportedGauge hU axial n, hg.angular_supportedGauge axial n, ?_⟩
  intro p hp hn
  rw [hg.axial_exact ha hab hU hleft hright axial n hp] at hn
  exact hg.desired_supportedGauge n p hp hn

end RankGeometry

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
/-- A fixed reserved profile interval has a uniform positive distance from
both outer moving edges after division by the actual local length. -/
theorem normalized_support_margin {a b lo hi : ℝ} (hal : a < lo) (hhb : hi < b)
    (ell : ℕ → P → ℝ) (U : Set P) (f : ScalarField (Point P))
    (hell : ∀ n x, x ∈ U → 0 < ell n x)
    (hs : ∀ n, VariableGaugeMean.SupportedGauge lo hi (ell n) U (f n)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ n p, p.2.1 ∈ U → f n p ≠ 0 →
      δ ≤ p.1 / ell n p.2.1 - a ∧ δ ≤ b - p.1 / ell n p.2.1 := by
  refine ⟨min (lo - a) (b - hi), lt_min (sub_pos.mpr hal) (sub_pos.mpr hhb), ?_⟩
  intro n p hp hn
  have hr := hs n p hp hn
  have hl : lo ≤ p.1 / ell n p.2.1 := (le_div_iff₀ (hell n _ hp)).mpr (by simpa only [mul_comm]
    using hr.1)
  have hh : p.1 / ell n p.2.1 ≤ hi := (div_le_iff₀ (hell n _ hp)).mpr (by simpa only [mul_comm]
    using hr.2)
  have h1 := min_le_left (lo - a) (b - hi)
  have h2 := min_le_right (lo - a) (b - hi)
  constructor <;> linarith

end NavierStokes.LocalRankDefect
