/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import LeanPool.MarkovProcess.MarkovProcess.Killed.GluingLinearity


/-!
# The supremum resolvent on bounded real observables

The supremum resolvent of `Killed/GluingMinimal.lean` acts on nonnegative extended-real
observables.  On a bounded real observable it acts through the positive and negative parts,

  `R_lam f := (R_lam f⁺).toReal - (R_lam f⁻).toReal`   (`minimalResolventReal`),

which is well defined because a uniform bound `D` for the observable bounds both values by
`D / lam` (`Killed/GluingLinearity.lean`).  The real form is measurable in the starting point
(`measurable_minimalResolventReal`), obeys the same uniform bound
(`abs_minimalResolventReal_le`), is additive and real homogeneous on bounded measurable
observables (`minimalResolventReal_add`, `minimalResolventReal_smul`), satisfies the
resolvent equation (`minimalResolventReal_resolventEquation`), and commutes at two shifts
(`minimalResolventReal_comm`).

Additivity, and with it the resolvent equation, is available exactly when the transported
resolvents are monotone in the index; that monotonicity is a bare hypothesis here.
-/

@[expose] public section

noncomputable section PortComputability

open Filter MeasureTheory ProbabilityTheory Set Topology
open scoped ENNReal NNReal ZeroAtInfty

section

namespace MarkovProcess

variable {alpha : Type*} [MeasurableSpace alpha] {X : ℕ → Type*}
  [∀ m, MetricSpace (X m)] [∀ m, LocallyCompactSpace (X m)]
  [∀ m, SecondCountableTopology (X m)] [∀ m, MeasurableSpace (X m)] [∀ m, BorelSpace (X m)]

variable (R : ∀ m, PositiveC0ContractiveResolvent (X m)) (emb : ∀ m, X m → alpha)

/-- **The supremum resolvent on real observables**: the difference of its values on the positive
and the negative part of the observable. -/
def minimalResolventReal (lam : ℝ) (f : alpha → ℝ) (x : alpha) : ℝ :=
  (minimalResolvent R emb lam (fun y ↦ ENNReal.ofReal (f y)) x).toReal -
    (minimalResolvent R emb lam (fun y ↦ ENNReal.ofReal (-f y)) x).toReal

section Bounds


/-- A real observable bounded by `D` has both parts bounded by `D` after `ENNReal.ofReal`. -/
private theorem ofReal_le_ofReal_of_abs_le {a D : ℝ} (h : |a| ≤ D) :
    ENNReal.ofReal a ≤ ENNReal.ofReal D :=
  ENNReal.ofReal_le_ofReal ((le_abs_self a).trans h)

/-- The supremum resolvent of a bounded real observable is finite. -/
theorem minimalResolvent_ofReal_ne_top (hemb : ∀ m, MeasurableEmbedding (emb m))
    {lam : ℝ} (hlam : 0 < lam) {f : alpha → ℝ} {D : ℝ} (hfD : ∀ y, |f y| ≤ D) (x : alpha) :
    minimalResolvent R emb lam (fun y ↦ ENNReal.ofReal (f y)) x ≠ ⊤ :=
  minimalResolvent_ne_top R emb hemb hlam ENNReal.ofReal_ne_top
    (fun y ↦ ofReal_le_ofReal_of_abs_le (hfD y)) x

/-- The supremum resolvent of a bounded real observable is at most `D / lam`. -/
theorem minimalResolvent_ofReal_toReal_le (hemb : ∀ m, MeasurableEmbedding (emb m))
    {lam : ℝ} (hlam : 0 < lam) {f : alpha → ℝ} {D : ℝ} (hfD : ∀ y, |f y| ≤ D) (x : alpha) :
    (minimalResolvent R emb lam (fun y ↦ ENNReal.ofReal (f y)) x).toReal ≤ D / lam := by
  have hD0 : 0 ≤ D := (abs_nonneg (f x)).trans (hfD x)
  refine ENNReal.toReal_le_of_le_ofReal (div_nonneg hD0 hlam.le) ?_
  refine le_trans (minimalResolvent_le_of_le_const R emb hemb hlam
    (fun y ↦ ofReal_le_ofReal_of_abs_le (hfD y)) x) ?_
  rw [← ENNReal.ofReal_mul hD0]
  exact le_of_eq (by rw [div_eq_mul_inv])

end Bounds

section Elementary


/-- On a nonnegative observable the real form is the extended-real value. -/
theorem minimalResolventReal_of_nonneg (hemb : ∀ m, MeasurableEmbedding (emb m))
    {lam : ℝ} (hlam : 0 < lam) {f : alpha → ℝ} (hf0 : ∀ y, 0 ≤ f y) (x : alpha) :
    minimalResolventReal R emb lam f x =
      (minimalResolvent R emb lam (fun y ↦ ENNReal.ofReal (f y)) x).toReal := by
  have hzero : (fun y ↦ ENNReal.ofReal (-f y)) = fun _ : alpha ↦ (0 : ℝ≥0∞) := by
    funext y
    exact ENNReal.ofReal_eq_zero.mpr (neg_nonpos.mpr (hf0 y))
  rw [minimalResolventReal, hzero, minimalResolvent_zero R emb hemb hlam x,
    ENNReal.toReal_zero, sub_zero]

/-- On a bounded nonnegative observable the extended-real value is recovered from the real
form. -/
theorem ofReal_minimalResolventReal (hemb : ∀ m, MeasurableEmbedding (emb m))
    {lam : ℝ} (hlam : 0 < lam) {f : alpha → ℝ} {D : ℝ} (hfD : ∀ y, |f y| ≤ D)
    (hf0 : ∀ y, 0 ≤ f y) (x : alpha) :
    ENNReal.ofReal (minimalResolventReal R emb lam f x) =
      minimalResolvent R emb lam (fun y ↦ ENNReal.ofReal (f y)) x := by
  rw [minimalResolventReal_of_nonneg R emb hemb hlam hf0 x,
    ENNReal.ofReal_toReal (minimalResolvent_ofReal_ne_top R emb hemb hlam hfD x)]

/-- The real form is nonnegative on a nonnegative observable. -/
theorem minimalResolventReal_nonneg (hemb : ∀ m, MeasurableEmbedding (emb m))
    {lam : ℝ} (hlam : 0 < lam) {f : alpha → ℝ} (hf0 : ∀ y, 0 ≤ f y) (x : alpha) :
    0 ≤ minimalResolventReal R emb lam f x := by
  rw [minimalResolventReal_of_nonneg R emb hemb hlam hf0 x]
  exact ENNReal.toReal_nonneg

/-- **The uniform bound in the real form**: the bound of the observable divided by the shift. -/
theorem abs_minimalResolventReal_le (hemb : ∀ m, MeasurableEmbedding (emb m))
    {lam : ℝ} (hlam : 0 < lam) {f : alpha → ℝ} {D : ℝ} (hfD : ∀ y, |f y| ≤ D) (x : alpha) :
    |minimalResolventReal R emb lam f x| ≤ D / lam := by
  have hpos := minimalResolvent_ofReal_toReal_le R emb hemb hlam hfD x
  have hneg := minimalResolvent_ofReal_toReal_le R emb (f := fun y ↦ -f y) hemb hlam
    (fun y ↦ by rw [abs_neg]; exact hfD y) x
  have hpos0 : 0 ≤ (minimalResolvent R emb lam (fun y ↦ ENNReal.ofReal (f y)) x).toReal :=
    ENNReal.toReal_nonneg
  have hneg0 : 0 ≤ (minimalResolvent R emb lam (fun y ↦ ENNReal.ofReal (-f y)) x).toReal :=
    ENNReal.toReal_nonneg
  rw [minimalResolventReal, abs_le]
  constructor
  · linarith only [hneg, hpos0]
  · linarith only [hpos, hneg0]

/-- The real form is measurable in the starting point. -/
theorem measurable_minimalResolventReal (hemb : ∀ m, MeasurableEmbedding (emb m)) (lam : ℝ)
    {f : alpha → ℝ} (hf : Measurable f) :
    Measurable (minimalResolventReal R emb lam f) :=
  ((measurable_minimalResolvent R emb hemb lam
      (ENNReal.measurable_ofReal.comp hf)).ennreal_toReal).sub
    ((measurable_minimalResolvent R emb hemb lam
      (ENNReal.measurable_ofReal.comp hf.neg)).ennreal_toReal)

omit [MeasurableSpace alpha] in
/-- The real form changes sign with the observable. -/
theorem minimalResolventReal_neg (lam : ℝ) (f : alpha → ℝ) (x : alpha) :
    minimalResolventReal R emb lam (fun y ↦ -f y) x =
      -minimalResolventReal R emb lam f x := by
  have hdouble : (fun y ↦ ENNReal.ofReal (-(-f y))) = fun y ↦ ENNReal.ofReal (f y) := by
    funext y
    rw [neg_neg]
  rw [minimalResolventReal, minimalResolventReal, hdouble, neg_sub]

/-- The real form is homogeneous under a nonnegative real factor. -/
theorem minimalResolventReal_const_mul_of_nonneg (hemb : ∀ m, MeasurableEmbedding (emb m))
    (lam : ℝ) {c : ℝ} (hc : 0 ≤ c) {f : alpha → ℝ} (hf : Measurable f) (x : alpha) :
    minimalResolventReal R emb lam (fun y ↦ c * f y) x =
      c * minimalResolventReal R emb lam f x := by
  have hpos : (fun y ↦ ENNReal.ofReal (c * f y)) =
      fun y ↦ ENNReal.ofReal c * ENNReal.ofReal (f y) := by
    funext y
    rw [ENNReal.ofReal_mul hc]
  have hneg : (fun y ↦ ENNReal.ofReal (-(c * f y))) =
      fun y ↦ ENNReal.ofReal c * ENNReal.ofReal (-f y) := by
    funext y
    rw [← ENNReal.ofReal_mul hc, mul_neg]
  rw [minimalResolventReal, minimalResolventReal, hpos, hneg,
    minimalResolvent_const_mul R emb hemb lam (ENNReal.ofReal c)
      (f := fun y ↦ ENNReal.ofReal (f y)) (ENNReal.measurable_ofReal.comp hf) x,
    minimalResolvent_const_mul R emb hemb lam (ENNReal.ofReal c)
      (f := fun y ↦ ENNReal.ofReal (-f y)) (ENNReal.measurable_ofReal.comp hf.neg) x,
    ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hc]
  ring

/-- **The real form is real homogeneous.** -/
theorem minimalResolventReal_smul (hemb : ∀ m, MeasurableEmbedding (emb m)) (lam : ℝ) (c : ℝ)
    {f : alpha → ℝ} (hf : Measurable f) (x : alpha) :
    minimalResolventReal R emb lam (fun y ↦ c * f y) x =
      c * minimalResolventReal R emb lam f x := by
  rcases le_or_gt 0 c with hc | hc
  · exact minimalResolventReal_const_mul_of_nonneg R emb hemb lam hc hf x
  · have hrewrite : (fun y ↦ c * f y) = fun y ↦ -((-c) * f y) := by
      funext y
      ring
    rw [hrewrite, minimalResolventReal_neg R emb,
      minimalResolventReal_const_mul_of_nonneg R emb hemb lam (neg_nonneg.mpr hc.le) hf x]
    ring

end Elementary

section Additive


private theorem ofReal_eq_ofReal_max (t : ℝ) :
    ENNReal.ofReal t = ENNReal.ofReal (max t 0) := by
  rcases le_total 0 t with h | h
  · rw [max_eq_left h]
  · rw [max_eq_right h, ENNReal.ofReal_eq_zero.mpr h, ENNReal.ofReal_zero]

private theorem max_eq_add_max_neg (t : ℝ) : max t 0 = t + max (-t) 0 := by
  rcases le_total 0 t with h | h
  · rw [max_eq_left h, max_eq_right (neg_nonpos.mpr h), add_zero]
  · rw [max_eq_right h, max_eq_left (neg_nonneg.mpr h)]
    ring

/-- The positive and negative parts of a sum of two reals rearrange into the parts of the
summands. -/
private theorem ofReal_parts_add (a b : ℝ) :
    ENNReal.ofReal (a + b) + ENNReal.ofReal (-a) + ENNReal.ofReal (-b) =
      ENNReal.ofReal a + ENNReal.ofReal b + ENNReal.ofReal (-(a + b)) := by
  rw [ofReal_eq_ofReal_max (a + b), ofReal_eq_ofReal_max (-a), ofReal_eq_ofReal_max (-b),
    ofReal_eq_ofReal_max a, ofReal_eq_ofReal_max b, ofReal_eq_ofReal_max (-(a + b)),
    ← ENNReal.ofReal_add (le_max_right _ _) (le_max_right _ _),
    ← ENNReal.ofReal_add (add_nonneg (le_max_right _ _) (le_max_right _ _))
      (le_max_right _ _),
    ← ENNReal.ofReal_add (le_max_right _ _) (le_max_right _ _),
    ← ENNReal.ofReal_add (add_nonneg (le_max_right _ _) (le_max_right _ _))
      (le_max_right _ _)]
  congr 1
  rw [max_eq_add_max_neg a, max_eq_add_max_neg b, max_eq_add_max_neg (a + b)]
  ring

/-- The supremum resolvent of a sum of three measurable observables. -/
private theorem minimalResolvent_add_three (hemb : ∀ m, MeasurableEmbedding (emb m))
    (hmono : ∀ nu > 0, ∀ {h : alpha → ℝ≥0∞}, Measurable h → ∀ y,
      Monotone fun m ↦ localResolvent R emb m nu h y)
    {lam : ℝ} (hlam : 0 < lam) {u v w : alpha → ℝ≥0∞} (hu : Measurable u) (hv : Measurable v)
    (hw : Measurable w) (x : alpha) :
    minimalResolvent R emb lam (fun y ↦ u y + v y + w y) x =
      minimalResolvent R emb lam u x + minimalResolvent R emb lam v x +
        minimalResolvent R emb lam w x := by
  have hfun : (fun y ↦ u y + v y + w y) = fun y ↦ (u + v) y + w y := rfl
  have hfun' : (u + v) = fun y ↦ u y + v y := rfl
  rw [hfun, minimalResolvent_add R emb hemb hmono hlam (hu.add hv) hw x, hfun',
    minimalResolvent_add R emb hemb hmono hlam hu hv x]

/-- **The real form is additive** on bounded measurable observables. -/
theorem minimalResolventReal_add (hemb : ∀ m, MeasurableEmbedding (emb m))
    (hmono : ∀ nu > 0, ∀ {h : alpha → ℝ≥0∞}, Measurable h → ∀ y,
      Monotone fun m ↦ localResolvent R emb m nu h y)
    {lam : ℝ} (hlam : 0 < lam) {f g : alpha → ℝ} {D E : ℝ}
    (hf : Measurable f) (hg : Measurable g) (hfD : ∀ y, |f y| ≤ D) (hgE : ∀ y, |g y| ≤ E)
    (x : alpha) :
    minimalResolventReal R emb lam (fun y ↦ f y + g y) x =
      minimalResolventReal R emb lam f x + minimalResolventReal R emb lam g x := by
  have hsum : ∀ y, |f y + g y| ≤ D + E := fun y ↦
    (abs_add_le (f y) (g y)).trans (add_le_add (hfD y) (hgE y))
  have hmeasP1 : Measurable fun y ↦ ENNReal.ofReal (f y + g y) :=
    ENNReal.measurable_ofReal.comp (hf.add hg)
  have hmeasN1 : Measurable fun y ↦ ENNReal.ofReal (-f y) :=
    ENNReal.measurable_ofReal.comp hf.neg
  have hmeasN2 : Measurable fun y ↦ ENNReal.ofReal (-g y) :=
    ENNReal.measurable_ofReal.comp hg.neg
  have hmeasP2 : Measurable fun y ↦ ENNReal.ofReal (f y) :=
    ENNReal.measurable_ofReal.comp hf
  have hmeasP3 : Measurable fun y ↦ ENNReal.ofReal (g y) :=
    ENNReal.measurable_ofReal.comp hg
  have hmeasN3 : Measurable fun y ↦ ENNReal.ofReal (-(f y + g y)) :=
    ENNReal.measurable_ofReal.comp (hf.add hg).neg
  have hkey : minimalResolvent R emb lam (fun y ↦ ENNReal.ofReal (f y + g y)) x +
        minimalResolvent R emb lam (fun y ↦ ENNReal.ofReal (-f y)) x +
        minimalResolvent R emb lam (fun y ↦ ENNReal.ofReal (-g y)) x =
      minimalResolvent R emb lam (fun y ↦ ENNReal.ofReal (f y)) x +
        minimalResolvent R emb lam (fun y ↦ ENNReal.ofReal (g y)) x +
        minimalResolvent R emb lam (fun y ↦ ENNReal.ofReal (-(f y + g y))) x := by
    rw [← minimalResolvent_add_three R emb hemb hmono hlam hmeasP1 hmeasN1 hmeasN2 x,
      ← minimalResolvent_add_three R emb hemb hmono hlam hmeasP2 hmeasP3 hmeasN3 x]
    congr 1
    funext y
    exact ofReal_parts_add (f y) (g y)
  have hP1 := minimalResolvent_ofReal_ne_top R emb (f := fun y ↦ f y + g y) hemb hlam hsum x
  have hN1 := minimalResolvent_ofReal_ne_top R emb (f := fun y ↦ -f y) hemb hlam
    (fun y ↦ by rw [abs_neg]; exact hfD y) x
  have hN2 := minimalResolvent_ofReal_ne_top R emb (f := fun y ↦ -g y) hemb hlam
    (fun y ↦ by rw [abs_neg]; exact hgE y) x
  have hP2 := minimalResolvent_ofReal_ne_top R emb (f := f) hemb hlam hfD x
  have hP3 := minimalResolvent_ofReal_ne_top R emb (f := g) hemb hlam hgE x
  have hN3 := minimalResolvent_ofReal_ne_top R emb (f := fun y ↦ -(f y + g y)) hemb hlam
    (fun y ↦ by rw [abs_neg]; exact hsum y) x
  have hreal := congrArg ENNReal.toReal hkey
  rw [ENNReal.toReal_add (ENNReal.add_ne_top.mpr ⟨hP1, hN1⟩) hN2,
    ENNReal.toReal_add hP1 hN1,
    ENNReal.toReal_add (ENNReal.add_ne_top.mpr ⟨hP2, hP3⟩) hN3,
    ENNReal.toReal_add hP2 hP3] at hreal
  rw [minimalResolventReal, minimalResolventReal, minimalResolventReal]
  linarith only [hreal]

/-- The real form is subtractive on bounded measurable observables. -/
theorem minimalResolventReal_sub (hemb : ∀ m, MeasurableEmbedding (emb m))
    (hmono : ∀ nu > 0, ∀ {h : alpha → ℝ≥0∞}, Measurable h → ∀ y,
      Monotone fun m ↦ localResolvent R emb m nu h y)
    {lam : ℝ} (hlam : 0 < lam) {f g : alpha → ℝ} {D E : ℝ}
    (hf : Measurable f) (hg : Measurable g) (hfD : ∀ y, |f y| ≤ D) (hgE : ∀ y, |g y| ≤ E)
    (x : alpha) :
    minimalResolventReal R emb lam (fun y ↦ f y - g y) x =
      minimalResolventReal R emb lam f x - minimalResolventReal R emb lam g x := by
  have hrewrite : (fun y ↦ f y - g y) = fun y ↦ f y + (-g) y := by
    funext y
    change f y - g y = f y + -g y
    ring
  have hneg : minimalResolventReal R emb lam (-g) x =
      - minimalResolventReal R emb lam g x := by
    have h : (-g) = fun y ↦ -g y := rfl
    rw [h, minimalResolventReal_neg R emb]
  rw [hrewrite, minimalResolventReal_add R emb hemb hmono hlam hf hg.neg hfD
      (fun y ↦ by simpa using hgE y) x, hneg]
  ring

end Additive

section ResolventEquation


/-- The real form of the supremum resolvent, composed with itself, in extended-real terms. -/
theorem minimalResolventReal_comp (hemb : ∀ m, MeasurableEmbedding (emb m))
    (hmono : ∀ nu > 0, ∀ {h : alpha → ℝ≥0∞}, Measurable h → ∀ y,
      Monotone fun m ↦ localResolvent R emb m nu h y)
    {lam mu : ℝ} (hlam : 0 < lam) (hmu : 0 < mu) {f : alpha → ℝ} {D : ℝ}
    (hf : Measurable f) (hfD : ∀ y, |f y| ≤ D) (x : alpha) :
    minimalResolventReal R emb lam (fun z ↦ minimalResolventReal R emb mu f z) x =
      (minimalResolvent R emb lam
          (fun z ↦ minimalResolvent R emb mu (fun y ↦ ENNReal.ofReal (f y)) z) x).toReal -
        (minimalResolvent R emb lam
          (fun z ↦ minimalResolvent R emb mu (fun y ↦ ENNReal.ofReal (-f y)) z) x).toReal := by
  set u : alpha → ℝ := fun z ↦
    (minimalResolvent R emb mu (fun y ↦ ENNReal.ofReal (f y)) z).toReal with hu
  set v : alpha → ℝ := fun z ↦
    (minimalResolvent R emb mu (fun y ↦ ENNReal.ofReal (-f y)) z).toReal with hv
  have hfneg : ∀ y, |(-f y)| ≤ D := fun y ↦ by rw [abs_neg]; exact hfD y
  have humeas : Measurable u :=
    (measurable_minimalResolvent R emb hemb mu
      (ENNReal.measurable_ofReal.comp hf)).ennreal_toReal
  have hvmeas : Measurable v :=
    (measurable_minimalResolvent R emb hemb mu
      (ENNReal.measurable_ofReal.comp hf.neg)).ennreal_toReal
  have hu0 : ∀ z, 0 ≤ u z := fun z ↦ ENNReal.toReal_nonneg
  have hv0 : ∀ z, 0 ≤ v z := fun z ↦ ENNReal.toReal_nonneg
  have huD : ∀ z, |u z| ≤ D / mu := fun z ↦ by
    rw [abs_of_nonneg (hu0 z)]
    exact minimalResolvent_ofReal_toReal_le R emb hemb hmu hfD z
  have hvD : ∀ z, |v z| ≤ D / mu := fun z ↦ by
    rw [abs_of_nonneg (hv0 z)]
    exact minimalResolvent_ofReal_toReal_le R emb hemb hmu hfneg z
  have hsplit : (fun z ↦ minimalResolventReal R emb mu f z) = fun z ↦ u z - v z := rfl
  have hofu : (fun z ↦ ENNReal.ofReal (u z)) =
      fun z ↦ minimalResolvent R emb mu (fun y ↦ ENNReal.ofReal (f y)) z := by
    funext z
    exact ENNReal.ofReal_toReal (minimalResolvent_ofReal_ne_top R emb hemb hmu hfD z)
  have hofv : (fun z ↦ ENNReal.ofReal (v z)) =
      fun z ↦ minimalResolvent R emb mu (fun y ↦ ENNReal.ofReal (-f y)) z := by
    funext z
    exact ENNReal.ofReal_toReal (minimalResolvent_ofReal_ne_top R emb hemb hmu hfneg z)
  rw [hsplit, minimalResolventReal_sub R emb hemb hmono hlam humeas hvmeas huD hvD x,
    minimalResolventReal_of_nonneg R emb hemb hlam hu0 x,
    minimalResolventReal_of_nonneg R emb hemb hlam hv0 x, hofu, hofv]

/-- **The real form at two shifts commutes** on bounded measurable observables. -/
theorem minimalResolventReal_comm (hemb : ∀ m, MeasurableEmbedding (emb m))
    (hmono : ∀ nu > 0, ∀ {h : alpha → ℝ≥0∞}, Measurable h → ∀ y,
      Monotone fun m ↦ localResolvent R emb m nu h y)
    {lam mu : ℝ} (hlam : 0 < lam) (hmu : 0 < mu) {f : alpha → ℝ} {D : ℝ}
    (hf : Measurable f) (hfD : ∀ y, |f y| ≤ D) (x : alpha) :
    minimalResolventReal R emb lam (fun z ↦ minimalResolventReal R emb mu f z) x =
      minimalResolventReal R emb mu (fun z ↦ minimalResolventReal R emb lam f z) x := by
  rw [minimalResolventReal_comp R emb hemb hmono hlam hmu hf hfD x,
    minimalResolventReal_comp R emb hemb hmono hmu hlam hf hfD x,
    minimalResolvent_comm R emb hemb hmono hlam hmu
      (f := fun y ↦ ENNReal.ofReal (f y)) (ENNReal.measurable_ofReal.comp hf) x,
    minimalResolvent_comm R emb hemb hmono hlam hmu
      (f := fun y ↦ ENNReal.ofReal (-f y)) (ENNReal.measurable_ofReal.comp hf.neg) x]

/-- **The resolvent equation in real form** on bounded measurable observables. -/
theorem minimalResolventReal_resolventEquation (hemb : ∀ m, MeasurableEmbedding (emb m))
    (hmono : ∀ nu > 0, ∀ {h : alpha → ℝ≥0∞}, Measurable h → ∀ y,
      Monotone fun m ↦ localResolvent R emb m nu h y)
    {lam mu : ℝ} (hlam : 0 < lam) (hlt : lam < mu) {f : alpha → ℝ} {D : ℝ}
    (hf : Measurable f) (hfD : ∀ y, |f y| ≤ D) (x : alpha) :
    minimalResolventReal R emb lam f x =
      minimalResolventReal R emb mu f x +
        (mu - lam) * minimalResolventReal R emb lam
          (fun z ↦ minimalResolventReal R emb mu f z) x := by
  have hmu : 0 < mu := hlam.trans hlt
  have hfneg : ∀ y, |(-f y)| ≤ D := fun y ↦ by rw [abs_neg]; exact hfD y
  -- the extended-real resolvent equation, on the positive and on the negative part
  have hstep : ∀ (h : alpha → ℝ), Measurable h → (∀ y, |h y| ≤ D) →
      (minimalResolvent R emb lam (fun y ↦ ENNReal.ofReal (h y)) x).toReal =
        (minimalResolvent R emb mu (fun y ↦ ENNReal.ofReal (h y)) x).toReal +
          (mu - lam) * (minimalResolvent R emb lam
            (fun z ↦ minimalResolvent R emb mu (fun y ↦ ENNReal.ofReal (h y)) z) x).toReal := by
    intro h hmeas hbound
    have hmeasE : Measurable fun y ↦ ENNReal.ofReal (h y) :=
      ENNReal.measurable_ofReal.comp hmeas
    have hinnermeas : Measurable fun z ↦
        minimalResolvent R emb mu (fun y ↦ ENNReal.ofReal (h y)) z :=
      measurable_minimalResolvent R emb hemb mu hmeasE
    have hinnerbound : ∀ z, minimalResolvent R emb mu (fun y ↦ ENNReal.ofReal (h y)) z ≤
        ENNReal.ofReal D * ENNReal.ofReal mu⁻¹ :=
      fun z ↦ minimalResolvent_le_of_le_const R emb hemb hmu
        (fun y ↦ ENNReal.ofReal_le_ofReal ((le_abs_self (h y)).trans (hbound y))) z
    have houter : minimalResolvent R emb lam
        (fun z ↦ minimalResolvent R emb mu (fun y ↦ ENNReal.ofReal (h y)) z) x ≠ ⊤ :=
      minimalResolvent_ne_top R emb hemb hlam
        (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top) hinnerbound x
    have hmid : minimalResolvent R emb mu (fun y ↦ ENNReal.ofReal (h y)) x ≠ ⊤ :=
      minimalResolvent_ofReal_ne_top R emb hemb hmu hbound x
    have heq := minimalResolvent_resolventEquation_of_monotone R emb hemb hmono hlam hlt
      hmeasE x
    rw [heq, ENNReal.toReal_add hmid
        (ENNReal.mul_ne_top ENNReal.ofReal_ne_top houter),
      ENNReal.toReal_mul, ENNReal.toReal_ofReal (by linarith only [hlt])]
  have hpos := hstep f hf hfD
  have hneg := hstep (fun y ↦ -f y) hf.neg hfneg
  rw [minimalResolventReal, minimalResolventReal,
    minimalResolventReal_comp R emb hemb hmono hlam hmu hf hfD x]
  linarith only [hpos, hneg]

end ResolventEquation

end MarkovProcess

end

end PortComputability
