/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import LeanPool.MarkovProcess.MarkovProcess.Killed.GluingLocal
public import LeanPool.MarkovProcess.MarkovProcess.Killed.GluingResolventEquation


/-!
# The supremum resolvent (the minimal process of Blumenthal--Getoor, in name only)

A family of positive `C₀`-contractive resolvents `R m` on local state spaces `X m`, embedded as
an increasing family of open subsets of an ambient measurable space, is glued here at the level
of resolvents.  Each `R m` is transported to the ambient space by extending its kernel resolvent
by zero off the `m`-th domain (`localResolvent`).  Under the part-process identity of
`Killed/GluingLocal.lean` -- the resolvent of the compactified process of `R (m+1)`, killed at
the exit from the image of `X m`, is `R m` -- the transported resolvents increase with `m`
(`localResolvent_le_succ`), because a path leaves the smaller domain no later and therefore
accumulates less.  Their supremum is `minimalResolvent`.

The supremum is monotone in the observable, measurable in the starting point, and sub-Markov at
every positive shift: `lam` times its value on the constant observable one is at most one
(`ofReal_mul_minimalResolvent_one_le`).  It satisfies the resolvent equation as soon as the
transported resolvents are monotone in `m`
(`minimalResolvent_resolventEquation_of_monotone`, by monotone convergence from the resolvent
equation of each member); the part-process identity enters only through that monotonicity
(`minimalResolvent_resolventEquation`).

No minimality property among resolvent families is asserted here.  The declaration names
keep the word `minimal` because the object is the resolvent of Blumenthal--Getoor's minimal
process, but that is a name and not a claim.

The regularity data of each compactification are an explicit hypothesis throughout: positivity,
contractivity and the resolvent identity do not by themselves give a compactified semigroup a
continuous-path process.

No transition semigroup, no process on the ambient space, and no conservativity are constructed
here.
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

/-- The kernel resolvent of the `m`-th local resolvent, transported to the ambient space and
extended by zero off the `m`-th local domain. -/
noncomputable def localResolvent (m : ℕ) (lam : ℝ) (f : alpha → ℝ≥0∞) : alpha → ℝ≥0∞ :=
  Function.extend (emb m)
    (fun y ↦ (R m).kernelSemigroup.kernelResolvent lam (fun z ↦ f (emb m z)) y) 0

omit [MeasurableSpace alpha] in
/-- Inside the `m`-th local domain the transported resolvent is the `m`-th kernel resolvent. -/
theorem localResolvent_apply {m : ℕ} (hemb : Function.Injective (emb m)) (lam : ℝ)
    (f : alpha → ℝ≥0∞) (y : X m) :
    localResolvent R emb m lam f (emb m y) =
      (R m).kernelSemigroup.kernelResolvent lam (fun z ↦ f (emb m z)) y :=
  hemb.extend_apply _ _ y

omit [MeasurableSpace alpha] in
/-- Off the `m`-th local domain the transported resolvent vanishes. -/
theorem localResolvent_of_notMem (m : ℕ) (lam : ℝ) (f : alpha → ℝ≥0∞) {x : alpha}
    (hx : x ∉ Set.range (emb m)) : localResolvent R emb m lam f x = 0 :=
  Function.extend_apply' _ _ _ fun hmem ↦ hx hmem

omit [MeasurableSpace alpha] in
/-- The transported resolvent is monotone in the observable. -/
theorem localResolvent_mono_of_le {m : ℕ} (hemb : Function.Injective (emb m)) (lam : ℝ)
    {f g : alpha → ℝ≥0∞} (hfg : f ≤ g) (x : alpha) :
    localResolvent R emb m lam f x ≤ localResolvent R emb m lam g x := by
  by_cases hx : x ∈ Set.range (emb m)
  · obtain ⟨y, rfl⟩ := hx
    rw [localResolvent_apply R emb hemb lam f y, localResolvent_apply R emb hemb lam g y]
    exact (R m).kernelSemigroup.kernelResolvent_mono lam (fun z ↦ hfg (emb m z)) y
  · rw [localResolvent_of_notMem R emb m lam f hx]
    exact zero_le

/-- The transported resolvent is measurable in the starting point. -/
theorem measurable_localResolvent {m : ℕ} (hemb : MeasurableEmbedding (emb m)) (lam : ℝ)
    {f : alpha → ℝ≥0∞} (hf : Measurable f) :
    Measurable (localResolvent R emb m lam f) :=
  hemb.measurable_extend
    ((R m).kernelSemigroup.measurable_kernelResolvent lam (hf.comp hemb.measurable))
    measurable_const

/-- The transported resolvent is continuous along monotone limits of observables. -/
theorem localResolvent_iSup {m : ℕ} (hemb : MeasurableEmbedding (emb m)) (lam : ℝ)
    {f : ℕ → alpha → ℝ≥0∞} (hf : ∀ n, Measurable (f n)) (hmono : Monotone f) (x : alpha) :
    localResolvent R emb m lam (fun y ↦ ⨆ n, f n y) x =
      ⨆ n, localResolvent R emb m lam (f n) x := by
  by_cases hx : x ∈ Set.range (emb m)
  · obtain ⟨y, rfl⟩ := hx
    rw [localResolvent_apply R emb hemb.injective lam _ y]
    have hcomp : ∀ n, Measurable fun z : X m ↦ f n (emb m z) := fun n ↦
      (hf n).comp hemb.measurable
    have hmonoComp : Monotone fun n ↦ fun z : X m ↦ f n (emb m z) :=
      fun a b hab z ↦ hmono hab (emb m z)
    rw [(R m).kernelSemigroup.kernelResolvent_iSup lam hcomp hmonoComp y]
    exact iSup_congr fun n ↦ (localResolvent_apply R emb hemb.injective lam (f n) y).symm
  · have hzero : ∀ n, localResolvent R emb m lam (f n) x = 0 :=
      fun n ↦ localResolvent_of_notMem R emb m lam (f n) hx
    rw [localResolvent_of_notMem R emb m lam _ hx]
    simp only [hzero, ciSup_const]

section Compatible

variable (iota : ∀ m, X m → X (m + 1))

/-- **The transported resolvents increase along the family.**  Under the part-process identity, a
path of the larger domain is killed no earlier than a path of the smaller one, so the transported
kernel resolvents increase. -/
theorem localResolvent_le_succ (hemb : ∀ m, MeasurableEmbedding (emb m))
    (hiota : ∀ m, IsOpenEmbedding (iota m))
    (hcomm : ∀ m (y : X m), emb (m + 1) (iota m y) = emb m y)
    (hreg : ∀ m, (R m).OnePointRegular)
    (hcompat : ∀ m, PositiveC0ContractiveResolvent.IsPartProcess (R m) (R (m + 1))
      (hreg (m + 1)) (hiota m))
    {lam : ℝ} (hlam : 0 < lam) {f : alpha → ℝ≥0∞} (hf : Measurable f) (m : ℕ) (x : alpha) :
    localResolvent R emb m lam f x ≤ localResolvent R emb (m + 1) lam f x := by
  by_cases hx : x ∈ Set.range (emb m)
  · obtain ⟨y, rfl⟩ := hx
    rw [localResolvent_apply R emb (hemb m).injective lam f y, ← hcomm m y,
      localResolvent_apply R emb (hemb (m + 1)).injective lam f (iota m y)]
    have hg : Measurable fun z : X (m + 1) ↦ f (emb (m + 1) z) :=
      hf.comp (hemb (m + 1)).measurable
    have hdom := PositiveC0ContractiveResolvent.kernelResolvent_le_of_partProcess
      (R m) (R (m + 1)) (hreg (m + 1)) (hiota m) (hcompat m) hlam hg y
    have hgf : (fun z : X m ↦ f (emb (m + 1) (iota m z))) = fun z : X m ↦ f (emb m z) := by
      funext z
      rw [hcomm m z]
    rwa [hgf] at hdom
  · rw [localResolvent_of_notMem R emb m lam f hx]
    exact zero_le

/-- The transported resolvents form a monotone family. -/
theorem monotone_localResolvent (hemb : ∀ m, MeasurableEmbedding (emb m))
    (hiota : ∀ m, IsOpenEmbedding (iota m))
    (hcomm : ∀ m (y : X m), emb (m + 1) (iota m y) = emb m y)
    (hreg : ∀ m, (R m).OnePointRegular)
    (hcompat : ∀ m, PositiveC0ContractiveResolvent.IsPartProcess (R m) (R (m + 1))
      (hreg (m + 1)) (hiota m))
    {lam : ℝ} (hlam : 0 < lam) {f : alpha → ℝ≥0∞} (hf : Measurable f) (x : alpha) :
    Monotone fun m ↦ localResolvent R emb m lam f x :=
  monotone_nat_of_le_succ fun m ↦
    localResolvent_le_succ R emb iota hemb hiota hcomm hreg hcompat hlam hf m x

end Compatible

/-- **The minimal resolvent** of a family of local resolvents: the pointwise supremum of the
transported local kernel resolvents.  Monotonicity in `m`, under which the supremum is an
increasing limit, is the content of `localResolvent_le_succ`. -/
noncomputable def minimalResolvent (lam : ℝ) (f : alpha → ℝ≥0∞) (x : alpha) : ℝ≥0∞ :=
  ⨆ m, localResolvent R emb m lam f x

omit [MeasurableSpace alpha] in
/-- Each transported resolvent is dominated by the minimal resolvent. -/
theorem localResolvent_le_minimalResolvent (m : ℕ) (lam : ℝ) (f : alpha → ℝ≥0∞) (x : alpha) :
    localResolvent R emb m lam f x ≤ minimalResolvent R emb lam f x :=
  le_iSup (fun n ↦ localResolvent R emb n lam f x) m

omit [MeasurableSpace alpha] in
/-- The minimal resolvent is monotone in the observable. -/
theorem minimalResolvent_mono_of_le (hemb : ∀ m, Function.Injective (emb m)) (lam : ℝ)
    {f g : alpha → ℝ≥0∞} (hfg : f ≤ g) (x : alpha) :
    minimalResolvent R emb lam f x ≤ minimalResolvent R emb lam g x :=
  iSup_mono fun m ↦ localResolvent_mono_of_le R emb (hemb m) lam hfg x

/-- The minimal resolvent is continuous along monotone limits of observables. -/
theorem minimalResolvent_iSup (hemb : ∀ m, MeasurableEmbedding (emb m)) (lam : ℝ)
    {f : ℕ → alpha → ℝ≥0∞} (hf : ∀ n, Measurable (f n)) (hmono : Monotone f) (x : alpha) :
    minimalResolvent R emb lam (fun y ↦ ⨆ n, f n y) x =
      ⨆ n, minimalResolvent R emb lam (f n) x := by
  unfold minimalResolvent
  rw [iSup_comm]
  exact iSup_congr fun m ↦ localResolvent_iSup R emb (hemb m) lam hf hmono x

/-- The minimal resolvent is measurable in the starting point. -/
theorem measurable_minimalResolvent (hemb : ∀ m, MeasurableEmbedding (emb m)) (lam : ℝ)
    {f : alpha → ℝ≥0∞} (hf : Measurable f) :
    Measurable (minimalResolvent R emb lam f) :=
  Measurable.iSup fun m ↦ measurable_localResolvent R emb (hemb m) lam hf

omit [MeasurableSpace alpha] in
/-- At a positive shift the minimal resolvent of the constant observable one is at most
`1 / lam`. -/
theorem minimalResolvent_one_le (hemb : ∀ m, Function.Injective (emb m))
    {lam : ℝ} (hlam : 0 < lam) (x : alpha) :
    minimalResolvent R emb lam (fun _ ↦ 1) x ≤ ENNReal.ofReal lam⁻¹ := by
  refine iSup_le fun m ↦ ?_
  by_cases hx : x ∈ Set.range (emb m)
  · obtain ⟨y, rfl⟩ := hx
    rw [localResolvent_apply R emb (hemb m) lam _ y]
    exact (R m).kernelSemigroup.kernelResolvent_one_le hlam y
  · rw [localResolvent_of_notMem R emb m lam _ hx]
    exact zero_le

omit [MeasurableSpace alpha] in
/-- **The minimal resolvent is sub-Markov.**  At a positive shift, `lam` times the minimal
resolvent of the constant observable one is at most one. -/
theorem ofReal_mul_minimalResolvent_one_le (hemb : ∀ m, Function.Injective (emb m))
    {lam : ℝ} (hlam : 0 < lam) (x : alpha) :
    ENNReal.ofReal lam * minimalResolvent R emb lam (fun _ ↦ 1) x ≤ 1 := by
  calc ENNReal.ofReal lam * minimalResolvent R emb lam (fun _ ↦ 1) x
      ≤ ENNReal.ofReal lam * ENNReal.ofReal lam⁻¹ :=
        mul_le_mul' le_rfl (minimalResolvent_one_le R emb hemb hlam x)
    _ = 1 := by
        rw [← ENNReal.ofReal_mul hlam.le, mul_inv_cancel₀ hlam.ne', ENNReal.ofReal_one]

section ResolventEquation

variable (iota : ∀ m, X m → X (m + 1))

/-- Each transported resolvent satisfies the resolvent equation. -/
theorem localResolvent_resolventEquation {m : ℕ} (hemb : MeasurableEmbedding (emb m))
    {lam mu : ℝ} (hlt : lam < mu) {f : alpha → ℝ≥0∞} (hf : Measurable f) (x : alpha) :
    localResolvent R emb m lam f x =
      localResolvent R emb m mu f x +
        ENNReal.ofReal (mu - lam) *
          localResolvent R emb m lam (localResolvent R emb m mu f) x := by
  by_cases hx : x ∈ Set.range (emb m)
  · obtain ⟨y, rfl⟩ := hx
    have hinner : (fun z ↦ localResolvent R emb m mu f (emb m z)) =
        (R m).kernelSemigroup.kernelResolvent mu fun z ↦ f (emb m z) := by
      funext z
      exact localResolvent_apply R emb hemb.injective mu f z
    rw [localResolvent_apply R emb hemb.injective lam f y,
      localResolvent_apply R emb hemb.injective mu f y,
      localResolvent_apply R emb hemb.injective lam _ y, hinner]
    exact (R m).kernelSemigroup.kernelResolvent_resolventEquation hlt
      (hf.comp hemb.measurable) y
  · rw [localResolvent_of_notMem R emb m lam f hx,
      localResolvent_of_notMem R emb m mu f hx,
      localResolvent_of_notMem R emb m lam _ hx]
    simp only [mul_zero, add_zero]

/-- **The composition of two supremum resolvents is the supremum along the diagonal**, as soon
as the transported resolvents are monotone in the index. -/
theorem minimalResolvent_comp_eq_iSup (hemb : ∀ m, MeasurableEmbedding (emb m))
    (hmono : ∀ nu > 0, ∀ {g : alpha → ℝ≥0∞}, Measurable g → ∀ y,
      Monotone fun m ↦ localResolvent R emb m nu g y)
    {lam mu : ℝ} (hlam : 0 < lam) (hmu : 0 < mu) {f : alpha → ℝ≥0∞} (hf : Measurable f)
    (x : alpha) :
    minimalResolvent R emb lam (minimalResolvent R emb mu f) x =
      ⨆ n, localResolvent R emb n lam (localResolvent R emb n mu f) x := by
  have hgmeas : ∀ k, Measurable (localResolvent R emb k mu f) := fun k ↦
    measurable_localResolvent R emb (hemb k) mu hf
  have hgmono : Monotone fun k ↦ localResolvent R emb k mu f :=
    fun a b hab y ↦ hmono mu hmu hf y hab
  have hrepr : minimalResolvent R emb mu f =
      fun y ↦ ⨆ k, localResolvent R emb k mu f y := rfl
  have hstep : ∀ m, localResolvent R emb m lam
      (fun y ↦ ⨆ k, localResolvent R emb k mu f y) x =
      ⨆ k, localResolvent R emb m lam (localResolvent R emb k mu f) x :=
    fun m ↦ localResolvent_iSup R emb (hemb m) lam hgmeas hgmono x
  rw [minimalResolvent, hrepr]
  simp_rw [hstep]
  refine le_antisymm (iSup_le fun m ↦ iSup_le fun k ↦ ?_) (iSup_le fun n ↦ ?_)
  · refine le_iSup_of_le (max m k) ?_
    calc localResolvent R emb m lam (localResolvent R emb k mu f) x
        ≤ localResolvent R emb (max m k) lam (localResolvent R emb k mu f) x :=
          hmono lam hlam (hgmeas k) x (le_max_left m k)
      _ ≤ localResolvent R emb (max m k) lam
            (localResolvent R emb (max m k) mu f) x :=
          localResolvent_mono_of_le R emb (hemb (max m k)).injective lam
            (hgmono (le_max_right m k)) x
  · exact le_iSup_of_le n (le_iSup_of_le n le_rfl)

/-- **The resolvent equation for the supremum of the transported resolvents.**  Each member
satisfies the resolvent equation, and both sides pass to the supremum by monotone convergence.
The only property of the family used is that the transported resolvents are monotone in `m` at
every positive shift. -/
theorem minimalResolvent_resolventEquation_of_monotone
    (hemb : ∀ m, MeasurableEmbedding (emb m))
    (hmono : ∀ nu > 0, ∀ {g : alpha → ℝ≥0∞}, Measurable g → ∀ y,
      Monotone fun m ↦ localResolvent R emb m nu g y)
    {lam mu : ℝ} (hlam : 0 < lam) (hlt : lam < mu) {f : alpha → ℝ≥0∞} (hf : Measurable f)
    (x : alpha) :
    minimalResolvent R emb lam f x =
      minimalResolvent R emb mu f x +
        ENNReal.ofReal (mu - lam) *
          minimalResolvent R emb lam (minimalResolvent R emb mu f) x := by
  have hmu : 0 < mu := hlam.trans hlt
  have hgmeas : ∀ k, Measurable (localResolvent R emb k mu f) := fun k ↦
    measurable_localResolvent R emb (hemb k) mu hf
  have hgmono : Monotone fun k ↦ localResolvent R emb k mu f :=
    fun a b hab y ↦ hmono mu hmu hf y hab
  have hamono : Monotone fun n ↦ localResolvent R emb n mu f x := hmono mu hmu hf x
  have hbmono : Monotone fun n ↦
      localResolvent R emb n lam (localResolvent R emb n mu f) x := by
    refine monotone_nat_of_le_succ fun n ↦ ?_
    refine le_trans (hmono lam hlam (hgmeas n) x (Nat.le_succ n)) ?_
    exact localResolvent_mono_of_le R emb (hemb (n + 1)).injective lam
      (hgmono (Nat.le_succ n)) x
  have hcmono : Monotone fun n ↦
      ENNReal.ofReal (mu - lam) *
        localResolvent R emb n lam (localResolvent R emb n mu f) x :=
    fun i j hij ↦ mul_le_mul' le_rfl (hbmono hij)
  calc minimalResolvent R emb lam f x = ⨆ n, localResolvent R emb n lam f x := rfl
    _ = ⨆ n, (localResolvent R emb n mu f x +
          ENNReal.ofReal (mu - lam) *
            localResolvent R emb n lam (localResolvent R emb n mu f) x) :=
        iSup_congr fun n ↦
          localResolvent_resolventEquation R emb (hemb n) hlt hf x
    _ = (⨆ n, localResolvent R emb n mu f x) +
          ⨆ n, ENNReal.ofReal (mu - lam) *
            localResolvent R emb n lam (localResolvent R emb n mu f) x :=
        (ENNReal.iSup_add_iSup_of_monotone hamono hcmono).symm
    _ = minimalResolvent R emb mu f x +
          ENNReal.ofReal (mu - lam) *
            minimalResolvent R emb lam (minimalResolvent R emb mu f) x := by
        rw [minimalResolvent_comp_eq_iSup R emb hemb hmono hlam hmu hf x,
          ENNReal.mul_iSup, minimalResolvent]

/-- **The minimal resolvent satisfies the resolvent equation.**  The part-process identity is
consumed only through the monotonicity of the transported resolvents. -/
theorem minimalResolvent_resolventEquation (hemb : ∀ m, MeasurableEmbedding (emb m))
    (hiota : ∀ m, IsOpenEmbedding (iota m))
    (hcomm : ∀ m (y : X m), emb (m + 1) (iota m y) = emb m y)
    (hreg : ∀ m, (R m).OnePointRegular)
    (hcompat : ∀ m, PositiveC0ContractiveResolvent.IsPartProcess (R m) (R (m + 1))
      (hreg (m + 1)) (hiota m))
    {lam mu : ℝ} (hlam : 0 < lam) (hlt : lam < mu) {f : alpha → ℝ≥0∞} (hf : Measurable f)
    (x : alpha) :
    minimalResolvent R emb lam f x =
      minimalResolvent R emb mu f x +
        ENNReal.ofReal (mu - lam) *
          minimalResolvent R emb lam (minimalResolvent R emb mu f) x :=
  minimalResolvent_resolventEquation_of_monotone R emb hemb
    (fun _nu hnu {_g} hg y ↦
      monotone_localResolvent R emb iota hemb hiota hcomm hreg hcompat hnu hg y)
    hlam hlt hf x

end ResolventEquation

end MarkovProcess

end

end PortComputability
