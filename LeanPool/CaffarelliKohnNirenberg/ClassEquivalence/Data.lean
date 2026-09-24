/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Statements.SuitableWeakSolutionIntegrable

/-!
# The data part of a suitable weak solution

`CKN.IsSuitableWeakSolutionIntegrable` from paper label `def:sws` is a conjunction of two
very different kinds of clauses.  The first six record that the fields are
measurable and have the stated local integrability; the last three record the
divergence-free identity, the weak momentum identity and the local energy
inequality, each of them paired with an integrability side condition on the
integrand it tests.

This file names the first six clauses `CKN.IsSuitableWeakSolutionData`.  The
body below is a character-for-character copy of the corresponding part of the
definition, so `CKN.IsSuitableWeakSolutionIntegrable.toData` is a plain projection
of the anonymous constructor and needs no tactic; that is the proof that the
predicate defined here is exactly those six clauses and nothing more.

Everything downstream that only needs measurability and local integrability
should take `IsSuitableWeakSolutionData` rather than the full class.  A lemma
stated that way can be used while the identity clauses of the class are still
being established, which a lemma stated with the full class cannot.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic


noncomputable section

namespace CKN

/-- The measurability and local-integrability clauses of `def:sws`: the first
six conjuncts of `CKN.IsSuitableWeakSolutionIntegrable`, copied verbatim. -/
def IsSuitableWeakSolutionData (Ω : Set Vec3) (I : Set ℝ) (q : ℝ)
    (u : ParabolicPoint → Vec3) (Du : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ) (f : ParabolicPoint → Vec3) : Prop :=
  IsOpen Ω ∧ IsOpen I ∧ OrdConnected I ∧ 5 / 2 < q ∧
    (∀ Ω' J, localBox Ω I Ω' J → localVecLp (spaceTimeSet Ω' J) q f) ∧
    (∀ Ω' J, localBox Ω I Ω' J →
      AEStronglyMeasurable u (volume.restrict (spaceTimeSet Ω' J)) ∧
      AEStronglyMeasurable Du (volume.restrict (spaceTimeSet Ω' J)) ∧
      AEStronglyMeasurable p (volume.restrict (spaceTimeSet Ω' J)) ∧
      AEStronglyMeasurable f (volume.restrict (spaceTimeSet Ω' J)) ∧
      essSup (fun s => ∫⁻ x in Ω', ‖u (x, s)‖ₑ ^ (2 : ℝ))
          (volume.restrict J) < ⊤ ∧
      (∫⁻ z in spaceTimeSet Ω' J,
          ‖u z‖ₑ ^ (2 : ℝ) + ‖Du z‖ₑ ^ (2 : ℝ)) < ⊤ ∧
      MemLp p (ENNReal.ofReal (3 / 2 : ℝ))
          (volume.restrict (spaceTimeSet Ω' J)) ∧
      MemLp f (ENNReal.ofReal q)
          (volume.restrict (spaceTimeSet Ω' J)) ∧
      ∀ i : Fin 3, ∀ᵐ s ∂volume.restrict J,
        HasWeakGradientOn Ω' (fun x => u (x, s) i) (fun x => Du (x, s) i))

variable {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
variable {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
variable {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}

/-- A suitable weak solution carries the data clauses of `def:sws`.  The proof
is the projection of the first six components, with no tactic: this is what
certifies that `IsSuitableWeakSolutionData` is the data part of the class. -/
theorem IsSuitableWeakSolutionIntegrable.toData
    (h : IsSuitableWeakSolutionIntegrable Ω I q u Du p f) :
    IsSuitableWeakSolutionData Ω I q u Du p f :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1⟩

namespace IsSuitableWeakSolutionData

variable (h : IsSuitableWeakSolutionData Ω I q u Du p f)
include h

/-- The spatial carrier is open. -/
theorem isOpen_space : IsOpen Ω := h.1

/-- The time carrier is open. -/
theorem isOpen_time : IsOpen I := h.2.1

/-- The time carrier is order connected, hence an interval. -/
theorem ordConnected_time : OrdConnected I := h.2.2.1

/-- The force exponent exceeds `5 / 2`. -/
theorem five_halves_lt_exponent : 5 / 2 < q := h.2.2.2.1

/-- The force is componentwise `L^q` on every local box. -/
theorem force_localVecLp {Ω' : Set Vec3} {J : Set ℝ} (hbox : localBox Ω I Ω' J) :
    localVecLp (spaceTimeSet Ω' J) q f := h.2.2.2.2.1 Ω' J hbox

/-- The velocity is measurable on every local box. -/
theorem aestronglyMeasurable_velocity {Ω' : Set Vec3} {J : Set ℝ}
    (hbox : localBox Ω I Ω' J) :
    AEStronglyMeasurable u (volume.restrict (spaceTimeSet Ω' J)) :=
  (h.2.2.2.2.2 Ω' J hbox).1

/-- The velocity gradient is measurable on every local box. -/
theorem aestronglyMeasurable_gradient {Ω' : Set Vec3} {J : Set ℝ}
    (hbox : localBox Ω I Ω' J) :
    AEStronglyMeasurable Du (volume.restrict (spaceTimeSet Ω' J)) :=
  (h.2.2.2.2.2 Ω' J hbox).2.1

/-- The pressure is measurable on every local box. -/
theorem aestronglyMeasurable_pressure {Ω' : Set Vec3} {J : Set ℝ}
    (hbox : localBox Ω I Ω' J) :
    AEStronglyMeasurable p (volume.restrict (spaceTimeSet Ω' J)) :=
  (h.2.2.2.2.2 Ω' J hbox).2.2.1

/-- The force is measurable on every local box. -/
theorem aestronglyMeasurable_force {Ω' : Set Vec3} {J : Set ℝ}
    (hbox : localBox Ω I Ω' J) :
    AEStronglyMeasurable f (volume.restrict (spaceTimeSet Ω' J)) :=
  (h.2.2.2.2.2 Ω' J hbox).2.2.2.1

/-- The spatial slice energies of the velocity are essentially bounded in time
on every local box. -/
theorem essSup_sliceEnergy_lt_top {Ω' : Set Vec3} {J : Set ℝ}
    (hbox : localBox Ω I Ω' J) :
    essSup (fun s => ∫⁻ x in Ω', ‖u (x, s)‖ₑ ^ (2 : ℝ)) (volume.restrict J) < ⊤ :=
  (h.2.2.2.2.2 Ω' J hbox).2.2.2.2.1

/-- The velocity and its gradient have finite joint energy on every local box. -/
theorem energy_lintegral_lt_top {Ω' : Set Vec3} {J : Set ℝ}
    (hbox : localBox Ω I Ω' J) :
    (∫⁻ z in spaceTimeSet Ω' J, ‖u z‖ₑ ^ (2 : ℝ) + ‖Du z‖ₑ ^ (2 : ℝ)) < ⊤ :=
  (h.2.2.2.2.2 Ω' J hbox).2.2.2.2.2.1

/-- The pressure is `L^{3/2}` on every local box. -/
theorem memLp_pressure {Ω' : Set Vec3} {J : Set ℝ} (hbox : localBox Ω I Ω' J) :
    MemLp p (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict (spaceTimeSet Ω' J)) :=
  (h.2.2.2.2.2 Ω' J hbox).2.2.2.2.2.2.1

/-- The force is `L^q` on every local box. -/
theorem memLp_force {Ω' : Set Vec3} {J : Set ℝ} (hbox : localBox Ω I Ω' J) :
    MemLp f (ENNReal.ofReal q) (volume.restrict (spaceTimeSet Ω' J)) :=
  (h.2.2.2.2.2 Ω' J hbox).2.2.2.2.2.2.2.1

/-- For almost every time, the spatial slice of the velocity has the
corresponding slice of `Du` as its weak gradient on the box. -/
theorem hasWeakGradientOn_slice {Ω' : Set Vec3} {J : Set ℝ}
    (hbox : localBox Ω I Ω' J) (i : Fin 3) :
    ∀ᵐ s ∂volume.restrict J,
      HasWeakGradientOn Ω' (fun x => u (x, s) i) (fun x => Du (x, s) i) :=
  (h.2.2.2.2.2 Ω' J hbox).2.2.2.2.2.2.2.2 i

end IsSuitableWeakSolutionData

end CKN
