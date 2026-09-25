/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.ClassEquivalence.Constructor
public import LeanPool.CaffarelliKohnNirenberg.Statements.SuitableWeakSolution
public import LeanPool.CaffarelliKohnNirenberg.Main.TheoremA
public import LeanPool.CaffarelliKohnNirenberg.Main.TheoremB
public import LeanPool.CaffarelliKohnNirenberg.Main.TheoremC

/-!
# The three main theorems under the manuscript's hypothesis

Definition `def:sws` of the manuscript asks four things of a suitable weak
solution: the regularity class (S1), the divergence-free identity (S2), the
weak momentum identity (S3) and the local energy inequality (S4).  It attaches
no integrability side condition to (S2), (S3) or (S4); the integrals appearing
there are simply asserted to vanish, or to satisfy an inequality.
`CKN.IsSuitableWeakSolution` of `CKN/Statements/SuitableWeakSolution.lean`
transcribes that definition literally, and it is the hypothesis of the
statements of Theorems A, B and C.

The Lean class `CKN.IsSuitableWeakSolutionIntegrable` states the same four conditions but
carries, inside its (S2), (S3) and (S4) clauses, four `IntegrableOn`
conjuncts - one for the divergence-free integrand, one for the momentum
integrand, and one for each side of the local energy inequality.  They were
recorded there because the Bochner integral of a non-integrable function is `0`
by convention: an identity `∫ ... = 0` read off a non-integrable integrand is
true for the wrong reason, and a class that allowed that would be weaker than
the manuscript's.

Those four conjuncts are not extra assumptions.  The files
`CKN/ClassEquivalence/*.lean` derive each of them from the (S1) clauses alone,
and `CKN.isSuitableWeakSolutionIntegrable_iff_identities` assembles that derivation into
an equivalence.  So the class with the side conditions and the class without
them have exactly the same inhabitants; `CKN.isSuitableWeakSolution_iff_integrable`
records the identification.

The three theorems that follow are Theorem A, Theorem B and Theorem C under the
manuscript's hypothesis.  Each is the corresponding implementation export of
`CKN/Main/TheoremA.lean`, `CKN/Main/TheoremB.lean` and `CKN/Main/TheoremC.lean`,
whose hypothesis is `CKN.IsSuitableWeakSolutionIntegrable`, composed with the equivalence;
the conclusions are copied unchanged.  `CKN/Main/TheoremAPaper.lean`,
`CKN/Main/TheoremBPaper.lean` and `CKN/Main/TheoremCPaper.lean` re-export them,
and the statements are short assemblies of those re-exports.

Both forms of the class therefore exist, and both are wanted.  The development
proves its intermediate results with `CKN.IsSuitableWeakSolutionIntegrable`, which keeps
the integrability of each tested integrand visible at the point of use.  The
statements assume `CKN.IsSuitableWeakSolution`: exactly what
`def:sws` assumes, and nothing more.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic


noncomputable section

namespace CKN

variable {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
variable {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
variable {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}

/-- The manuscript's suitable weak-solution class and the class carrying the
integrability side conditions have the same inhabitants.  Read from left to
right this is the content of `CKN/ClassEquivalence`: the four `IntegrableOn`
conjuncts of `CKN.IsSuitableWeakSolutionIntegrable` follow from the (S1) clauses, so
assuming them assumes nothing beyond `def:sws`.  Read from right to left it is
the projection that discards them.

The two classes group their clauses differently - `CKN.IsSuitableWeakSolutionIntegrable`
and `CKN.IsSuitableWeakSolution` both write the (S1) clauses inline, while
`CKN.isSuitableWeakSolutionIntegrable_iff_identities` collects them into
`CKN.IsSuitableWeakSolutionData` - so each direction re-associates the
conjunction before handing it on.  No identity is read at a junk value of the
Bochner integral: the left-to-right direction goes through
`CKN.isSuitableWeakSolutionIntegrable_of_identities`, which establishes the four
integrability clauses from the (S1) clauses before consuming any identity. -/
theorem isSuitableWeakSolution_iff_integrable :
    IsSuitableWeakSolution Ω I q u Du p f ↔
      IsSuitableWeakSolutionIntegrable Ω I q u Du p f :=
  ⟨fun h =>
      isSuitableWeakSolutionIntegrable_of_identities
        ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1⟩
        h.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2.2,
    fun h =>
      ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1,
        fun ψ hψ => (h.2.2.2.2.2.2.1 ψ hψ).2,
        fun φ hφ => (h.2.2.2.2.2.2.2.1 φ hφ).2,
        fun ψ hψ hnn => (h.2.2.2.2.2.2.2.2 ψ hψ hnn).2.2⟩⟩

/-- Theorem A of the manuscript, paper label `thm:A`, under the manuscript's
definition of a suitable weak solution.  The conclusion is that of
`CKN.epsilonRegularityL3`, unchanged; the hypothesis class of the implementation
export `CKN.Main.epsilonRegularityL3` differs, and by
`CKN.isSuitableWeakSolution_iff_integrable` the two classes coincide. -/
theorem epsilonRegularityL3_paper (q : ℝ) (hq : 5 / 2 < q) :
    ∃ ε₀ γ₀ C₄ : ℝ, 0 < ε₀ ∧ 0 < γ₀ ∧ γ₀ ≤ 2 / 3 ∧ 0 ≤ C₄ ∧
      ∀ (Ω : Set Vec3) (I : Set ℝ) (u : ParabolicPoint → Vec3)
        (Du : ParabolicPoint → Fin 3 → Vec3)
        (p : ParabolicPoint → ℝ) (f : ParabolicPoint → Vec3),
        IsSuitableWeakSolution Ω I q u Du p f →
        closure (parabolicCylinder 0 0 1) ⊆ spaceTimeSet Ω I →
        (∫⁻ z in parabolicCylinder 0 0 1,
          ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (3 : ℝ) +
            ENNReal.ofReal |p z| ^ (3 / 2 : ℝ) +
            ENNReal.ofReal (vec3EuclideanNorm (f z)) ^ q) ≤ ENNReal.ofReal ε₀ →
        ∃ w : ParabolicPoint → Vec3,
          w =ᵐ[volume.restrict (parabolicCylinder 0 0 (1 / 2))] u ∧
          ParabolicHolderVecNormLE (closure (parabolicCylinder 0 0 (1 / 2)))
            w γ₀ C₄ ∧
          ∀ z ∈ vec3Ball 0 (1 / 2) ×ˢ Ioo (-(1 / 4 : ℝ)) 0,
            IsRegularPoint Ω I u z := by
  obtain ⟨ε₀, γ₀, C₄, hε₀, hγ₀, hγ₀le, hC₄, hmain⟩ := CKN.Main.epsilonRegularityL3 q hq
  exact ⟨ε₀, γ₀, C₄, hε₀, hγ₀, hγ₀le, hC₄, fun Ω I u Du p f hsol =>
    hmain Ω I u Du p f (isSuitableWeakSolution_iff_integrable.mp hsol)⟩

/-- Theorem B of the manuscript, paper label `thm:B`, under the manuscript's
definition of a suitable weak solution.  The conclusion is that of
`CKN.epsilonRegularityGradient`, unchanged; the hypothesis class of the
implementation export `CKN.Main.epsilonRegularityGradient` differs, and by
`CKN.isSuitableWeakSolution_iff_integrable` the two classes coincide. -/
theorem epsilonRegularityGradient_paper (q : ℝ) (hq : 5 / 2 < q) :
    ∃ ε₁ : ℝ, 0 < ε₁ ∧
      ∀ (Ω : Set Vec3) (I : Set ℝ) (u : ParabolicPoint → Vec3)
        (Du : ParabolicPoint → Fin 3 → Vec3)
        (p : ParabolicPoint → ℝ) (f : ParabolicPoint → Vec3),
        (hsol : IsSuitableWeakSolution Ω I q u Du p f) →
        ∀ z₀ ∈ spaceTimeSet Ω I,
          Filter.limsup (fun r : ℝ =>
              (ENNReal.ofReal r)⁻¹ *
                ∫⁻ w in parabolicCylinder z₀.1 z₀.2 r,
                  ENNReal.ofReal (spatialGradientSq u Du w))
            (𝓝[>] (0 : ℝ)) < ENNReal.ofReal (ε₁ ^ (2 : ℕ)) →
          IsRegularPoint Ω I u z₀ := by
  obtain ⟨ε₁, hε₁, hmain⟩ := CKN.Main.epsilonRegularityGradient q hq
  exact ⟨ε₁, hε₁, fun Ω I u Du p f hsol =>
    hmain Ω I u Du p f (isSuitableWeakSolution_iff_integrable.mp hsol)⟩

/-- Theorem C of the manuscript, paper label `thm:C`, under the manuscript's
definition of a suitable weak solution.  The conclusion is that of
`CKN.caffarelliKohnNirenberg`, unchanged; the hypothesis class of the
implementation export `CKN.Main.caffarelliKohnNirenberg` differs, and by
`CKN.isSuitableWeakSolution_iff_integrable` the two classes coincide. -/
theorem caffarelliKohnNirenberg_paper (q : ℝ) (hq : 5 / 2 < q) :
    ∀ (Ω : Set Vec3) (I : Set ℝ) (u : ParabolicPoint → Vec3)
      (Du : ParabolicPoint → Fin 3 → Vec3)
      (p : ParabolicPoint → ℝ) (f : ParabolicPoint → Vec3),
      IsSuitableWeakSolution Ω I q u Du p f →
      parabolicHausdorffMeasure 1 (SingularSet Ω I u) = 0 :=
  fun Ω I u Du p f hsol =>
    CKN.Main.caffarelliKohnNirenberg q hq Ω I u Du p f
      (isSuitableWeakSolution_iff_integrable.mp hsol)

end CKN
