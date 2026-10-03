/-
Copyright (c) 2026 Dawid Trela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dawid Trela
-/
module

public import LeanPool.MovingSofa.GerverSofa.KernelOnly.Core.Bundle005
/-!
# Gerver sofa: related certificate and semantic modules

* `GerverSofa.KernelOnly.PartE.Certificates.Batch009`.
* `GerverSofa.KernelOnly.PartE.Certificates.Batch024`.
-/

public section

noncomputable section

namespace GerverSofa.PartE.CertificateCellsb518b98fbe

/-- Subcell `0110` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0110 : AngleCell :=
  childLL (childLH (childLH (childLL e24ThetaAboveRoot)))

/-- Subcell `0111` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0111 : AngleCell :=
  childLH (childLH (childLH (childLL e24ThetaAboveRoot)))

/-- Subcell `01103210` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01103210 : AngleCell :=
  childLL (childLH (childHL (childHH thetaAboveCell0110)))

/-- Subcell `01103211` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01103211 : AngleCell :=
  childLH (childLH (childHL (childHH thetaAboveCell0110)))

/-- Subcell `01103212` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01103212 : AngleCell :=
  childHL (childLH (childHL (childHH thetaAboveCell0110)))

/-- Subcell `01103213` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01103213 : AngleCell :=
  childHH (childLH (childHL (childHH thetaAboveCell0110)))

/-- Subcell `01103220` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01103220 : AngleCell :=
  childLL (childHL (childHL (childHH thetaAboveCell0110)))

/-- Subcell `01103221` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01103221 : AngleCell :=
  childLH (childHL (childHL (childHH thetaAboveCell0110)))

/-- Subcell `01103222` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01103222 : AngleCell :=
  childHL (childHL (childHL (childHH thetaAboveCell0110)))

/-- Subcell `01103223` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01103223 : AngleCell :=
  childHH (childHL (childHL (childHH thetaAboveCell0110)))

/-- Subcell `01103230` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01103230 : AngleCell :=
  childLL (childHH (childHL (childHH thetaAboveCell0110)))

/-- Subcell `01103231` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01103231 : AngleCell :=
  childLH (childHH (childHL (childHH thetaAboveCell0110)))

/-- Subcell `01103232` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01103232 : AngleCell :=
  childHL (childHH (childHL (childHH thetaAboveCell0110)))

/-- Subcell `01103233` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01103233 : AngleCell :=
  childHH (childHH (childHL (childHH thetaAboveCell0110)))

/-- Subcell `01103300` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01103300 : AngleCell :=
  childLL (childLL (childHH (childHH thetaAboveCell0110)))

/-- Subcell `01103301` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01103301 : AngleCell :=
  childLH (childLL (childHH (childHH thetaAboveCell0110)))

/-- Subcell `01103302` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01103302 : AngleCell :=
  childHL (childLL (childHH (childHH thetaAboveCell0110)))

/-- Subcell `01103303` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01103303 : AngleCell :=
  childHH (childLL (childHH (childHH thetaAboveCell0110)))

/-- Subcell `01103310` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01103310 : AngleCell :=
  childLL (childLH (childHH (childHH thetaAboveCell0110)))

/-- Subcell `01103311` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01103311 : AngleCell :=
  childLH (childLH (childHH (childHH thetaAboveCell0110)))

/-- Subcell `01103312` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01103312 : AngleCell :=
  childHL (childLH (childHH (childHH thetaAboveCell0110)))

/-- Subcell `01103313` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01103313 : AngleCell :=
  childHH (childLH (childHH (childHH thetaAboveCell0110)))

/-- Subcell `01103320` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01103320 : AngleCell :=
  childLL (childHL (childHH (childHH thetaAboveCell0110)))

/-- Subcell `01103321` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01103321 : AngleCell :=
  childLH (childHL (childHH (childHH thetaAboveCell0110)))

/-- Subcell `01103322` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01103322 : AngleCell :=
  childHL (childHL (childHH (childHH thetaAboveCell0110)))

/-- Subcell `01103323` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01103323 : AngleCell :=
  childHH (childHL (childHH (childHH thetaAboveCell0110)))

/-- Subcell `01103330` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01103330 : AngleCell :=
  childLL (childHH (childHH (childHH thetaAboveCell0110)))

/-- Subcell `01103331` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01103331 : AngleCell :=
  childLH (childHH (childHH (childHH thetaAboveCell0110)))

/-- Subcell `01103332` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01103332 : AngleCell :=
  childHL (childHH (childHH (childHH thetaAboveCell0110)))

/-- Subcell `01103333` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01103333 : AngleCell :=
  childHH (childHH (childHH (childHH thetaAboveCell0110)))

/-- Subcell `01112020` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01112020 : AngleCell :=
  childLL (childHL (childLL (childHL thetaAboveCell0111)))

/-- Subcell `01112021` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01112021 : AngleCell :=
  childLH (childHL (childLL (childHL thetaAboveCell0111)))

/-- Subcell `01112022` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01112022 : AngleCell :=
  childHL (childHL (childLL (childHL thetaAboveCell0111)))

/-- Subcell `01112023` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01112023 : AngleCell :=
  childHH (childHL (childLL (childHL thetaAboveCell0111)))

/-- Subcell `01112030` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01112030 : AngleCell :=
  childLL (childHH (childLL (childHL thetaAboveCell0111)))

/-- Subcell `01112031` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01112031 : AngleCell :=
  childLH (childHH (childLL (childHL thetaAboveCell0111)))

/-- Subcell `01112032` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01112032 : AngleCell :=
  childHL (childHH (childLL (childHL thetaAboveCell0111)))

/-- Subcell `01112033` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01112033 : AngleCell :=
  childHH (childHH (childLL (childHL thetaAboveCell0111)))

/-- Subcell `01112120` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01112120 : AngleCell :=
  childLL (childHL (childLH (childHL thetaAboveCell0111)))

/-- Subcell `01112121` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01112121 : AngleCell :=
  childLH (childHL (childLH (childHL thetaAboveCell0111)))

/-- Subcell `01112122` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01112122 : AngleCell :=
  childHL (childHL (childLH (childHL thetaAboveCell0111)))

/-- Subcell `01112123` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01112123 : AngleCell :=
  childHH (childHL (childLH (childHL thetaAboveCell0111)))

/-- Subcell `01112130` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01112130 : AngleCell :=
  childLL (childHH (childLH (childHL thetaAboveCell0111)))

/-- Subcell `01112131` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01112131 : AngleCell :=
  childLH (childHH (childLH (childHL thetaAboveCell0111)))

/-- Subcell `01112132` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01112132 : AngleCell :=
  childHL (childHH (childLH (childHL thetaAboveCell0111)))

/-- Subcell `01112133` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01112133 : AngleCell :=
  childHH (childHH (childLH (childHL thetaAboveCell0111)))

/-- Subcell `01112200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01112200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0111)))

/-- Subcell `01112201` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01112201 : AngleCell :=
  childLH (childLL (childHL (childHL thetaAboveCell0111)))

/-- Subcell `01112202` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01112202 : AngleCell :=
  childHL (childLL (childHL (childHL thetaAboveCell0111)))

/-- Subcell `01112203` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01112203 : AngleCell :=
  childHH (childLL (childHL (childHL thetaAboveCell0111)))

/-- Subcell `01112210` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01112210 : AngleCell :=
  childLL (childLH (childHL (childHL thetaAboveCell0111)))

/-- Subcell `01112211` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01112211 : AngleCell :=
  childLH (childLH (childHL (childHL thetaAboveCell0111)))

/-- Subcell `01112212` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01112212 : AngleCell :=
  childHL (childLH (childHL (childHL thetaAboveCell0111)))

/-- Subcell `01112213` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01112213 : AngleCell :=
  childHH (childLH (childHL (childHL thetaAboveCell0111)))

/-- Subcell `01112220` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01112220 : AngleCell :=
  childLL (childHL (childHL (childHL thetaAboveCell0111)))

/-- Subcell `01112221` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01112221 : AngleCell :=
  childLH (childHL (childHL (childHL thetaAboveCell0111)))

/-- Subcell `01112222` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01112222 : AngleCell :=
  childHL (childHL (childHL (childHL thetaAboveCell0111)))

/-- Subcell `01112223` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01112223 : AngleCell :=
  childHH (childHL (childHL (childHL thetaAboveCell0111)))

/-- Subcell `01112230` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01112230 : AngleCell :=
  childLL (childHH (childHL (childHL thetaAboveCell0111)))

/-- Subcell `01112231` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01112231 : AngleCell :=
  childLH (childHH (childHL (childHL thetaAboveCell0111)))

/-- Subcell `01112232` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01112232 : AngleCell :=
  childHL (childHH (childHL (childHL thetaAboveCell0111)))

/-- Subcell `01112233` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01112233 : AngleCell :=
  childHH (childHH (childHL (childHL thetaAboveCell0111)))

/-- Subcell `01112300` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01112300 : AngleCell :=
  childLL (childLL (childHH (childHL thetaAboveCell0111)))

/-- Subcell `01112301` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01112301 : AngleCell :=
  childLH (childLL (childHH (childHL thetaAboveCell0111)))

/-- Subcell `01112302` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01112302 : AngleCell :=
  childHL (childLL (childHH (childHL thetaAboveCell0111)))

/-- Subcell `01112303` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01112303 : AngleCell :=
  childHH (childLL (childHH (childHL thetaAboveCell0111)))

/-- Subcell `01112310` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01112310 : AngleCell :=
  childLL (childLH (childHH (childHL thetaAboveCell0111)))

/-- Subcell `01112311` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01112311 : AngleCell :=
  childLH (childLH (childHH (childHL thetaAboveCell0111)))

/-- Subcell `01112312` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01112312 : AngleCell :=
  childHL (childLH (childHH (childHL thetaAboveCell0111)))

/-- Subcell `01112313` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01112313 : AngleCell :=
  childHH (childLH (childHH (childHL thetaAboveCell0111)))

/-- Subcell `01112320` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01112320 : AngleCell :=
  childLL (childHL (childHH (childHL thetaAboveCell0111)))

/-- Subcell `01112321` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01112321 : AngleCell :=
  childLH (childHL (childHH (childHL thetaAboveCell0111)))

/-- Subcell `01112322` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01112322 : AngleCell :=
  childHL (childHL (childHH (childHL thetaAboveCell0111)))

/-- Subcell `01112323` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01112323 : AngleCell :=
  childHH (childHL (childHH (childHL thetaAboveCell0111)))

/-- Subcell `01112330` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01112330 : AngleCell :=
  childLL (childHH (childHH (childHL thetaAboveCell0111)))

/-- Subcell `01112331` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01112331 : AngleCell :=
  childLH (childHH (childHH (childHL thetaAboveCell0111)))

/-- Subcell `01112332` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01112332 : AngleCell :=
  childHL (childHH (childHH (childHL thetaAboveCell0111)))

/-- Subcell `01112333` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01112333 : AngleCell :=
  childHH (childHH (childHH (childHL thetaAboveCell0111)))

/-- Subcell `01113020` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01113020 : AngleCell :=
  childLL (childHL (childLL (childHH thetaAboveCell0111)))

/-- Subcell `01113021` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01113021 : AngleCell :=
  childLH (childHL (childLL (childHH thetaAboveCell0111)))

/-- Subcell `01113022` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01113022 : AngleCell :=
  childHL (childHL (childLL (childHH thetaAboveCell0111)))

/-- Subcell `01113023` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01113023 : AngleCell :=
  childHH (childHL (childLL (childHH thetaAboveCell0111)))

/-- Subcell `01113030` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01113030 : AngleCell :=
  childLL (childHH (childLL (childHH thetaAboveCell0111)))

/-- Subcell `01113031` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01113031 : AngleCell :=
  childLH (childHH (childLL (childHH thetaAboveCell0111)))

/-- Subcell `01113032` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01113032 : AngleCell :=
  childHL (childHH (childLL (childHH thetaAboveCell0111)))

/-- Subcell `01113033` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01113033 : AngleCell :=
  childHH (childHH (childLL (childHH thetaAboveCell0111)))

/-- Subcell `01113120` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01113120 : AngleCell :=
  childLL (childHL (childLH (childHH thetaAboveCell0111)))

/-- Subcell `01113121` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01113121 : AngleCell :=
  childLH (childHL (childLH (childHH thetaAboveCell0111)))

/-- Subcell `01113122` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01113122 : AngleCell :=
  childHL (childHL (childLH (childHH thetaAboveCell0111)))

/-- Subcell `01113123` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01113123 : AngleCell :=
  childHH (childHL (childLH (childHH thetaAboveCell0111)))

/-- Subcell `01113130` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01113130 : AngleCell :=
  childLL (childHH (childLH (childHH thetaAboveCell0111)))

/-- Subcell `01113131` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01113131 : AngleCell :=
  childLH (childHH (childLH (childHH thetaAboveCell0111)))

/-- Subcell `01113132` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01113132 : AngleCell :=
  childHL (childHH (childLH (childHH thetaAboveCell0111)))

/-- Subcell `01113133` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01113133 : AngleCell :=
  childHH (childHH (childLH (childHH thetaAboveCell0111)))

/-- Subcell `01113200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01113200 : AngleCell :=
  childLL (childLL (childHL (childHH thetaAboveCell0111)))

/-- Subcell `01113201` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01113201 : AngleCell :=
  childLH (childLL (childHL (childHH thetaAboveCell0111)))

/-- Subcell `01113202` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01113202 : AngleCell :=
  childHL (childLL (childHL (childHH thetaAboveCell0111)))

end GerverSofa.PartE.CertificateCellsb518b98fbe

namespace GerverSofa.PartE.CertificateCells37514173c1

/-- Subcell `0011` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0011 : AngleCell :=
  childLH (childLH (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `0100` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0100 : AngleCell :=
  childLL (childLL (childLH (childLL e24ThetaAboveRoot)))

/-- Subcell `1110` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1110 : AngleCell :=
  childLL (childLH (childLH (childLH e24ThetaBelowRoot)))

/-- Subcell `1111` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111 : AngleCell :=
  childLH (childLH (childLH (childLH e24ThetaBelowRoot)))

/-- Subcell `00113310` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00113310 : AngleCell :=
  childLL (childLH (childHH (childHH thetaAboveCell0011)))

/-- Subcell `00113311` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00113311 : AngleCell :=
  childLH (childLH (childHH (childHH thetaAboveCell0011)))

/-- Subcell `00113312` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00113312 : AngleCell :=
  childHL (childLH (childHH (childHH thetaAboveCell0011)))

/-- Subcell `00113313` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00113313 : AngleCell :=
  childHH (childLH (childHH (childHH thetaAboveCell0011)))

/-- Subcell `01002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0100)))

/-- Subcell `01002201` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01002201 : AngleCell :=
  childLH (childLL (childHL (childHL thetaAboveCell0100)))

/-- Subcell `01002202` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01002202 : AngleCell :=
  childHL (childLL (childHL (childHL thetaAboveCell0100)))

/-- Subcell `01002203` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01002203 : AngleCell :=
  childHH (childLL (childHL (childHL thetaAboveCell0100)))

/-- Subcell `01002210` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01002210 : AngleCell :=
  childLL (childLH (childHL (childHL thetaAboveCell0100)))

/-- Subcell `01002211` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01002211 : AngleCell :=
  childLH (childLH (childHL (childHL thetaAboveCell0100)))

/-- Subcell `01002212` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01002212 : AngleCell :=
  childHL (childLH (childHL (childHL thetaAboveCell0100)))

/-- Subcell `01002213` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01002213 : AngleCell :=
  childHH (childLH (childHL (childHL thetaAboveCell0100)))

/-- Subcell `01002300` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01002300 : AngleCell :=
  childLL (childLL (childHH (childHL thetaAboveCell0100)))

/-- Subcell `01002301` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01002301 : AngleCell :=
  childLH (childLL (childHH (childHL thetaAboveCell0100)))

/-- Subcell `01002302` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01002302 : AngleCell :=
  childHL (childLL (childHH (childHL thetaAboveCell0100)))

/-- Subcell `01002303` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01002303 : AngleCell :=
  childHH (childLL (childHH (childHL thetaAboveCell0100)))

/-- Subcell `01002310` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01002310 : AngleCell :=
  childLL (childLH (childHH (childHL thetaAboveCell0100)))

/-- Subcell `01002311` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01002311 : AngleCell :=
  childLH (childLH (childHH (childHL thetaAboveCell0100)))

/-- Subcell `01003200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01003200 : AngleCell :=
  childLL (childLL (childHL (childHH thetaAboveCell0100)))

/-- Subcell `01003201` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01003201 : AngleCell :=
  childLH (childLL (childHL (childHH thetaAboveCell0100)))

/-- Subcell `11103022` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11103022 : AngleCell :=
  childHL (childHL (childLL (childHH thetaBelowCell1110)))

/-- Subcell `11103023` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11103023 : AngleCell :=
  childHH (childHL (childLL (childHH thetaBelowCell1110)))

/-- Subcell `11103031` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11103031 : AngleCell :=
  childLH (childHH (childLL (childHH thetaBelowCell1110)))

/-- Subcell `11103032` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11103032 : AngleCell :=
  childHL (childHH (childLL (childHH thetaBelowCell1110)))

/-- Subcell `11103033` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11103033 : AngleCell :=
  childHH (childHH (childLL (childHH thetaBelowCell1110)))

/-- Subcell `11103120` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11103120 : AngleCell :=
  childLL (childHL (childLH (childHH thetaBelowCell1110)))

/-- Subcell `11103122` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11103122 : AngleCell :=
  childHL (childHL (childLH (childHH thetaBelowCell1110)))

/-- Subcell `11103123` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11103123 : AngleCell :=
  childHH (childHL (childLH (childHH thetaBelowCell1110)))

/-- Subcell `11103132` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11103132 : AngleCell :=
  childHL (childHH (childLH (childHH thetaBelowCell1110)))

/-- Subcell `11103133` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11103133 : AngleCell :=
  childHH (childHH (childLH (childHH thetaBelowCell1110)))

/-- Subcell `11103210` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11103210 : AngleCell :=
  childLL (childLH (childHL (childHH thetaBelowCell1110)))

/-- Subcell `11103211` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11103211 : AngleCell :=
  childLH (childLH (childHL (childHH thetaBelowCell1110)))

/-- Subcell `11103300` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11103300 : AngleCell :=
  childLL (childLL (childHH (childHH thetaBelowCell1110)))

/-- Subcell `11103301` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11103301 : AngleCell :=
  childLH (childLL (childHH (childHH thetaBelowCell1110)))

/-- Subcell `11103310` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11103310 : AngleCell :=
  childLL (childLH (childHH (childHH thetaBelowCell1110)))

/-- Subcell `11103311` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11103311 : AngleCell :=
  childLH (childLH (childHH (childHH thetaBelowCell1110)))

/-- Subcell `11112022` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11112022 : AngleCell :=
  childHL (childHL (childLL (childHL thetaBelowCell1111)))

/-- Subcell `11112023` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11112023 : AngleCell :=
  childHH (childHL (childLL (childHL thetaBelowCell1111)))

/-- Subcell `11112032` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11112032 : AngleCell :=
  childHL (childHH (childLL (childHL thetaBelowCell1111)))

/-- Subcell `11112033` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11112033 : AngleCell :=
  childHH (childHH (childLL (childHL thetaBelowCell1111)))

/-- Subcell `11112122` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11112122 : AngleCell :=
  childHL (childHL (childLH (childHL thetaBelowCell1111)))

/-- Subcell `11112123` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11112123 : AngleCell :=
  childHH (childHL (childLH (childHL thetaBelowCell1111)))

/-- Subcell `11112132` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11112132 : AngleCell :=
  childHL (childHH (childLH (childHL thetaBelowCell1111)))

/-- Subcell `11112133` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11112133 : AngleCell :=
  childHH (childHH (childLH (childHL thetaBelowCell1111)))

/-- Subcell `11112200` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11112200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaBelowCell1111)))

/-- Subcell `11112201` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11112201 : AngleCell :=
  childLH (childLL (childHL (childHL thetaBelowCell1111)))

/-- Subcell `11112210` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11112210 : AngleCell :=
  childLL (childLH (childHL (childHL thetaBelowCell1111)))

/-- Subcell `11112211` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11112211 : AngleCell :=
  childLH (childLH (childHL (childHL thetaBelowCell1111)))

/-- Subcell `11112300` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11112300 : AngleCell :=
  childLL (childLL (childHH (childHL thetaBelowCell1111)))

/-- Subcell `11112301` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11112301 : AngleCell :=
  childLH (childLL (childHH (childHL thetaBelowCell1111)))

/-- Subcell `11112310` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11112310 : AngleCell :=
  childLL (childLH (childHH (childHL thetaBelowCell1111)))

/-- Subcell `11112311` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11112311 : AngleCell :=
  childLH (childLH (childHH (childHL thetaBelowCell1111)))

/-- Subcell `11113022` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113022 : AngleCell :=
  childHL (childHL (childLL (childHH thetaBelowCell1111)))

/-- Subcell `11113023` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113023 : AngleCell :=
  childHH (childHL (childLL (childHH thetaBelowCell1111)))

/-- Subcell `11113032` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113032 : AngleCell :=
  childHL (childHH (childLL (childHH thetaBelowCell1111)))

/-- Subcell `11113033` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113033 : AngleCell :=
  childHH (childHH (childLL (childHH thetaBelowCell1111)))

/-- Subcell `11113122` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113122 : AngleCell :=
  childHL (childHL (childLH (childHH thetaBelowCell1111)))

/-- Subcell `11113123` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113123 : AngleCell :=
  childHH (childHL (childLH (childHH thetaBelowCell1111)))

/-- Subcell `11113132` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113132 : AngleCell :=
  childHL (childHH (childLH (childHH thetaBelowCell1111)))

/-- Subcell `11113133` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113133 : AngleCell :=
  childHH (childHH (childLH (childHH thetaBelowCell1111)))

/-- Subcell `11113200` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113200 : AngleCell :=
  childLL (childLL (childHL (childHH thetaBelowCell1111)))

/-- Subcell `11113201` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113201 : AngleCell :=
  childLH (childLL (childHL (childHH thetaBelowCell1111)))

/-- Subcell `11113210` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113210 : AngleCell :=
  childLL (childLH (childHL (childHH thetaBelowCell1111)))

/-- Subcell `111132010310` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132010310 : AngleCell :=
  childLL (childLH (childHH (childLL thetaBelowCell11113201)))

/-- Subcell `111132010311` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132010311 : AngleCell :=
  childLH (childLH (childHH (childLL thetaBelowCell11113201)))

/-- Subcell `111132010312` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132010312 : AngleCell :=
  childHL (childLH (childHH (childLL thetaBelowCell11113201)))

/-- Subcell `111132010313` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132010313 : AngleCell :=
  childHH (childLH (childHH (childLL thetaBelowCell11113201)))

/-- Subcell `111132011120` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132011120 : AngleCell :=
  childLL (childHL (childLH (childLH thetaBelowCell11113201)))

/-- Subcell `111132011121` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132011121 : AngleCell :=
  childLH (childHL (childLH (childLH thetaBelowCell11113201)))

/-- Subcell `111132011122` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132011122 : AngleCell :=
  childHL (childHL (childLH (childLH thetaBelowCell11113201)))

/-- Subcell `111132011123` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132011123 : AngleCell :=
  childHH (childHL (childLH (childLH thetaBelowCell11113201)))

/-- Subcell `111132011130` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132011130 : AngleCell :=
  childLL (childHH (childLH (childLH thetaBelowCell11113201)))

/-- Subcell `111132011131` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132011131 : AngleCell :=
  childLH (childHH (childLH (childLH thetaBelowCell11113201)))

/-- Subcell `111132011132` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132011132 : AngleCell :=
  childHL (childHH (childLH (childLH thetaBelowCell11113201)))

/-- Subcell `111132011133` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132011133 : AngleCell :=
  childHH (childHH (childLH (childLH thetaBelowCell11113201)))

/-- Subcell `111132011200` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132011200 : AngleCell :=
  childLL (childLL (childHL (childLH thetaBelowCell11113201)))

/-- Subcell `111132011201` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132011201 : AngleCell :=
  childLH (childLL (childHL (childLH thetaBelowCell11113201)))

/-- Subcell `111132011202` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132011202 : AngleCell :=
  childHL (childLL (childHL (childLH thetaBelowCell11113201)))

/-- Subcell `111132011203` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132011203 : AngleCell :=
  childHH (childLL (childHL (childLH thetaBelowCell11113201)))

/-- Subcell `111132011210` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132011210 : AngleCell :=
  childLL (childLH (childHL (childLH thetaBelowCell11113201)))

/-- Subcell `111132011211` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132011211 : AngleCell :=
  childLH (childLH (childHL (childLH thetaBelowCell11113201)))

/-- Subcell `111132011212` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132011212 : AngleCell :=
  childHL (childLH (childHL (childLH thetaBelowCell11113201)))

/-- Subcell `111132011213` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132011213 : AngleCell :=
  childHH (childLH (childHL (childLH thetaBelowCell11113201)))

/-- Subcell `111132011300` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132011300 : AngleCell :=
  childLL (childLL (childHH (childLH thetaBelowCell11113201)))

/-- Subcell `111132011301` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132011301 : AngleCell :=
  childLH (childLL (childHH (childLH thetaBelowCell11113201)))

/-- Subcell `111132011302` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132011302 : AngleCell :=
  childHL (childLL (childHH (childLH thetaBelowCell11113201)))

/-- Subcell `111132011303` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132011303 : AngleCell :=
  childHH (childLL (childHH (childLH thetaBelowCell11113201)))

/-- Subcell `111132011310` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132011310 : AngleCell :=
  childLL (childLH (childHH (childLH thetaBelowCell11113201)))

/-- Subcell `111132011311` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132011311 : AngleCell :=
  childLH (childLH (childHH (childLH thetaBelowCell11113201)))

/-- Subcell `111132011312` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132011312 : AngleCell :=
  childHL (childLH (childHH (childLH thetaBelowCell11113201)))

/-- Subcell `111132011313` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132011313 : AngleCell :=
  childHH (childLH (childHH (childLH thetaBelowCell11113201)))

/-- Subcell `111132011320` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132011320 : AngleCell :=
  childLL (childHL (childHH (childLH thetaBelowCell11113201)))

/-- Subcell `111132011321` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132011321 : AngleCell :=
  childLH (childHL (childHH (childLH thetaBelowCell11113201)))

/-- Subcell `111132011322` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132011322 : AngleCell :=
  childHL (childHL (childHH (childLH thetaBelowCell11113201)))

/-- Subcell `111132011323` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132011323 : AngleCell :=
  childHH (childHL (childHH (childLH thetaBelowCell11113201)))

/-- Subcell `111132011330` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132011330 : AngleCell :=
  childLL (childHH (childHH (childLH thetaBelowCell11113201)))

/-- Subcell `111132011331` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132011331 : AngleCell :=
  childLH (childHH (childHH (childLH thetaBelowCell11113201)))

/-- Subcell `111132011332` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132011332 : AngleCell :=
  childHL (childHH (childHH (childLH thetaBelowCell11113201)))

/-- Subcell `111132011333` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132011333 : AngleCell :=
  childHH (childHH (childHH (childLH thetaBelowCell11113201)))

/-- Subcell `111132100000` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132100000 : AngleCell :=
  childLL (childLL (childLL (childLL thetaBelowCell11113210)))

/-- Subcell `111132100001` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132100001 : AngleCell :=
  childLH (childLL (childLL (childLL thetaBelowCell11113210)))

/-- Subcell `111132100002` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132100002 : AngleCell :=
  childHL (childLL (childLL (childLL thetaBelowCell11113210)))

/-- Subcell `111132100003` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132100003 : AngleCell :=
  childHH (childLL (childLL (childLL thetaBelowCell11113210)))

/-- Subcell `111132100010` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132100010 : AngleCell :=
  childLL (childLH (childLL (childLL thetaBelowCell11113210)))

/-- Subcell `111132100011` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132100011 : AngleCell :=
  childLH (childLH (childLL (childLL thetaBelowCell11113210)))

/-- Subcell `111132100012` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132100012 : AngleCell :=
  childHL (childLH (childLL (childLL thetaBelowCell11113210)))

/-- Subcell `111132100013` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132100013 : AngleCell :=
  childHH (childLH (childLL (childLL thetaBelowCell11113210)))

/-- Subcell `111132100020` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132100020 : AngleCell :=
  childLL (childHL (childLL (childLL thetaBelowCell11113210)))

/-- Subcell `111132100021` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132100021 : AngleCell :=
  childLH (childHL (childLL (childLL thetaBelowCell11113210)))

/-- Subcell `111132100022` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132100022 : AngleCell :=
  childHL (childHL (childLL (childLL thetaBelowCell11113210)))

/-- Subcell `111132100023` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132100023 : AngleCell :=
  childHH (childHL (childLL (childLL thetaBelowCell11113210)))

/-- Subcell `111132100030` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132100030 : AngleCell :=
  childLL (childHH (childLL (childLL thetaBelowCell11113210)))

/-- Subcell `111132100031` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132100031 : AngleCell :=
  childLH (childHH (childLL (childLL thetaBelowCell11113210)))

/-- Subcell `111132100032` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132100032 : AngleCell :=
  childHL (childHH (childLL (childLL thetaBelowCell11113210)))

/-- Subcell `111132100033` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132100033 : AngleCell :=
  childHH (childHH (childLL (childLL thetaBelowCell11113210)))

/-- Subcell `111132100100` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132100100 : AngleCell :=
  childLL (childLL (childLH (childLL thetaBelowCell11113210)))

/-- Subcell `111132100101` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132100101 : AngleCell :=
  childLH (childLL (childLH (childLL thetaBelowCell11113210)))

/-- Subcell `111132100102` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132100102 : AngleCell :=
  childHL (childLL (childLH (childLL thetaBelowCell11113210)))

/-- Subcell `111132100103` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132100103 : AngleCell :=
  childHH (childLL (childLH (childLL thetaBelowCell11113210)))

/-- Subcell `111132100120` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132100120 : AngleCell :=
  childLL (childHL (childLH (childLL thetaBelowCell11113210)))

/-- Subcell `111132100121` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132100121 : AngleCell :=
  childLH (childHL (childLH (childLL thetaBelowCell11113210)))

/-- Subcell `111132100122` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132100122 : AngleCell :=
  childHL (childHL (childLH (childLL thetaBelowCell11113210)))

/-- Subcell `111132100123` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132100123 : AngleCell :=
  childHH (childHL (childLH (childLL thetaBelowCell11113210)))

/-- Subcell `111132100130` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132100130 : AngleCell :=
  childLL (childHH (childLH (childLL thetaBelowCell11113210)))

/-- Subcell `111132100131` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132100131 : AngleCell :=
  childLH (childHH (childLH (childLL thetaBelowCell11113210)))

/-- Subcell `111132100132` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132100132 : AngleCell :=
  childHL (childHH (childLH (childLL thetaBelowCell11113210)))

/-- Subcell `111132100133` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132100133 : AngleCell :=
  childHH (childHH (childLH (childLL thetaBelowCell11113210)))

/-- Subcell `111132100200` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132100200 : AngleCell :=
  childLL (childLL (childHL (childLL thetaBelowCell11113210)))

/-- Subcell `111132100201` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132100201 : AngleCell :=
  childLH (childLL (childHL (childLL thetaBelowCell11113210)))

/-- Subcell `111132100202` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132100202 : AngleCell :=
  childHL (childLL (childHL (childLL thetaBelowCell11113210)))

/-- Subcell `111132100203` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132100203 : AngleCell :=
  childHH (childLL (childHL (childLL thetaBelowCell11113210)))

/-- Subcell `111132100210` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132100210 : AngleCell :=
  childLL (childLH (childHL (childLL thetaBelowCell11113210)))

/-- Subcell `111132100211` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132100211 : AngleCell :=
  childLH (childLH (childHL (childLL thetaBelowCell11113210)))

/-- Subcell `111132100212` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132100212 : AngleCell :=
  childHL (childLH (childHL (childLL thetaBelowCell11113210)))

/-- Subcell `111132100213` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132100213 : AngleCell :=
  childHH (childLH (childHL (childLL thetaBelowCell11113210)))

/-- Subcell `111132100220` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132100220 : AngleCell :=
  childLL (childHL (childHL (childLL thetaBelowCell11113210)))

/-- Subcell `111132100221` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132100221 : AngleCell :=
  childLH (childHL (childHL (childLL thetaBelowCell11113210)))

/-- Subcell `111132100222` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132100222 : AngleCell :=
  childHL (childHL (childHL (childLL thetaBelowCell11113210)))

/-- Subcell `111132100223` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132100223 : AngleCell :=
  childHH (childHL (childHL (childLL thetaBelowCell11113210)))

/-- Subcell `111132100230` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132100230 : AngleCell :=
  childLL (childHH (childHL (childLL thetaBelowCell11113210)))

/-- Subcell `111132100231` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132100231 : AngleCell :=
  childLH (childHH (childHL (childLL thetaBelowCell11113210)))

/-- Subcell `111132100232` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132100232 : AngleCell :=
  childHL (childHH (childHL (childLL thetaBelowCell11113210)))

/-- Subcell `111132100233` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132100233 : AngleCell :=
  childHH (childHH (childHL (childLL thetaBelowCell11113210)))

/-- Subcell `111132100300` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132100300 : AngleCell :=
  childLL (childLL (childHH (childLL thetaBelowCell11113210)))

/-- Subcell `111132100301` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132100301 : AngleCell :=
  childLH (childLL (childHH (childLL thetaBelowCell11113210)))

/-- Subcell `111132100302` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132100302 : AngleCell :=
  childHL (childLL (childHH (childLL thetaBelowCell11113210)))

/-- Subcell `111132100303` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132100303 : AngleCell :=
  childHH (childLL (childHH (childLL thetaBelowCell11113210)))

/-- Subcell `111132100310` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132100310 : AngleCell :=
  childLL (childLH (childHH (childLL thetaBelowCell11113210)))

/-- Subcell `111132100311` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132100311 : AngleCell :=
  childLH (childLH (childHH (childLL thetaBelowCell11113210)))

/-- Subcell `111132100312` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132100312 : AngleCell :=
  childHL (childLH (childHH (childLL thetaBelowCell11113210)))

/-- Subcell `111132100313` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132100313 : AngleCell :=
  childHH (childLH (childHH (childLL thetaBelowCell11113210)))

/-- Subcell `111132100320` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132100320 : AngleCell :=
  childLL (childHL (childHH (childLL thetaBelowCell11113210)))

/-- Subcell `111132100321` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132100321 : AngleCell :=
  childLH (childHL (childHH (childLL thetaBelowCell11113210)))

/-- Subcell `111132100322` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132100322 : AngleCell :=
  childHL (childHL (childHH (childLL thetaBelowCell11113210)))

/-- Subcell `111132100323` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132100323 : AngleCell :=
  childHH (childHL (childHH (childLL thetaBelowCell11113210)))

/-- Subcell `111132100330` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132100330 : AngleCell :=
  childLL (childHH (childHH (childLL thetaBelowCell11113210)))

/-- Subcell `111132100331` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132100331 : AngleCell :=
  childLH (childHH (childHH (childLL thetaBelowCell11113210)))

/-- Subcell `111132100332` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132100332 : AngleCell :=
  childHL (childHH (childHH (childLL thetaBelowCell11113210)))

/-- Subcell `111132100333` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111132100333 : AngleCell :=
  childHH (childHH (childHH (childLL thetaBelowCell11113210)))

end GerverSofa.PartE.CertificateCells37514173c1

namespace GerverSofa.PartE.CertificateCells00c658e5bf

/-- Subcell `1111` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111 : AngleCell :=
  childLH (childLH (childLH (childLH e24ThetaBelowRoot)))

/-- Subcell `11113312` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113312 : AngleCell :=
  childHL (childLH (childHH (childHH thetaBelowCell1111)))

/-- Subcell `11113313` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113313 : AngleCell :=
  childHH (childLH (childHH (childHH thetaBelowCell1111)))

end GerverSofa.PartE.CertificateCells00c658e5bf

section

/-
Copyright (c) 2026 Dawid Trela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dawid Trela
-/
/-!
# Gerver sofa dependency batch

* `KernelOnly.PartE.E24KC5TerminalBatchT307200009`.
-/

public section

noncomputable section

section

/-! E24KC5 checkpoint-aware kernel batch. -/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsb518b98fbe

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCellsb518b98fbe

open CertificateCellsb518b98fbe
theorem e24KC2ThetaAboveLeaf0110321030 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell01103210)) = true := by
  have h : ((childLL (childHH thetaAboveCell01103210))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell01103210)) h
theorem e24KC2ThetaAboveLeaf0110321031 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell01103210)) = true := by
  have h : ((childLH (childHH thetaAboveCell01103210))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell01103210)) h
theorem e24KC2ThetaAboveLeaf0110321032 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell01103210)) = true := by
  have h : ((childHL (childHH thetaAboveCell01103210))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH thetaAboveCell01103210)) h
theorem e24KC2ThetaAboveLeaf0110321033 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell01103210)) = true := by
  have h : ((childHH (childHH thetaAboveCell01103210))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH thetaAboveCell01103210)) h
theorem e24KC2ThetaAboveLeaf011032110 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell01103211) = true := by
  have h : ((childLL thetaAboveCell01103211)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell01103211) h
theorem e24KC2ThetaAboveLeaf011032111 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell01103211) = true := by
  have h : ((childLH thetaAboveCell01103211)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell01103211) h
theorem e24KC2ThetaAboveLeaf0110321120 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell01103211)) = true := by
  have h : ((childLL (childHL thetaAboveCell01103211))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell01103211)) h
theorem e24KC2ThetaAboveLeaf0110321121 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell01103211)) = true := by
  have h : ((childLH (childHL thetaAboveCell01103211))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell01103211)) h
theorem e24KC2ThetaAboveLeaf0110321122 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell01103211)) = true := by
  have h : ((childHL (childHL thetaAboveCell01103211))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL thetaAboveCell01103211)) h
theorem e24KC2ThetaAboveLeaf0110321123 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell01103211)) = true := by
  have h : ((childHH (childHL thetaAboveCell01103211))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL thetaAboveCell01103211)) h
theorem e24KC2ThetaAboveLeaf0110321130 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell01103211)) = true := by
  have h : ((childLL (childHH thetaAboveCell01103211))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell01103211)) h
theorem e24KC2ThetaAboveLeaf0110321131 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell01103211)) = true := by
  have h : ((childLH (childHH thetaAboveCell01103211))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell01103211)) h
theorem e24KC2ThetaAboveLeaf0110321132 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell01103211)) = true := by
  have h : ((childHL (childHH thetaAboveCell01103211))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH thetaAboveCell01103211)) h
theorem e24KC2ThetaAboveLeaf0110321133 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell01103211)) = true := by
  have h : ((childHH (childHH thetaAboveCell01103211))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH thetaAboveCell01103211)) h
theorem e24KC2ThetaAboveLeaf0110321200 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell01103212)) = true := by
  have h : ((childLL (childLL thetaAboveCell01103212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell01103212)) h
theorem e24KC2ThetaAboveLeaf0110321201 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell01103212)) = true := by
  have h : ((childLH (childLL thetaAboveCell01103212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell01103212)) h
theorem e24KC2ThetaAboveLeaf0110321202 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell01103212)) = true := by
  have h : ((childHL (childLL thetaAboveCell01103212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell01103212)) h
theorem e24KC2ThetaAboveLeaf0110321203 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell01103212)) = true := by
  have h : ((childHH (childLL thetaAboveCell01103212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell01103212)) h
theorem e24KC2ThetaAboveLeaf0110321210 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell01103212)) = true := by
  have h : ((childLL (childLH thetaAboveCell01103212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell01103212)) h
theorem e24KC2ThetaAboveLeaf0110321211 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell01103212)) = true := by
  have h : ((childLH (childLH thetaAboveCell01103212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell01103212)) h
theorem e24KC2ThetaAboveLeaf0110321212 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell01103212)) = true := by
  have h : ((childHL (childLH thetaAboveCell01103212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell01103212)) h
theorem e24KC2ThetaAboveLeaf0110321213 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell01103212)) = true := by
  have h : ((childHH (childLH thetaAboveCell01103212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell01103212)) h
theorem e24KC2ThetaAboveLeaf0110321220 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell01103212)) = true := by
  have h : ((childLL (childHL thetaAboveCell01103212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell01103212)) h
theorem e24KC2ThetaAboveLeaf0110321221 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell01103212)) = true := by
  have h : ((childLH (childHL thetaAboveCell01103212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell01103212)) h
theorem e24KC2ThetaAboveLeaf0110321222 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell01103212)) = true := by
  have h : ((childHL (childHL thetaAboveCell01103212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL thetaAboveCell01103212)) h
theorem e24KC2ThetaAboveLeaf0110321223 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell01103212)) = true := by
  have h : ((childHH (childHL thetaAboveCell01103212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL thetaAboveCell01103212)) h
theorem e24KC2ThetaAboveLeaf0110321230 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell01103212)) = true := by
  have h : ((childLL (childHH thetaAboveCell01103212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell01103212)) h
theorem e24KC2ThetaAboveLeaf0110321231 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell01103212)) = true := by
  have h : ((childLH (childHH thetaAboveCell01103212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell01103212)) h
theorem e24KC2ThetaAboveLeaf0110321232 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell01103212)) = true := by
  have h : ((childHL (childHH thetaAboveCell01103212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH thetaAboveCell01103212)) h
theorem e24KC2ThetaAboveLeaf0110321233 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell01103212)) = true := by
  have h : ((childHH (childHH thetaAboveCell01103212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH thetaAboveCell01103212)) h
theorem e24KC2ThetaAboveLeaf0110321300 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell01103213)) = true := by
  have h : ((childLL (childLL thetaAboveCell01103213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell01103213)) h
theorem e24KC2ThetaAboveLeaf0110321301 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell01103213)) = true := by
  have h : ((childLH (childLL thetaAboveCell01103213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell01103213)) h
theorem e24KC2ThetaAboveLeaf0110321302 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell01103213)) = true := by
  have h : ((childHL (childLL thetaAboveCell01103213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell01103213)) h
theorem e24KC2ThetaAboveLeaf0110321303 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell01103213)) = true := by
  have h : ((childHH (childLL thetaAboveCell01103213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell01103213)) h
theorem e24KC2ThetaAboveLeaf0110321310 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell01103213)) = true := by
  have h : ((childLL (childLH thetaAboveCell01103213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell01103213)) h
theorem e24KC2ThetaAboveLeaf0110321311 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell01103213)) = true := by
  have h : ((childLH (childLH thetaAboveCell01103213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell01103213)) h
theorem e24KC2ThetaAboveLeaf0110321312 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell01103213)) = true := by
  have h : ((childHL (childLH thetaAboveCell01103213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell01103213)) h
theorem e24KC2ThetaAboveLeaf0110321313 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell01103213)) = true := by
  have h : ((childHH (childLH thetaAboveCell01103213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell01103213)) h
theorem e24KC2ThetaAboveLeaf0110321320 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell01103213)) = true := by
  have h : ((childLL (childHL thetaAboveCell01103213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell01103213)) h
theorem e24KC2ThetaAboveLeaf0110321321 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell01103213)) = true := by
  have h : ((childLH (childHL thetaAboveCell01103213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell01103213)) h
theorem e24KC2ThetaAboveLeaf0110321322 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell01103213)) = true := by
  have h : ((childHL (childHL thetaAboveCell01103213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL thetaAboveCell01103213)) h
theorem e24KC2ThetaAboveLeaf0110321323 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell01103213)) = true := by
  have h : ((childHH (childHL thetaAboveCell01103213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL thetaAboveCell01103213)) h
theorem e24KC2ThetaAboveLeaf0110321330 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell01103213)) = true := by
  have h : ((childLL (childHH thetaAboveCell01103213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell01103213)) h
theorem e24KC2ThetaAboveLeaf0110321331 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell01103213)) = true := by
  have h : ((childLH (childHH thetaAboveCell01103213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell01103213)) h
theorem e24KC2ThetaAboveLeaf0110321332 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell01103213)) = true := by
  have h : ((childHL (childHH thetaAboveCell01103213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH thetaAboveCell01103213)) h
theorem e24KC2ThetaAboveLeaf0110321333 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell01103213)) = true := by
  have h : ((childHH (childHH thetaAboveCell01103213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH thetaAboveCell01103213)) h
theorem e24KC2ThetaAboveLeaf011032200 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell01103220) = true := by
  have h : ((childLL thetaAboveCell01103220)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell01103220) h
theorem e24KC2ThetaAboveLeaf011032201 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell01103220) = true := by
  have h : ((childLH thetaAboveCell01103220)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell01103220) h
theorem e24KC2ThetaAboveLeaf011032202 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell01103220) = true := by
  have h : ((childHL thetaAboveCell01103220)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell01103220) h
theorem e24KC2ThetaAboveLeaf011032203 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell01103220) = true := by
  have h : ((childHH thetaAboveCell01103220)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell01103220) h
theorem e24KC2ThetaAboveLeaf011032210 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell01103221) = true := by
  have h : ((childLL thetaAboveCell01103221)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell01103221) h
theorem e24KC2ThetaAboveLeaf011032211 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell01103221) = true := by
  have h : ((childLH thetaAboveCell01103221)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell01103221) h
theorem e24KC2ThetaAboveLeaf011032212 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell01103221) = true := by
  have h : ((childHL thetaAboveCell01103221)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell01103221) h
theorem e24KC2ThetaAboveLeaf011032213 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell01103221) = true := by
  have h : ((childHH thetaAboveCell01103221)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell01103221) h
theorem e24KC2ThetaAboveLeaf01103222 :
    adaptiveCoverCheck 11 thetaAboveCell01103222 = true := by
  have h : (thetaAboveCell01103222).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01103222 h
theorem e24KC2ThetaAboveLeaf01103223 :
    adaptiveCoverCheck 11 thetaAboveCell01103223 = true := by
  have h : (thetaAboveCell01103223).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01103223 h
theorem e24KC2ThetaAboveLeaf011032300 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell01103230) = true := by
  have h : ((childLL thetaAboveCell01103230)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell01103230) h
theorem e24KC2ThetaAboveLeaf011032301 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell01103230) = true := by
  have h : ((childLH thetaAboveCell01103230)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell01103230) h
theorem e24KC2ThetaAboveLeaf011032302 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell01103230) = true := by
  have h : ((childHL thetaAboveCell01103230)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell01103230) h
theorem e24KC2ThetaAboveLeaf011032303 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell01103230) = true := by
  have h : ((childHH thetaAboveCell01103230)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell01103230) h
theorem e24KC2ThetaAboveLeaf011032310 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell01103231) = true := by
  have h : ((childLL thetaAboveCell01103231)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell01103231) h
theorem e24KC2ThetaAboveLeaf011032311 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell01103231) = true := by
  have h : ((childLH thetaAboveCell01103231)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell01103231) h
theorem e24KC2ThetaAboveLeaf011032312 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell01103231) = true := by
  have h : ((childHL thetaAboveCell01103231)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell01103231) h
theorem e24KC2ThetaAboveLeaf011032313 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell01103231) = true := by
  have h : ((childHH thetaAboveCell01103231)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell01103231) h
theorem e24KC2ThetaAboveLeaf01103232 :
    adaptiveCoverCheck 11 thetaAboveCell01103232 = true := by
  have h : (thetaAboveCell01103232).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01103232 h
theorem e24KC2ThetaAboveLeaf01103233 :
    adaptiveCoverCheck 11 thetaAboveCell01103233 = true := by
  have h : (thetaAboveCell01103233).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01103233 h
theorem e24KC2ThetaAboveLeaf011033000 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell01103300) = true := by
  have h : ((childLL thetaAboveCell01103300)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell01103300) h
theorem e24KC2ThetaAboveLeaf011033001 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell01103300) = true := by
  have h : ((childLH thetaAboveCell01103300)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell01103300) h
theorem e24KC2ThetaAboveLeaf0110330020 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell01103300)) = true := by
  have h : ((childLL (childHL thetaAboveCell01103300))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell01103300)) h
theorem e24KC2ThetaAboveLeaf0110330021 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell01103300)) = true := by
  have h : ((childLH (childHL thetaAboveCell01103300))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell01103300)) h
theorem e24KC2ThetaAboveLeaf0110330022 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell01103300)) = true := by
  have h : ((childHL (childHL thetaAboveCell01103300))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL thetaAboveCell01103300)) h
theorem e24KC2ThetaAboveLeaf0110330023 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell01103300)) = true := by
  have h : ((childHH (childHL thetaAboveCell01103300))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL thetaAboveCell01103300)) h
theorem e24KC2ThetaAboveLeaf0110330030 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell01103300)) = true := by
  have h : ((childLL (childHH thetaAboveCell01103300))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell01103300)) h
theorem e24KC2ThetaAboveLeaf0110330031 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell01103300)) = true := by
  have h : ((childLH (childHH thetaAboveCell01103300))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell01103300)) h
theorem e24KC2ThetaAboveLeaf0110330032 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell01103300)) = true := by
  have h : ((childHL (childHH thetaAboveCell01103300))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH thetaAboveCell01103300)) h
theorem e24KC2ThetaAboveLeaf0110330033 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell01103300)) = true := by
  have h : ((childHH (childHH thetaAboveCell01103300))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH thetaAboveCell01103300)) h
theorem e24KC2ThetaAboveLeaf011033010 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell01103301) = true := by
  have h : ((childLL thetaAboveCell01103301)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell01103301) h
theorem e24KC2ThetaAboveLeaf011033011 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell01103301) = true := by
  have h : ((childLH thetaAboveCell01103301)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell01103301) h
theorem e24KC2ThetaAboveLeaf0110330120 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell01103301)) = true := by
  have h : ((childLL (childHL thetaAboveCell01103301))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell01103301)) h
theorem e24KC2ThetaAboveLeaf0110330121 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell01103301)) = true := by
  have h : ((childLH (childHL thetaAboveCell01103301))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell01103301)) h
theorem e24KC2ThetaAboveLeaf0110330122 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell01103301)) = true := by
  have h : ((childHL (childHL thetaAboveCell01103301))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL thetaAboveCell01103301)) h
theorem e24KC2ThetaAboveLeaf0110330123 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell01103301)) = true := by
  have h : ((childHH (childHL thetaAboveCell01103301))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL thetaAboveCell01103301)) h
theorem e24KC2ThetaAboveLeaf0110330130 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell01103301)) = true := by
  have h : ((childLL (childHH thetaAboveCell01103301))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell01103301)) h
theorem e24KC2ThetaAboveLeaf0110330131 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell01103301)) = true := by
  have h : ((childLH (childHH thetaAboveCell01103301))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell01103301)) h
theorem e24KC2ThetaAboveLeaf0110330132 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell01103301)) = true := by
  have h : ((childHL (childHH thetaAboveCell01103301))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH thetaAboveCell01103301)) h
theorem e24KC2ThetaAboveLeaf0110330133 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell01103301)) = true := by
  have h : ((childHH (childHH thetaAboveCell01103301))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH thetaAboveCell01103301)) h
theorem e24KC2ThetaAboveLeaf0110330200 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell01103302)) = true := by
  have h : ((childLL (childLL thetaAboveCell01103302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell01103302)) h
theorem e24KC2ThetaAboveLeaf0110330201 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell01103302)) = true := by
  have h : ((childLH (childLL thetaAboveCell01103302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell01103302)) h
theorem e24KC2ThetaAboveLeaf0110330202 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell01103302)) = true := by
  have h : ((childHL (childLL thetaAboveCell01103302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell01103302)) h
theorem e24KC2ThetaAboveLeaf0110330203 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell01103302)) = true := by
  have h : ((childHH (childLL thetaAboveCell01103302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell01103302)) h
theorem e24KC2ThetaAboveLeaf0110330210 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell01103302)) = true := by
  have h : ((childLL (childLH thetaAboveCell01103302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell01103302)) h
theorem e24KC2ThetaAboveLeaf0110330211 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell01103302)) = true := by
  have h : ((childLH (childLH thetaAboveCell01103302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell01103302)) h
theorem e24KC2ThetaAboveLeaf0110330212 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell01103302)) = true := by
  have h : ((childHL (childLH thetaAboveCell01103302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell01103302)) h
theorem e24KC2ThetaAboveLeaf0110330213 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell01103302)) = true := by
  have h : ((childHH (childLH thetaAboveCell01103302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell01103302)) h
theorem e24KC2ThetaAboveLeaf0110330220 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell01103302)) = true := by
  have h : ((childLL (childHL thetaAboveCell01103302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell01103302)) h
theorem e24KC2ThetaAboveLeaf0110330221 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell01103302)) = true := by
  have h : ((childLH (childHL thetaAboveCell01103302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell01103302)) h
theorem e24KC2ThetaAboveLeaf0110330222 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell01103302)) = true := by
  have h : ((childHL (childHL thetaAboveCell01103302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL thetaAboveCell01103302)) h
theorem e24KC2ThetaAboveLeaf0110330223 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell01103302)) = true := by
  have h : ((childHH (childHL thetaAboveCell01103302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL thetaAboveCell01103302)) h
theorem e24KC2ThetaAboveLeaf0110330230 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell01103302)) = true := by
  have h : ((childLL (childHH thetaAboveCell01103302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell01103302)) h
theorem e24KC2ThetaAboveLeaf0110330231 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell01103302)) = true := by
  have h : ((childLH (childHH thetaAboveCell01103302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell01103302)) h
theorem e24KC2ThetaAboveLeaf0110330232 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell01103302)) = true := by
  have h : ((childHL (childHH thetaAboveCell01103302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH thetaAboveCell01103302)) h
theorem e24KC2ThetaAboveLeaf0110330233 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell01103302)) = true := by
  have h : ((childHH (childHH thetaAboveCell01103302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH thetaAboveCell01103302)) h
theorem e24KC2ThetaAboveLeaf0110330300 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell01103303)) = true := by
  have h : ((childLL (childLL thetaAboveCell01103303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell01103303)) h
theorem e24KC2ThetaAboveLeaf0110330301 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell01103303)) = true := by
  have h : ((childLH (childLL thetaAboveCell01103303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell01103303)) h
theorem e24KC2ThetaAboveLeaf0110330302 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell01103303)) = true := by
  have h : ((childHL (childLL thetaAboveCell01103303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell01103303)) h
theorem e24KC2ThetaAboveLeaf0110330303 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell01103303)) = true := by
  have h : ((childHH (childLL thetaAboveCell01103303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell01103303)) h
theorem e24KC2ThetaAboveLeaf0110330310 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell01103303)) = true := by
  have h : ((childLL (childLH thetaAboveCell01103303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell01103303)) h
theorem e24KC2ThetaAboveLeaf0110330311 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell01103303)) = true := by
  have h : ((childLH (childLH thetaAboveCell01103303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell01103303)) h
theorem e24KC2ThetaAboveLeaf0110330312 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell01103303)) = true := by
  have h : ((childHL (childLH thetaAboveCell01103303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell01103303)) h
theorem e24KC2ThetaAboveLeaf0110330313 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell01103303)) = true := by
  have h : ((childHH (childLH thetaAboveCell01103303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell01103303)) h
theorem e24KC2ThetaAboveLeaf0110330320 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell01103303)) = true := by
  have h : ((childLL (childHL thetaAboveCell01103303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell01103303)) h
theorem e24KC2ThetaAboveLeaf0110330321 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell01103303)) = true := by
  have h : ((childLH (childHL thetaAboveCell01103303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell01103303)) h
theorem e24KC2ThetaAboveLeaf0110330322 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell01103303)) = true := by
  have h : ((childHL (childHL thetaAboveCell01103303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL thetaAboveCell01103303)) h
theorem e24KC2ThetaAboveLeaf0110330323 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell01103303)) = true := by
  have h : ((childHH (childHL thetaAboveCell01103303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL thetaAboveCell01103303)) h
theorem e24KC2ThetaAboveLeaf0110330330 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell01103303)) = true := by
  have h : ((childLL (childHH thetaAboveCell01103303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell01103303)) h
theorem e24KC2ThetaAboveLeaf0110330331 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell01103303)) = true := by
  have h : ((childLH (childHH thetaAboveCell01103303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell01103303)) h
theorem e24KC2ThetaAboveLeaf0110330332 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell01103303)) = true := by
  have h : ((childHL (childHH thetaAboveCell01103303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH thetaAboveCell01103303)) h
theorem e24KC2ThetaAboveLeaf0110330333 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell01103303)) = true := by
  have h : ((childHH (childHH thetaAboveCell01103303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH thetaAboveCell01103303)) h
theorem e24KC2ThetaAboveLeaf011033100 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell01103310) = true := by
  have h : ((childLL thetaAboveCell01103310)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell01103310) h
theorem e24KC2ThetaAboveLeaf011033101 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell01103310) = true := by
  have h : ((childLH thetaAboveCell01103310)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell01103310) h
theorem e24KC2ThetaAboveLeaf0110331020 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell01103310)) = true := by
  have h : ((childLL (childHL thetaAboveCell01103310))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell01103310)) h
theorem e24KC2ThetaAboveLeaf0110331021 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell01103310)) = true := by
  have h : ((childLH (childHL thetaAboveCell01103310))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell01103310)) h
theorem e24KC2ThetaAboveLeaf0110331022 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell01103310)) = true := by
  have h : ((childHL (childHL thetaAboveCell01103310))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL thetaAboveCell01103310)) h
theorem e24KC2ThetaAboveLeaf0110331023 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell01103310)) = true := by
  have h : ((childHH (childHL thetaAboveCell01103310))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL thetaAboveCell01103310)) h
theorem e24KC2ThetaAboveLeaf0110331030 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell01103310)) = true := by
  have h : ((childLL (childHH thetaAboveCell01103310))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell01103310)) h
theorem e24KC2ThetaAboveLeaf0110331031 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell01103310)) = true := by
  have h : ((childLH (childHH thetaAboveCell01103310))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell01103310)) h
theorem e24KC2ThetaAboveLeaf0110331032 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell01103310)) = true := by
  have h : ((childHL (childHH thetaAboveCell01103310))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH thetaAboveCell01103310)) h
theorem e24KC2ThetaAboveLeaf0110331033 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell01103310)) = true := by
  have h : ((childHH (childHH thetaAboveCell01103310))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH thetaAboveCell01103310)) h
theorem e24KC2ThetaAboveLeaf011033110 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell01103311) = true := by
  have h : ((childLL thetaAboveCell01103311)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell01103311) h
theorem e24KC2ThetaAboveLeaf011033111 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell01103311) = true := by
  have h : ((childLH thetaAboveCell01103311)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell01103311) h
theorem e24KC2ThetaAboveLeaf0110331120 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell01103311)) = true := by
  have h : ((childLL (childHL thetaAboveCell01103311))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell01103311)) h
theorem e24KC2ThetaAboveLeaf0110331121 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell01103311)) = true := by
  have h : ((childLH (childHL thetaAboveCell01103311))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell01103311)) h
theorem e24KC2ThetaAboveLeaf0110331122 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell01103311)) = true := by
  have h : ((childHL (childHL thetaAboveCell01103311))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL thetaAboveCell01103311)) h
theorem e24KC2ThetaAboveLeaf0110331123 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell01103311)) = true := by
  have h : ((childHH (childHL thetaAboveCell01103311))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL thetaAboveCell01103311)) h
theorem e24KC2ThetaAboveLeaf0110331130 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell01103311)) = true := by
  have h : ((childLL (childHH thetaAboveCell01103311))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell01103311)) h
theorem e24KC2ThetaAboveLeaf0110331131 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell01103311)) = true := by
  have h : ((childLH (childHH thetaAboveCell01103311))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell01103311)) h
theorem e24KC2ThetaAboveLeaf0110331132 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell01103311)) = true := by
  have h : ((childHL (childHH thetaAboveCell01103311))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH thetaAboveCell01103311)) h
theorem e24KC2ThetaAboveLeaf0110331133 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell01103311)) = true := by
  have h : ((childHH (childHH thetaAboveCell01103311))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH thetaAboveCell01103311)) h
theorem e24KC2ThetaAboveLeaf0110331200 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell01103312)) = true := by
  have h : ((childLL (childLL thetaAboveCell01103312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell01103312)) h
theorem e24KC2ThetaAboveLeaf0110331201 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell01103312)) = true := by
  have h : ((childLH (childLL thetaAboveCell01103312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell01103312)) h
theorem e24KC2ThetaAboveLeaf0110331202 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell01103312)) = true := by
  have h : ((childHL (childLL thetaAboveCell01103312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell01103312)) h
theorem e24KC2ThetaAboveLeaf0110331203 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell01103312)) = true := by
  have h : ((childHH (childLL thetaAboveCell01103312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell01103312)) h
theorem e24KC2ThetaAboveLeaf0110331210 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell01103312)) = true := by
  have h : ((childLL (childLH thetaAboveCell01103312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell01103312)) h
theorem e24KC2ThetaAboveLeaf0110331211 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell01103312)) = true := by
  have h : ((childLH (childLH thetaAboveCell01103312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell01103312)) h
theorem e24KC2ThetaAboveLeaf0110331212 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell01103312)) = true := by
  have h : ((childHL (childLH thetaAboveCell01103312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell01103312)) h
theorem e24KC2ThetaAboveLeaf0110331213 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell01103312)) = true := by
  have h : ((childHH (childLH thetaAboveCell01103312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell01103312)) h
theorem e24KC2ThetaAboveLeaf0110331220 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell01103312)) = true := by
  have h : ((childLL (childHL thetaAboveCell01103312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell01103312)) h
theorem e24KC2ThetaAboveLeaf0110331221 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell01103312)) = true := by
  have h : ((childLH (childHL thetaAboveCell01103312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell01103312)) h
theorem e24KC2ThetaAboveLeaf0110331222 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell01103312)) = true := by
  have h : ((childHL (childHL thetaAboveCell01103312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL thetaAboveCell01103312)) h
theorem e24KC2ThetaAboveLeaf0110331223 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell01103312)) = true := by
  have h : ((childHH (childHL thetaAboveCell01103312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL thetaAboveCell01103312)) h
theorem e24KC2ThetaAboveLeaf0110331230 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell01103312)) = true := by
  have h : ((childLL (childHH thetaAboveCell01103312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell01103312)) h
theorem e24KC2ThetaAboveLeaf0110331231 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell01103312)) = true := by
  have h : ((childLH (childHH thetaAboveCell01103312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell01103312)) h
theorem e24KC2ThetaAboveLeaf0110331232 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell01103312)) = true := by
  have h : ((childHL (childHH thetaAboveCell01103312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH thetaAboveCell01103312)) h
theorem e24KC2ThetaAboveLeaf0110331233 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell01103312)) = true := by
  have h : ((childHH (childHH thetaAboveCell01103312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH thetaAboveCell01103312)) h
theorem e24KC2ThetaAboveLeaf0110331300 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell01103313)) = true := by
  have h : ((childLL (childLL thetaAboveCell01103313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell01103313)) h
theorem e24KC2ThetaAboveLeaf0110331301 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell01103313)) = true := by
  have h : ((childLH (childLL thetaAboveCell01103313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell01103313)) h
theorem e24KC2ThetaAboveLeaf0110331302 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell01103313)) = true := by
  have h : ((childHL (childLL thetaAboveCell01103313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell01103313)) h
theorem e24KC2ThetaAboveLeaf0110331303 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell01103313)) = true := by
  have h : ((childHH (childLL thetaAboveCell01103313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell01103313)) h
theorem e24KC2ThetaAboveLeaf0110331310 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell01103313)) = true := by
  have h : ((childLL (childLH thetaAboveCell01103313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell01103313)) h
theorem e24KC2ThetaAboveLeaf0110331311 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell01103313)) = true := by
  have h : ((childLH (childLH thetaAboveCell01103313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell01103313)) h
theorem e24KC2ThetaAboveLeaf0110331312 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell01103313)) = true := by
  have h : ((childHL (childLH thetaAboveCell01103313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell01103313)) h
theorem e24KC2ThetaAboveLeaf0110331313 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell01103313)) = true := by
  have h : ((childHH (childLH thetaAboveCell01103313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell01103313)) h
theorem e24KC2ThetaAboveLeaf0110331320 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell01103313)) = true := by
  have h : ((childLL (childHL thetaAboveCell01103313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell01103313)) h
theorem e24KC2ThetaAboveLeaf0110331321 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell01103313)) = true := by
  have h : ((childLH (childHL thetaAboveCell01103313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell01103313)) h
theorem e24KC2ThetaAboveLeaf0110331322 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell01103313)) = true := by
  have h : ((childHL (childHL thetaAboveCell01103313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL thetaAboveCell01103313)) h
theorem e24KC2ThetaAboveLeaf0110331323 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell01103313)) = true := by
  have h : ((childHH (childHL thetaAboveCell01103313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL thetaAboveCell01103313)) h
theorem e24KC2ThetaAboveLeaf0110331330 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell01103313)) = true := by
  have h : ((childLL (childHH thetaAboveCell01103313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell01103313)) h
theorem e24KC2ThetaAboveLeaf0110331331 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell01103313)) = true := by
  have h : ((childLH (childHH thetaAboveCell01103313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell01103313)) h
theorem e24KC2ThetaAboveLeaf0110331332 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell01103313)) = true := by
  have h : ((childHL (childHH thetaAboveCell01103313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH thetaAboveCell01103313)) h
theorem e24KC2ThetaAboveLeaf0110331333 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell01103313)) = true := by
  have h : ((childHH (childHH thetaAboveCell01103313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH thetaAboveCell01103313)) h
theorem e24KC2ThetaAboveLeaf011033200 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell01103320) = true := by
  have h : ((childLL thetaAboveCell01103320)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell01103320) h
theorem e24KC2ThetaAboveLeaf011033201 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell01103320) = true := by
  have h : ((childLH thetaAboveCell01103320)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell01103320) h
theorem e24KC2ThetaAboveLeaf011033202 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell01103320) = true := by
  have h : ((childHL thetaAboveCell01103320)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell01103320) h
theorem e24KC2ThetaAboveLeaf011033203 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell01103320) = true := by
  have h : ((childHH thetaAboveCell01103320)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell01103320) h
theorem e24KC2ThetaAboveLeaf011033210 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell01103321) = true := by
  have h : ((childLL thetaAboveCell01103321)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell01103321) h
theorem e24KC2ThetaAboveLeaf011033211 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell01103321) = true := by
  have h : ((childLH thetaAboveCell01103321)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell01103321) h
theorem e24KC2ThetaAboveLeaf011033212 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell01103321) = true := by
  have h : ((childHL thetaAboveCell01103321)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell01103321) h
theorem e24KC2ThetaAboveLeaf011033213 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell01103321) = true := by
  have h : ((childHH thetaAboveCell01103321)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell01103321) h
theorem e24KC2ThetaAboveLeaf01103322 :
    adaptiveCoverCheck 11 thetaAboveCell01103322 = true := by
  have h : (thetaAboveCell01103322).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01103322 h
theorem e24KC2ThetaAboveLeaf01103323 :
    adaptiveCoverCheck 11 thetaAboveCell01103323 = true := by
  have h : (thetaAboveCell01103323).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01103323 h
theorem e24KC2ThetaAboveLeaf011033300 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell01103330) = true := by
  have h : ((childLL thetaAboveCell01103330)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell01103330) h
theorem e24KC2ThetaAboveLeaf011033301 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell01103330) = true := by
  have h : ((childLH thetaAboveCell01103330)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell01103330) h
theorem e24KC2ThetaAboveLeaf011033302 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell01103330) = true := by
  have h : ((childHL thetaAboveCell01103330)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell01103330) h
theorem e24KC2ThetaAboveLeaf011033303 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell01103330) = true := by
  have h : ((childHH thetaAboveCell01103330)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell01103330) h
theorem e24KC2ThetaAboveLeaf011033310 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell01103331) = true := by
  have h : ((childLL thetaAboveCell01103331)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell01103331) h
theorem e24KC2ThetaAboveLeaf011033311 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell01103331) = true := by
  have h : ((childLH thetaAboveCell01103331)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell01103331) h
theorem e24KC2ThetaAboveLeaf011033312 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell01103331) = true := by
  have h : ((childHL thetaAboveCell01103331)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell01103331) h
theorem e24KC2ThetaAboveLeaf011033313 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell01103331) = true := by
  have h : ((childHH thetaAboveCell01103331)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell01103331) h
theorem e24KC2ThetaAboveLeaf01103332 :
    adaptiveCoverCheck 11 thetaAboveCell01103332 = true := by
  have h : (thetaAboveCell01103332).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01103332 h
theorem e24KC2ThetaAboveLeaf01103333 :
    adaptiveCoverCheck 11 thetaAboveCell01103333 = true := by
  have h : (thetaAboveCell01103333).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01103333 h
theorem e24KC2ThetaAboveLeaf011100 :
    adaptiveCoverCheck 13 (childLL (childLL thetaAboveCell0111)) = true := by
  have h : ((childLL (childLL thetaAboveCell0111))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLL (childLL thetaAboveCell0111)) h
theorem e24KC2ThetaAboveLeaf011101 :
    adaptiveCoverCheck 13 (childLH (childLL thetaAboveCell0111)) = true := by
  have h : ((childLH (childLL thetaAboveCell0111))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLH (childLL thetaAboveCell0111)) h
theorem e24KC2ThetaAboveLeaf011102 :
    adaptiveCoverCheck 13 (childHL (childLL thetaAboveCell0111)) = true := by
  have h : ((childHL (childLL thetaAboveCell0111))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHL (childLL thetaAboveCell0111)) h
theorem e24KC2ThetaAboveLeaf011103 :
    adaptiveCoverCheck 13 (childHH (childLL thetaAboveCell0111)) = true := by
  have h : ((childHH (childLL thetaAboveCell0111))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHH (childLL thetaAboveCell0111)) h
theorem e24KC2ThetaAboveLeaf011110 :
    adaptiveCoverCheck 13 (childLL (childLH thetaAboveCell0111)) = true := by
  have h : ((childLL (childLH thetaAboveCell0111))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLL (childLH thetaAboveCell0111)) h
theorem e24KC2ThetaAboveLeaf011111 :
    adaptiveCoverCheck 13 (childLH (childLH thetaAboveCell0111)) = true := by
  have h : ((childLH (childLH thetaAboveCell0111))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLH (childLH thetaAboveCell0111)) h
theorem e24KC2ThetaAboveLeaf011112 :
    adaptiveCoverCheck 13 (childHL (childLH thetaAboveCell0111)) = true := by
  have h : ((childHL (childLH thetaAboveCell0111))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHL (childLH thetaAboveCell0111)) h
theorem e24KC2ThetaAboveLeaf011113 :
    adaptiveCoverCheck 13 (childHH (childLH thetaAboveCell0111)) = true := by
  have h : ((childHH (childLH thetaAboveCell0111))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHH (childLH thetaAboveCell0111)) h
theorem e24KC2ThetaAboveLeaf0111200 :
    adaptiveCoverCheck 12 (childLL (childLL (childHL thetaAboveCell0111))) = true := by
  have h : ((childLL (childLL (childHL thetaAboveCell0111)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLL (childHL thetaAboveCell0111))) h
theorem e24KC2ThetaAboveLeaf0111201 :
    adaptiveCoverCheck 12 (childLH (childLL (childHL thetaAboveCell0111))) = true := by
  have h : ((childLH (childLL (childHL thetaAboveCell0111)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLL (childHL thetaAboveCell0111))) h
theorem e24KC2ThetaAboveLeaf01112020 :
    adaptiveCoverCheck 11 thetaAboveCell01112020 = true := by
  have h : (thetaAboveCell01112020).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01112020 h
theorem e24KC2ThetaAboveLeaf01112021 :
    adaptiveCoverCheck 11 thetaAboveCell01112021 = true := by
  have h : (thetaAboveCell01112021).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01112021 h
theorem e24KC2ThetaAboveLeaf01112022 :
    adaptiveCoverCheck 11 thetaAboveCell01112022 = true := by
  have h : (thetaAboveCell01112022).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01112022 h
theorem e24KC2ThetaAboveLeaf01112023 :
    adaptiveCoverCheck 11 thetaAboveCell01112023 = true := by
  have h : (thetaAboveCell01112023).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01112023 h
theorem e24KC2ThetaAboveLeaf01112030 :
    adaptiveCoverCheck 11 thetaAboveCell01112030 = true := by
  have h : (thetaAboveCell01112030).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01112030 h
theorem e24KC2ThetaAboveLeaf01112031 :
    adaptiveCoverCheck 11 thetaAboveCell01112031 = true := by
  have h : (thetaAboveCell01112031).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01112031 h
theorem e24KC2ThetaAboveLeaf01112032 :
    adaptiveCoverCheck 11 thetaAboveCell01112032 = true := by
  have h : (thetaAboveCell01112032).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01112032 h
theorem e24KC2ThetaAboveLeaf01112033 :
    adaptiveCoverCheck 11 thetaAboveCell01112033 = true := by
  have h : (thetaAboveCell01112033).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01112033 h
theorem e24KC2ThetaAboveLeaf0111210 :
    adaptiveCoverCheck 12 (childLL (childLH (childHL thetaAboveCell0111))) = true := by
  have h : ((childLL (childLH (childHL thetaAboveCell0111)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLH (childHL thetaAboveCell0111))) h
theorem e24KC2ThetaAboveLeaf0111211 :
    adaptiveCoverCheck 12 (childLH (childLH (childHL thetaAboveCell0111))) = true := by
  have h : ((childLH (childLH (childHL thetaAboveCell0111)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLH (childHL thetaAboveCell0111))) h
theorem e24KC2ThetaAboveLeaf01112120 :
    adaptiveCoverCheck 11 thetaAboveCell01112120 = true := by
  have h : (thetaAboveCell01112120).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01112120 h
theorem e24KC2ThetaAboveLeaf01112121 :
    adaptiveCoverCheck 11 thetaAboveCell01112121 = true := by
  have h : (thetaAboveCell01112121).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01112121 h
theorem e24KC2ThetaAboveLeaf01112122 :
    adaptiveCoverCheck 11 thetaAboveCell01112122 = true := by
  have h : (thetaAboveCell01112122).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01112122 h
theorem e24KC2ThetaAboveLeaf01112123 :
    adaptiveCoverCheck 11 thetaAboveCell01112123 = true := by
  have h : (thetaAboveCell01112123).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01112123 h
theorem e24KC2ThetaAboveLeaf01112130 :
    adaptiveCoverCheck 11 thetaAboveCell01112130 = true := by
  have h : (thetaAboveCell01112130).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01112130 h
theorem e24KC2ThetaAboveLeaf01112131 :
    adaptiveCoverCheck 11 thetaAboveCell01112131 = true := by
  have h : (thetaAboveCell01112131).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01112131 h
theorem e24KC2ThetaAboveLeaf01112132 :
    adaptiveCoverCheck 11 thetaAboveCell01112132 = true := by
  have h : (thetaAboveCell01112132).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01112132 h
theorem e24KC2ThetaAboveLeaf01112133 :
    adaptiveCoverCheck 11 thetaAboveCell01112133 = true := by
  have h : (thetaAboveCell01112133).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01112133 h
theorem e24KC2ThetaAboveLeaf011122000 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell01112200) = true := by
  have h : ((childLL thetaAboveCell01112200)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell01112200) h
theorem e24KC2ThetaAboveLeaf011122001 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell01112200) = true := by
  have h : ((childLH thetaAboveCell01112200)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell01112200) h
theorem e24KC2ThetaAboveLeaf0111220020 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell01112200)) = true := by
  have h : ((childLL (childHL thetaAboveCell01112200))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell01112200)) h
theorem e24KC2ThetaAboveLeaf0111220021 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell01112200)) = true := by
  have h : ((childLH (childHL thetaAboveCell01112200))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell01112200)) h
theorem e24KC2ThetaAboveLeaf0111220022 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell01112200)) = true := by
  have h : ((childHL (childHL thetaAboveCell01112200))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL thetaAboveCell01112200)) h
theorem e24KC2ThetaAboveLeaf0111220023 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell01112200)) = true := by
  have h : ((childHH (childHL thetaAboveCell01112200))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL thetaAboveCell01112200)) h
theorem e24KC2ThetaAboveLeaf0111220030 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell01112200)) = true := by
  have h : ((childLL (childHH thetaAboveCell01112200))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell01112200)) h
theorem e24KC2ThetaAboveLeaf0111220031 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell01112200)) = true := by
  have h : ((childLH (childHH thetaAboveCell01112200))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell01112200)) h
theorem e24KC2ThetaAboveLeaf0111220032 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell01112200)) = true := by
  have h : ((childHL (childHH thetaAboveCell01112200))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH thetaAboveCell01112200)) h
theorem e24KC2ThetaAboveLeaf0111220033 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell01112200)) = true := by
  have h : ((childHH (childHH thetaAboveCell01112200))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH thetaAboveCell01112200)) h
theorem e24KC2ThetaAboveLeaf011122010 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell01112201) = true := by
  have h : ((childLL thetaAboveCell01112201)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell01112201) h
theorem e24KC2ThetaAboveLeaf011122011 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell01112201) = true := by
  have h : ((childLH thetaAboveCell01112201)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell01112201) h
theorem e24KC2ThetaAboveLeaf0111220120 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell01112201)) = true := by
  have h : ((childLL (childHL thetaAboveCell01112201))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell01112201)) h
theorem e24KC2ThetaAboveLeaf0111220121 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell01112201)) = true := by
  have h : ((childLH (childHL thetaAboveCell01112201))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell01112201)) h
theorem e24KC2ThetaAboveLeaf0111220122 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell01112201)) = true := by
  have h : ((childHL (childHL thetaAboveCell01112201))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL thetaAboveCell01112201)) h
theorem e24KC2ThetaAboveLeaf0111220123 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell01112201)) = true := by
  have h : ((childHH (childHL thetaAboveCell01112201))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL thetaAboveCell01112201)) h
theorem e24KC2ThetaAboveLeaf0111220130 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell01112201)) = true := by
  have h : ((childLL (childHH thetaAboveCell01112201))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell01112201)) h
theorem e24KC2ThetaAboveLeaf0111220131 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell01112201)) = true := by
  have h : ((childLH (childHH thetaAboveCell01112201))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell01112201)) h
theorem e24KC2ThetaAboveLeaf0111220132 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell01112201)) = true := by
  have h : ((childHL (childHH thetaAboveCell01112201))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH thetaAboveCell01112201)) h
theorem e24KC2ThetaAboveLeaf0111220133 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell01112201)) = true := by
  have h : ((childHH (childHH thetaAboveCell01112201))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH thetaAboveCell01112201)) h
theorem e24KC2ThetaAboveLeaf0111220200 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell01112202)) = true := by
  have h : ((childLL (childLL thetaAboveCell01112202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell01112202)) h
theorem e24KC2ThetaAboveLeaf0111220201 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell01112202)) = true := by
  have h : ((childLH (childLL thetaAboveCell01112202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell01112202)) h
theorem e24KC2ThetaAboveLeaf0111220202 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell01112202)) = true := by
  have h : ((childHL (childLL thetaAboveCell01112202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell01112202)) h
theorem e24KC2ThetaAboveLeaf0111220203 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell01112202)) = true := by
  have h : ((childHH (childLL thetaAboveCell01112202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell01112202)) h
theorem e24KC2ThetaAboveLeaf0111220210 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell01112202)) = true := by
  have h : ((childLL (childLH thetaAboveCell01112202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell01112202)) h
theorem e24KC2ThetaAboveLeaf0111220211 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell01112202)) = true := by
  have h : ((childLH (childLH thetaAboveCell01112202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell01112202)) h
theorem e24KC2ThetaAboveLeaf0111220212 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell01112202)) = true := by
  have h : ((childHL (childLH thetaAboveCell01112202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell01112202)) h
theorem e24KC2ThetaAboveLeaf0111220213 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell01112202)) = true := by
  have h : ((childHH (childLH thetaAboveCell01112202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell01112202)) h
theorem e24KC2ThetaAboveLeaf0111220220 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell01112202)) = true := by
  have h : ((childLL (childHL thetaAboveCell01112202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell01112202)) h
theorem e24KC2ThetaAboveLeaf0111220221 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell01112202)) = true := by
  have h : ((childLH (childHL thetaAboveCell01112202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell01112202)) h
theorem e24KC2ThetaAboveLeaf0111220222 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell01112202)) = true := by
  have h : ((childHL (childHL thetaAboveCell01112202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL thetaAboveCell01112202)) h
theorem e24KC2ThetaAboveLeaf0111220223 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell01112202)) = true := by
  have h : ((childHH (childHL thetaAboveCell01112202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL thetaAboveCell01112202)) h
theorem e24KC2ThetaAboveLeaf0111220230 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell01112202)) = true := by
  have h : ((childLL (childHH thetaAboveCell01112202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell01112202)) h
theorem e24KC2ThetaAboveLeaf0111220231 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell01112202)) = true := by
  have h : ((childLH (childHH thetaAboveCell01112202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell01112202)) h
theorem e24KC2ThetaAboveLeaf0111220232 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell01112202)) = true := by
  have h : ((childHL (childHH thetaAboveCell01112202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH thetaAboveCell01112202)) h
theorem e24KC2ThetaAboveLeaf0111220233 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell01112202)) = true := by
  have h : ((childHH (childHH thetaAboveCell01112202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH thetaAboveCell01112202)) h
theorem e24KC2ThetaAboveLeaf0111220300 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell01112203)) = true := by
  have h : ((childLL (childLL thetaAboveCell01112203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell01112203)) h
theorem e24KC2ThetaAboveLeaf0111220301 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell01112203)) = true := by
  have h : ((childLH (childLL thetaAboveCell01112203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell01112203)) h
theorem e24KC2ThetaAboveLeaf0111220302 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell01112203)) = true := by
  have h : ((childHL (childLL thetaAboveCell01112203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell01112203)) h
theorem e24KC2ThetaAboveLeaf0111220303 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell01112203)) = true := by
  have h : ((childHH (childLL thetaAboveCell01112203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell01112203)) h
theorem e24KC2ThetaAboveLeaf0111220310 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell01112203)) = true := by
  have h : ((childLL (childLH thetaAboveCell01112203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell01112203)) h
theorem e24KC2ThetaAboveLeaf0111220311 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell01112203)) = true := by
  have h : ((childLH (childLH thetaAboveCell01112203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell01112203)) h
theorem e24KC2ThetaAboveLeaf0111220312 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell01112203)) = true := by
  have h : ((childHL (childLH thetaAboveCell01112203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell01112203)) h
theorem e24KC2ThetaAboveLeaf0111220313 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell01112203)) = true := by
  have h : ((childHH (childLH thetaAboveCell01112203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell01112203)) h
theorem e24KC2ThetaAboveLeaf0111220320 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell01112203)) = true := by
  have h : ((childLL (childHL thetaAboveCell01112203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell01112203)) h
theorem e24KC2ThetaAboveLeaf0111220321 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell01112203)) = true := by
  have h : ((childLH (childHL thetaAboveCell01112203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell01112203)) h
theorem e24KC2ThetaAboveLeaf0111220322 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell01112203)) = true := by
  have h : ((childHL (childHL thetaAboveCell01112203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL thetaAboveCell01112203)) h
theorem e24KC2ThetaAboveLeaf0111220323 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell01112203)) = true := by
  have h : ((childHH (childHL thetaAboveCell01112203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL thetaAboveCell01112203)) h
theorem e24KC2ThetaAboveLeaf0111220330 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell01112203)) = true := by
  have h : ((childLL (childHH thetaAboveCell01112203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell01112203)) h
theorem e24KC2ThetaAboveLeaf0111220331 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell01112203)) = true := by
  have h : ((childLH (childHH thetaAboveCell01112203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell01112203)) h
theorem e24KC2ThetaAboveLeaf0111220332 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell01112203)) = true := by
  have h : ((childHL (childHH thetaAboveCell01112203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH thetaAboveCell01112203)) h
theorem e24KC2ThetaAboveLeaf0111220333 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell01112203)) = true := by
  have h : ((childHH (childHH thetaAboveCell01112203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH thetaAboveCell01112203)) h
theorem e24KC2ThetaAboveLeaf011122100 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell01112210) = true := by
  have h : ((childLL thetaAboveCell01112210)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell01112210) h
theorem e24KC2ThetaAboveLeaf011122101 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell01112210) = true := by
  have h : ((childLH thetaAboveCell01112210)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell01112210) h
theorem e24KC2ThetaAboveLeaf0111221020 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell01112210)) = true := by
  have h : ((childLL (childHL thetaAboveCell01112210))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell01112210)) h
theorem e24KC2ThetaAboveLeaf0111221021 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell01112210)) = true := by
  have h : ((childLH (childHL thetaAboveCell01112210))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell01112210)) h
theorem e24KC2ThetaAboveLeaf0111221022 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell01112210)) = true := by
  have h : ((childHL (childHL thetaAboveCell01112210))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL thetaAboveCell01112210)) h
theorem e24KC2ThetaAboveLeaf0111221023 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell01112210)) = true := by
  have h : ((childHH (childHL thetaAboveCell01112210))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL thetaAboveCell01112210)) h
theorem e24KC2ThetaAboveLeaf0111221030 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell01112210)) = true := by
  have h : ((childLL (childHH thetaAboveCell01112210))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell01112210)) h
theorem e24KC2ThetaAboveLeaf0111221031 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell01112210)) = true := by
  have h : ((childLH (childHH thetaAboveCell01112210))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell01112210)) h
theorem e24KC2ThetaAboveLeaf0111221032 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell01112210)) = true := by
  have h : ((childHL (childHH thetaAboveCell01112210))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH thetaAboveCell01112210)) h
theorem e24KC2ThetaAboveLeaf0111221033 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell01112210)) = true := by
  have h : ((childHH (childHH thetaAboveCell01112210))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH thetaAboveCell01112210)) h
theorem e24KC2ThetaAboveLeaf011122110 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell01112211) = true := by
  have h : ((childLL thetaAboveCell01112211)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell01112211) h
theorem e24KC2ThetaAboveLeaf011122111 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell01112211) = true := by
  have h : ((childLH thetaAboveCell01112211)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell01112211) h
theorem e24KC2ThetaAboveLeaf0111221120 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell01112211)) = true := by
  have h : ((childLL (childHL thetaAboveCell01112211))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell01112211)) h
theorem e24KC2ThetaAboveLeaf0111221121 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell01112211)) = true := by
  have h : ((childLH (childHL thetaAboveCell01112211))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell01112211)) h
theorem e24KC2ThetaAboveLeaf0111221122 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell01112211)) = true := by
  have h : ((childHL (childHL thetaAboveCell01112211))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL thetaAboveCell01112211)) h
theorem e24KC2ThetaAboveLeaf0111221123 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell01112211)) = true := by
  have h : ((childHH (childHL thetaAboveCell01112211))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL thetaAboveCell01112211)) h
theorem e24KC2ThetaAboveLeaf0111221130 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell01112211)) = true := by
  have h : ((childLL (childHH thetaAboveCell01112211))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell01112211)) h
theorem e24KC2ThetaAboveLeaf0111221131 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell01112211)) = true := by
  have h : ((childLH (childHH thetaAboveCell01112211))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell01112211)) h
theorem e24KC2ThetaAboveLeaf0111221132 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell01112211)) = true := by
  have h : ((childHL (childHH thetaAboveCell01112211))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH thetaAboveCell01112211)) h
theorem e24KC2ThetaAboveLeaf0111221133 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell01112211)) = true := by
  have h : ((childHH (childHH thetaAboveCell01112211))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH thetaAboveCell01112211)) h
theorem e24KC2ThetaAboveLeaf0111221200 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell01112212)) = true := by
  have h : ((childLL (childLL thetaAboveCell01112212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell01112212)) h
theorem e24KC2ThetaAboveLeaf0111221201 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell01112212)) = true := by
  have h : ((childLH (childLL thetaAboveCell01112212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell01112212)) h
theorem e24KC2ThetaAboveLeaf0111221202 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell01112212)) = true := by
  have h : ((childHL (childLL thetaAboveCell01112212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell01112212)) h
theorem e24KC2ThetaAboveLeaf0111221203 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell01112212)) = true := by
  have h : ((childHH (childLL thetaAboveCell01112212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell01112212)) h
theorem e24KC2ThetaAboveLeaf0111221210 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell01112212)) = true := by
  have h : ((childLL (childLH thetaAboveCell01112212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell01112212)) h
theorem e24KC2ThetaAboveLeaf0111221211 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell01112212)) = true := by
  have h : ((childLH (childLH thetaAboveCell01112212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell01112212)) h
theorem e24KC2ThetaAboveLeaf0111221212 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell01112212)) = true := by
  have h : ((childHL (childLH thetaAboveCell01112212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell01112212)) h
theorem e24KC2ThetaAboveLeaf0111221213 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell01112212)) = true := by
  have h : ((childHH (childLH thetaAboveCell01112212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell01112212)) h
theorem e24KC2ThetaAboveLeaf0111221220 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell01112212)) = true := by
  have h : ((childLL (childHL thetaAboveCell01112212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell01112212)) h
theorem e24KC2ThetaAboveLeaf0111221221 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell01112212)) = true := by
  have h : ((childLH (childHL thetaAboveCell01112212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell01112212)) h
theorem e24KC2ThetaAboveLeaf0111221222 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell01112212)) = true := by
  have h : ((childHL (childHL thetaAboveCell01112212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL thetaAboveCell01112212)) h
theorem e24KC2ThetaAboveLeaf0111221223 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell01112212)) = true := by
  have h : ((childHH (childHL thetaAboveCell01112212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL thetaAboveCell01112212)) h
theorem e24KC2ThetaAboveLeaf0111221230 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell01112212)) = true := by
  have h : ((childLL (childHH thetaAboveCell01112212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell01112212)) h
theorem e24KC2ThetaAboveLeaf0111221231 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell01112212)) = true := by
  have h : ((childLH (childHH thetaAboveCell01112212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell01112212)) h
theorem e24KC2ThetaAboveLeaf0111221232 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell01112212)) = true := by
  have h : ((childHL (childHH thetaAboveCell01112212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH thetaAboveCell01112212)) h
theorem e24KC2ThetaAboveLeaf0111221233 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell01112212)) = true := by
  have h : ((childHH (childHH thetaAboveCell01112212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH thetaAboveCell01112212)) h
theorem e24KC2ThetaAboveLeaf0111221300 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell01112213)) = true := by
  have h : ((childLL (childLL thetaAboveCell01112213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell01112213)) h
theorem e24KC2ThetaAboveLeaf0111221301 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell01112213)) = true := by
  have h : ((childLH (childLL thetaAboveCell01112213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell01112213)) h
theorem e24KC2ThetaAboveLeaf0111221302 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell01112213)) = true := by
  have h : ((childHL (childLL thetaAboveCell01112213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell01112213)) h
theorem e24KC2ThetaAboveLeaf0111221303 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell01112213)) = true := by
  have h : ((childHH (childLL thetaAboveCell01112213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell01112213)) h
theorem e24KC2ThetaAboveLeaf0111221310 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell01112213)) = true := by
  have h : ((childLL (childLH thetaAboveCell01112213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell01112213)) h
theorem e24KC2ThetaAboveLeaf0111221311 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell01112213)) = true := by
  have h : ((childLH (childLH thetaAboveCell01112213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell01112213)) h
theorem e24KC2ThetaAboveLeaf0111221312 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell01112213)) = true := by
  have h : ((childHL (childLH thetaAboveCell01112213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell01112213)) h
theorem e24KC2ThetaAboveLeaf0111221313 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell01112213)) = true := by
  have h : ((childHH (childLH thetaAboveCell01112213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell01112213)) h
theorem e24KC2ThetaAboveLeaf0111221320 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell01112213)) = true := by
  have h : ((childLL (childHL thetaAboveCell01112213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell01112213)) h
theorem e24KC2ThetaAboveLeaf0111221321 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell01112213)) = true := by
  have h : ((childLH (childHL thetaAboveCell01112213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell01112213)) h
theorem e24KC2ThetaAboveLeaf0111221322 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell01112213)) = true := by
  have h : ((childHL (childHL thetaAboveCell01112213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL thetaAboveCell01112213)) h
theorem e24KC2ThetaAboveLeaf0111221323 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell01112213)) = true := by
  have h : ((childHH (childHL thetaAboveCell01112213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL thetaAboveCell01112213)) h
theorem e24KC2ThetaAboveLeaf0111221330 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell01112213)) = true := by
  have h : ((childLL (childHH thetaAboveCell01112213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell01112213)) h
theorem e24KC2ThetaAboveLeaf0111221331 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell01112213)) = true := by
  have h : ((childLH (childHH thetaAboveCell01112213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell01112213)) h
theorem e24KC2ThetaAboveLeaf0111221332 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell01112213)) = true := by
  have h : ((childHL (childHH thetaAboveCell01112213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH thetaAboveCell01112213)) h
theorem e24KC2ThetaAboveLeaf0111221333 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell01112213)) = true := by
  have h : ((childHH (childHH thetaAboveCell01112213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH thetaAboveCell01112213)) h
theorem e24KC2ThetaAboveLeaf011122200 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell01112220) = true := by
  have h : ((childLL thetaAboveCell01112220)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell01112220) h
theorem e24KC2ThetaAboveLeaf011122201 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell01112220) = true := by
  have h : ((childLH thetaAboveCell01112220)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell01112220) h
theorem e24KC2ThetaAboveLeaf011122202 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell01112220) = true := by
  have h : ((childHL thetaAboveCell01112220)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell01112220) h
theorem e24KC2ThetaAboveLeaf011122203 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell01112220) = true := by
  have h : ((childHH thetaAboveCell01112220)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell01112220) h
theorem e24KC2ThetaAboveLeaf011122210 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell01112221) = true := by
  have h : ((childLL thetaAboveCell01112221)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell01112221) h
theorem e24KC2ThetaAboveLeaf011122211 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell01112221) = true := by
  have h : ((childLH thetaAboveCell01112221)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell01112221) h
theorem e24KC2ThetaAboveLeaf011122212 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell01112221) = true := by
  have h : ((childHL thetaAboveCell01112221)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell01112221) h
theorem e24KC2ThetaAboveLeaf011122213 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell01112221) = true := by
  have h : ((childHH thetaAboveCell01112221)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell01112221) h
theorem e24KC2ThetaAboveLeaf01112222 :
    adaptiveCoverCheck 11 thetaAboveCell01112222 = true := by
  have h : (thetaAboveCell01112222).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01112222 h
theorem e24KC2ThetaAboveLeaf01112223 :
    adaptiveCoverCheck 11 thetaAboveCell01112223 = true := by
  have h : (thetaAboveCell01112223).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01112223 h
theorem e24KC2ThetaAboveLeaf011122300 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell01112230) = true := by
  have h : ((childLL thetaAboveCell01112230)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell01112230) h
theorem e24KC2ThetaAboveLeaf011122301 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell01112230) = true := by
  have h : ((childLH thetaAboveCell01112230)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell01112230) h
theorem e24KC2ThetaAboveLeaf011122302 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell01112230) = true := by
  have h : ((childHL thetaAboveCell01112230)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell01112230) h
theorem e24KC2ThetaAboveLeaf011122303 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell01112230) = true := by
  have h : ((childHH thetaAboveCell01112230)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell01112230) h
theorem e24KC2ThetaAboveLeaf011122310 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell01112231) = true := by
  have h : ((childLL thetaAboveCell01112231)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell01112231) h
theorem e24KC2ThetaAboveLeaf011122311 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell01112231) = true := by
  have h : ((childLH thetaAboveCell01112231)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell01112231) h
theorem e24KC2ThetaAboveLeaf011122312 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell01112231) = true := by
  have h : ((childHL thetaAboveCell01112231)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell01112231) h
theorem e24KC2ThetaAboveLeaf011122313 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell01112231) = true := by
  have h : ((childHH thetaAboveCell01112231)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell01112231) h
theorem e24KC2ThetaAboveLeaf01112232 :
    adaptiveCoverCheck 11 thetaAboveCell01112232 = true := by
  have h : (thetaAboveCell01112232).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01112232 h
theorem e24KC2ThetaAboveLeaf01112233 :
    adaptiveCoverCheck 11 thetaAboveCell01112233 = true := by
  have h : (thetaAboveCell01112233).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01112233 h
theorem e24KC2ThetaAboveLeaf011123000 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell01112300) = true := by
  have h : ((childLL thetaAboveCell01112300)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell01112300) h
theorem e24KC2ThetaAboveLeaf011123001 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell01112300) = true := by
  have h : ((childLH thetaAboveCell01112300)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell01112300) h
theorem e24KC2ThetaAboveLeaf0111230020 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell01112300)) = true := by
  have h : ((childLL (childHL thetaAboveCell01112300))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell01112300)) h
theorem e24KC2ThetaAboveLeaf0111230021 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell01112300)) = true := by
  have h : ((childLH (childHL thetaAboveCell01112300))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell01112300)) h
theorem e24KC2ThetaAboveLeaf0111230022 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell01112300)) = true := by
  have h : ((childHL (childHL thetaAboveCell01112300))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL thetaAboveCell01112300)) h
theorem e24KC2ThetaAboveLeaf0111230023 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell01112300)) = true := by
  have h : ((childHH (childHL thetaAboveCell01112300))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL thetaAboveCell01112300)) h
theorem e24KC2ThetaAboveLeaf0111230030 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell01112300)) = true := by
  have h : ((childLL (childHH thetaAboveCell01112300))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell01112300)) h
theorem e24KC2ThetaAboveLeaf0111230031 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell01112300)) = true := by
  have h : ((childLH (childHH thetaAboveCell01112300))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell01112300)) h
theorem e24KC2ThetaAboveLeaf0111230032 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell01112300)) = true := by
  have h : ((childHL (childHH thetaAboveCell01112300))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH thetaAboveCell01112300)) h
theorem e24KC2ThetaAboveLeaf0111230033 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell01112300)) = true := by
  have h : ((childHH (childHH thetaAboveCell01112300))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH thetaAboveCell01112300)) h
theorem e24KC2ThetaAboveLeaf011123010 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell01112301) = true := by
  have h : ((childLL thetaAboveCell01112301)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell01112301) h
theorem e24KC2ThetaAboveLeaf011123011 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell01112301) = true := by
  have h : ((childLH thetaAboveCell01112301)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell01112301) h
theorem e24KC2ThetaAboveLeaf0111230120 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell01112301)) = true := by
  have h : ((childLL (childHL thetaAboveCell01112301))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell01112301)) h
theorem e24KC2ThetaAboveLeaf0111230121 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell01112301)) = true := by
  have h : ((childLH (childHL thetaAboveCell01112301))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell01112301)) h
theorem e24KC2ThetaAboveLeaf0111230122 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell01112301)) = true := by
  have h : ((childHL (childHL thetaAboveCell01112301))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL thetaAboveCell01112301)) h
theorem e24KC2ThetaAboveLeaf0111230123 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell01112301)) = true := by
  have h : ((childHH (childHL thetaAboveCell01112301))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL thetaAboveCell01112301)) h
theorem e24KC2ThetaAboveLeaf0111230130 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell01112301)) = true := by
  have h : ((childLL (childHH thetaAboveCell01112301))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell01112301)) h
theorem e24KC2ThetaAboveLeaf0111230131 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell01112301)) = true := by
  have h : ((childLH (childHH thetaAboveCell01112301))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell01112301)) h
theorem e24KC2ThetaAboveLeaf0111230132 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell01112301)) = true := by
  have h : ((childHL (childHH thetaAboveCell01112301))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH thetaAboveCell01112301)) h
theorem e24KC2ThetaAboveLeaf0111230133 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell01112301)) = true := by
  have h : ((childHH (childHH thetaAboveCell01112301))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH thetaAboveCell01112301)) h
theorem e24KC2ThetaAboveLeaf0111230200 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell01112302)) = true := by
  have h : ((childLL (childLL thetaAboveCell01112302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell01112302)) h
theorem e24KC2ThetaAboveLeaf0111230201 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell01112302)) = true := by
  have h : ((childLH (childLL thetaAboveCell01112302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell01112302)) h
theorem e24KC2ThetaAboveLeaf0111230202 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell01112302)) = true := by
  have h : ((childHL (childLL thetaAboveCell01112302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell01112302)) h
theorem e24KC2ThetaAboveLeaf0111230203 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell01112302)) = true := by
  have h : ((childHH (childLL thetaAboveCell01112302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell01112302)) h
theorem e24KC2ThetaAboveLeaf0111230210 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell01112302)) = true := by
  have h : ((childLL (childLH thetaAboveCell01112302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell01112302)) h
theorem e24KC2ThetaAboveLeaf0111230211 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell01112302)) = true := by
  have h : ((childLH (childLH thetaAboveCell01112302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell01112302)) h
theorem e24KC2ThetaAboveLeaf0111230212 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell01112302)) = true := by
  have h : ((childHL (childLH thetaAboveCell01112302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell01112302)) h
theorem e24KC2ThetaAboveLeaf0111230213 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell01112302)) = true := by
  have h : ((childHH (childLH thetaAboveCell01112302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell01112302)) h
theorem e24KC2ThetaAboveLeaf0111230220 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell01112302)) = true := by
  have h : ((childLL (childHL thetaAboveCell01112302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell01112302)) h
theorem e24KC2ThetaAboveLeaf0111230221 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell01112302)) = true := by
  have h : ((childLH (childHL thetaAboveCell01112302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell01112302)) h
theorem e24KC2ThetaAboveLeaf0111230222 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell01112302)) = true := by
  have h : ((childHL (childHL thetaAboveCell01112302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL thetaAboveCell01112302)) h
theorem e24KC2ThetaAboveLeaf0111230223 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell01112302)) = true := by
  have h : ((childHH (childHL thetaAboveCell01112302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL thetaAboveCell01112302)) h
theorem e24KC2ThetaAboveLeaf0111230230 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell01112302)) = true := by
  have h : ((childLL (childHH thetaAboveCell01112302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell01112302)) h
theorem e24KC2ThetaAboveLeaf0111230231 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell01112302)) = true := by
  have h : ((childLH (childHH thetaAboveCell01112302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell01112302)) h
theorem e24KC2ThetaAboveLeaf0111230232 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell01112302)) = true := by
  have h : ((childHL (childHH thetaAboveCell01112302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH thetaAboveCell01112302)) h
theorem e24KC2ThetaAboveLeaf0111230233 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell01112302)) = true := by
  have h : ((childHH (childHH thetaAboveCell01112302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH thetaAboveCell01112302)) h
theorem e24KC2ThetaAboveLeaf0111230300 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell01112303)) = true := by
  have h : ((childLL (childLL thetaAboveCell01112303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell01112303)) h
theorem e24KC2ThetaAboveLeaf0111230301 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell01112303)) = true := by
  have h : ((childLH (childLL thetaAboveCell01112303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell01112303)) h
theorem e24KC2ThetaAboveLeaf0111230302 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell01112303)) = true := by
  have h : ((childHL (childLL thetaAboveCell01112303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell01112303)) h
theorem e24KC2ThetaAboveLeaf0111230303 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell01112303)) = true := by
  have h : ((childHH (childLL thetaAboveCell01112303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell01112303)) h
theorem e24KC2ThetaAboveLeaf0111230310 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell01112303)) = true := by
  have h : ((childLL (childLH thetaAboveCell01112303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell01112303)) h
theorem e24KC2ThetaAboveLeaf0111230311 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell01112303)) = true := by
  have h : ((childLH (childLH thetaAboveCell01112303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell01112303)) h
theorem e24KC2ThetaAboveLeaf0111230312 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell01112303)) = true := by
  have h : ((childHL (childLH thetaAboveCell01112303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell01112303)) h
theorem e24KC2ThetaAboveLeaf0111230313 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell01112303)) = true := by
  have h : ((childHH (childLH thetaAboveCell01112303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell01112303)) h
theorem e24KC2ThetaAboveLeaf0111230320 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell01112303)) = true := by
  have h : ((childLL (childHL thetaAboveCell01112303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell01112303)) h
theorem e24KC2ThetaAboveLeaf0111230321 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell01112303)) = true := by
  have h : ((childLH (childHL thetaAboveCell01112303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell01112303)) h
theorem e24KC2ThetaAboveLeaf0111230322 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell01112303)) = true := by
  have h : ((childHL (childHL thetaAboveCell01112303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL thetaAboveCell01112303)) h
theorem e24KC2ThetaAboveLeaf0111230323 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell01112303)) = true := by
  have h : ((childHH (childHL thetaAboveCell01112303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL thetaAboveCell01112303)) h
theorem e24KC2ThetaAboveLeaf0111230330 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell01112303)) = true := by
  have h : ((childLL (childHH thetaAboveCell01112303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell01112303)) h
theorem e24KC2ThetaAboveLeaf0111230331 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell01112303)) = true := by
  have h : ((childLH (childHH thetaAboveCell01112303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell01112303)) h
theorem e24KC2ThetaAboveLeaf0111230332 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell01112303)) = true := by
  have h : ((childHL (childHH thetaAboveCell01112303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH thetaAboveCell01112303)) h
theorem e24KC2ThetaAboveLeaf0111230333 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell01112303)) = true := by
  have h : ((childHH (childHH thetaAboveCell01112303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH thetaAboveCell01112303)) h
theorem e24KC2ThetaAboveLeaf011123100 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell01112310) = true := by
  have h : ((childLL thetaAboveCell01112310)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell01112310) h
theorem e24KC2ThetaAboveLeaf011123101 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell01112310) = true := by
  have h : ((childLH thetaAboveCell01112310)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell01112310) h
theorem e24KC2ThetaAboveLeaf0111231020 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell01112310)) = true := by
  have h : ((childLL (childHL thetaAboveCell01112310))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell01112310)) h
theorem e24KC2ThetaAboveLeaf0111231021 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell01112310)) = true := by
  have h : ((childLH (childHL thetaAboveCell01112310))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell01112310)) h
theorem e24KC2ThetaAboveLeaf0111231022 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell01112310)) = true := by
  have h : ((childHL (childHL thetaAboveCell01112310))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL thetaAboveCell01112310)) h
theorem e24KC2ThetaAboveLeaf0111231023 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell01112310)) = true := by
  have h : ((childHH (childHL thetaAboveCell01112310))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL thetaAboveCell01112310)) h
theorem e24KC2ThetaAboveLeaf0111231030 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell01112310)) = true := by
  have h : ((childLL (childHH thetaAboveCell01112310))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell01112310)) h
theorem e24KC2ThetaAboveLeaf0111231031 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell01112310)) = true := by
  have h : ((childLH (childHH thetaAboveCell01112310))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell01112310)) h
theorem e24KC2ThetaAboveLeaf0111231032 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell01112310)) = true := by
  have h : ((childHL (childHH thetaAboveCell01112310))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH thetaAboveCell01112310)) h
theorem e24KC2ThetaAboveLeaf0111231033 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell01112310)) = true := by
  have h : ((childHH (childHH thetaAboveCell01112310))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH thetaAboveCell01112310)) h
theorem e24KC2ThetaAboveLeaf011123110 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell01112311) = true := by
  have h : ((childLL thetaAboveCell01112311)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell01112311) h
theorem e24KC2ThetaAboveLeaf011123111 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell01112311) = true := by
  have h : ((childLH thetaAboveCell01112311)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell01112311) h
theorem e24KC2ThetaAboveLeaf0111231120 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell01112311)) = true := by
  have h : ((childLL (childHL thetaAboveCell01112311))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell01112311)) h
theorem e24KC2ThetaAboveLeaf0111231121 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell01112311)) = true := by
  have h : ((childLH (childHL thetaAboveCell01112311))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell01112311)) h
theorem e24KC2ThetaAboveLeaf0111231122 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell01112311)) = true := by
  have h : ((childHL (childHL thetaAboveCell01112311))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL thetaAboveCell01112311)) h
theorem e24KC2ThetaAboveLeaf0111231123 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell01112311)) = true := by
  have h : ((childHH (childHL thetaAboveCell01112311))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL thetaAboveCell01112311)) h
theorem e24KC2ThetaAboveLeaf0111231130 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell01112311)) = true := by
  have h : ((childLL (childHH thetaAboveCell01112311))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell01112311)) h
theorem e24KC2ThetaAboveLeaf0111231131 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell01112311)) = true := by
  have h : ((childLH (childHH thetaAboveCell01112311))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell01112311)) h
theorem e24KC2ThetaAboveLeaf0111231132 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell01112311)) = true := by
  have h : ((childHL (childHH thetaAboveCell01112311))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH thetaAboveCell01112311)) h
theorem e24KC2ThetaAboveLeaf0111231133 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell01112311)) = true := by
  have h : ((childHH (childHH thetaAboveCell01112311))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH thetaAboveCell01112311)) h
theorem e24KC2ThetaAboveLeaf0111231200 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell01112312)) = true := by
  have h : ((childLL (childLL thetaAboveCell01112312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell01112312)) h
theorem e24KC2ThetaAboveLeaf0111231201 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell01112312)) = true := by
  have h : ((childLH (childLL thetaAboveCell01112312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell01112312)) h
theorem e24KC2ThetaAboveLeaf0111231202 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell01112312)) = true := by
  have h : ((childHL (childLL thetaAboveCell01112312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell01112312)) h
theorem e24KC2ThetaAboveLeaf0111231203 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell01112312)) = true := by
  have h : ((childHH (childLL thetaAboveCell01112312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell01112312)) h
theorem e24KC2ThetaAboveLeaf0111231210 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell01112312)) = true := by
  have h : ((childLL (childLH thetaAboveCell01112312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell01112312)) h
theorem e24KC2ThetaAboveLeaf0111231211 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell01112312)) = true := by
  have h : ((childLH (childLH thetaAboveCell01112312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell01112312)) h
theorem e24KC2ThetaAboveLeaf0111231212 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell01112312)) = true := by
  have h : ((childHL (childLH thetaAboveCell01112312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell01112312)) h
theorem e24KC2ThetaAboveLeaf0111231213 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell01112312)) = true := by
  have h : ((childHH (childLH thetaAboveCell01112312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell01112312)) h
theorem e24KC2ThetaAboveLeaf0111231220 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell01112312)) = true := by
  have h : ((childLL (childHL thetaAboveCell01112312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell01112312)) h
theorem e24KC2ThetaAboveLeaf0111231221 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell01112312)) = true := by
  have h : ((childLH (childHL thetaAboveCell01112312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell01112312)) h
theorem e24KC2ThetaAboveLeaf0111231222 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell01112312)) = true := by
  have h : ((childHL (childHL thetaAboveCell01112312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL thetaAboveCell01112312)) h
theorem e24KC2ThetaAboveLeaf0111231223 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell01112312)) = true := by
  have h : ((childHH (childHL thetaAboveCell01112312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL thetaAboveCell01112312)) h
theorem e24KC2ThetaAboveLeaf0111231230 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell01112312)) = true := by
  have h : ((childLL (childHH thetaAboveCell01112312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell01112312)) h
theorem e24KC2ThetaAboveLeaf0111231231 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell01112312)) = true := by
  have h : ((childLH (childHH thetaAboveCell01112312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell01112312)) h
theorem e24KC2ThetaAboveLeaf0111231232 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell01112312)) = true := by
  have h : ((childHL (childHH thetaAboveCell01112312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH thetaAboveCell01112312)) h
theorem e24KC2ThetaAboveLeaf0111231233 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell01112312)) = true := by
  have h : ((childHH (childHH thetaAboveCell01112312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH thetaAboveCell01112312)) h
theorem e24KC2ThetaAboveLeaf0111231300 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell01112313)) = true := by
  have h : ((childLL (childLL thetaAboveCell01112313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell01112313)) h
theorem e24KC2ThetaAboveLeaf0111231301 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell01112313)) = true := by
  have h : ((childLH (childLL thetaAboveCell01112313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell01112313)) h
theorem e24KC2ThetaAboveLeaf0111231302 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell01112313)) = true := by
  have h : ((childHL (childLL thetaAboveCell01112313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell01112313)) h
theorem e24KC2ThetaAboveLeaf0111231303 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell01112313)) = true := by
  have h : ((childHH (childLL thetaAboveCell01112313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell01112313)) h
theorem e24KC2ThetaAboveLeaf0111231310 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell01112313)) = true := by
  have h : ((childLL (childLH thetaAboveCell01112313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell01112313)) h
theorem e24KC2ThetaAboveLeaf0111231311 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell01112313)) = true := by
  have h : ((childLH (childLH thetaAboveCell01112313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell01112313)) h
theorem e24KC2ThetaAboveLeaf0111231312 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell01112313)) = true := by
  have h : ((childHL (childLH thetaAboveCell01112313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell01112313)) h
theorem e24KC2ThetaAboveLeaf0111231313 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell01112313)) = true := by
  have h : ((childHH (childLH thetaAboveCell01112313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell01112313)) h
theorem e24KC2ThetaAboveLeaf0111231320 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell01112313)) = true := by
  have h : ((childLL (childHL thetaAboveCell01112313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell01112313)) h
theorem e24KC2ThetaAboveLeaf0111231321 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell01112313)) = true := by
  have h : ((childLH (childHL thetaAboveCell01112313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell01112313)) h
theorem e24KC2ThetaAboveLeaf0111231322 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell01112313)) = true := by
  have h : ((childHL (childHL thetaAboveCell01112313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL thetaAboveCell01112313)) h
theorem e24KC2ThetaAboveLeaf0111231323 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell01112313)) = true := by
  have h : ((childHH (childHL thetaAboveCell01112313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL thetaAboveCell01112313)) h
theorem e24KC2ThetaAboveLeaf0111231330 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell01112313)) = true := by
  have h : ((childLL (childHH thetaAboveCell01112313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell01112313)) h
theorem e24KC2ThetaAboveLeaf0111231331 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell01112313)) = true := by
  have h : ((childLH (childHH thetaAboveCell01112313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell01112313)) h
theorem e24KC2ThetaAboveLeaf0111231332 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell01112313)) = true := by
  have h : ((childHL (childHH thetaAboveCell01112313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH thetaAboveCell01112313)) h
theorem e24KC2ThetaAboveLeaf0111231333 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell01112313)) = true := by
  have h : ((childHH (childHH thetaAboveCell01112313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH thetaAboveCell01112313)) h
theorem e24KC2ThetaAboveLeaf011123200 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell01112320) = true := by
  have h : ((childLL thetaAboveCell01112320)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell01112320) h
theorem e24KC2ThetaAboveLeaf011123201 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell01112320) = true := by
  have h : ((childLH thetaAboveCell01112320)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell01112320) h
theorem e24KC2ThetaAboveLeaf011123202 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell01112320) = true := by
  have h : ((childHL thetaAboveCell01112320)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell01112320) h
theorem e24KC2ThetaAboveLeaf011123203 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell01112320) = true := by
  have h : ((childHH thetaAboveCell01112320)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell01112320) h
theorem e24KC2ThetaAboveLeaf011123210 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell01112321) = true := by
  have h : ((childLL thetaAboveCell01112321)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell01112321) h
theorem e24KC2ThetaAboveLeaf011123211 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell01112321) = true := by
  have h : ((childLH thetaAboveCell01112321)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell01112321) h
theorem e24KC2ThetaAboveLeaf011123212 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell01112321) = true := by
  have h : ((childHL thetaAboveCell01112321)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell01112321) h
theorem e24KC2ThetaAboveLeaf011123213 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell01112321) = true := by
  have h : ((childHH thetaAboveCell01112321)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell01112321) h
theorem e24KC2ThetaAboveLeaf01112322 :
    adaptiveCoverCheck 11 thetaAboveCell01112322 = true := by
  have h : (thetaAboveCell01112322).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01112322 h
theorem e24KC2ThetaAboveLeaf01112323 :
    adaptiveCoverCheck 11 thetaAboveCell01112323 = true := by
  have h : (thetaAboveCell01112323).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01112323 h
theorem e24KC2ThetaAboveLeaf011123300 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell01112330) = true := by
  have h : ((childLL thetaAboveCell01112330)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell01112330) h
theorem e24KC2ThetaAboveLeaf011123301 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell01112330) = true := by
  have h : ((childLH thetaAboveCell01112330)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell01112330) h
theorem e24KC2ThetaAboveLeaf011123302 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell01112330) = true := by
  have h : ((childHL thetaAboveCell01112330)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell01112330) h
theorem e24KC2ThetaAboveLeaf011123303 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell01112330) = true := by
  have h : ((childHH thetaAboveCell01112330)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell01112330) h
theorem e24KC2ThetaAboveLeaf011123310 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell01112331) = true := by
  have h : ((childLL thetaAboveCell01112331)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell01112331) h
theorem e24KC2ThetaAboveLeaf011123311 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell01112331) = true := by
  have h : ((childLH thetaAboveCell01112331)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell01112331) h
theorem e24KC2ThetaAboveLeaf011123312 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell01112331) = true := by
  have h : ((childHL thetaAboveCell01112331)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell01112331) h
theorem e24KC2ThetaAboveLeaf011123313 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell01112331) = true := by
  have h : ((childHH thetaAboveCell01112331)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell01112331) h
theorem e24KC2ThetaAboveLeaf01112332 :
    adaptiveCoverCheck 11 thetaAboveCell01112332 = true := by
  have h : (thetaAboveCell01112332).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01112332 h
theorem e24KC2ThetaAboveLeaf01112333 :
    adaptiveCoverCheck 11 thetaAboveCell01112333 = true := by
  have h : (thetaAboveCell01112333).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01112333 h
theorem e24KC2ThetaAboveLeaf0111300 :
    adaptiveCoverCheck 12 (childLL (childLL (childHH thetaAboveCell0111))) = true := by
  have h : ((childLL (childLL (childHH thetaAboveCell0111)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLL (childHH thetaAboveCell0111))) h
theorem e24KC2ThetaAboveLeaf0111301 :
    adaptiveCoverCheck 12 (childLH (childLL (childHH thetaAboveCell0111))) = true := by
  have h : ((childLH (childLL (childHH thetaAboveCell0111)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLL (childHH thetaAboveCell0111))) h
theorem e24KC2ThetaAboveLeaf01113020 :
    adaptiveCoverCheck 11 thetaAboveCell01113020 = true := by
  have h : (thetaAboveCell01113020).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01113020 h
theorem e24KC2ThetaAboveLeaf01113021 :
    adaptiveCoverCheck 11 thetaAboveCell01113021 = true := by
  have h : (thetaAboveCell01113021).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01113021 h
theorem e24KC2ThetaAboveLeaf01113022 :
    adaptiveCoverCheck 11 thetaAboveCell01113022 = true := by
  have h : (thetaAboveCell01113022).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01113022 h
theorem e24KC2ThetaAboveLeaf01113023 :
    adaptiveCoverCheck 11 thetaAboveCell01113023 = true := by
  have h : (thetaAboveCell01113023).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01113023 h
theorem e24KC2ThetaAboveLeaf01113030 :
    adaptiveCoverCheck 11 thetaAboveCell01113030 = true := by
  have h : (thetaAboveCell01113030).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01113030 h
theorem e24KC2ThetaAboveLeaf01113031 :
    adaptiveCoverCheck 11 thetaAboveCell01113031 = true := by
  have h : (thetaAboveCell01113031).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01113031 h
theorem e24KC2ThetaAboveLeaf01113032 :
    adaptiveCoverCheck 11 thetaAboveCell01113032 = true := by
  have h : (thetaAboveCell01113032).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01113032 h
theorem e24KC2ThetaAboveLeaf01113033 :
    adaptiveCoverCheck 11 thetaAboveCell01113033 = true := by
  have h : (thetaAboveCell01113033).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01113033 h
theorem e24KC2ThetaAboveLeaf0111310 :
    adaptiveCoverCheck 12 (childLL (childLH (childHH thetaAboveCell0111))) = true := by
  have h : ((childLL (childLH (childHH thetaAboveCell0111)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLH (childHH thetaAboveCell0111))) h
theorem e24KC2ThetaAboveLeaf0111311 :
    adaptiveCoverCheck 12 (childLH (childLH (childHH thetaAboveCell0111))) = true := by
  have h : ((childLH (childLH (childHH thetaAboveCell0111)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLH (childHH thetaAboveCell0111))) h
theorem e24KC2ThetaAboveLeaf01113120 :
    adaptiveCoverCheck 11 thetaAboveCell01113120 = true := by
  have h : (thetaAboveCell01113120).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01113120 h
theorem e24KC2ThetaAboveLeaf01113121 :
    adaptiveCoverCheck 11 thetaAboveCell01113121 = true := by
  have h : (thetaAboveCell01113121).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01113121 h
theorem e24KC2ThetaAboveLeaf01113122 :
    adaptiveCoverCheck 11 thetaAboveCell01113122 = true := by
  have h : (thetaAboveCell01113122).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01113122 h
theorem e24KC2ThetaAboveLeaf01113123 :
    adaptiveCoverCheck 11 thetaAboveCell01113123 = true := by
  have h : (thetaAboveCell01113123).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01113123 h
theorem e24KC2ThetaAboveLeaf01113130 :
    adaptiveCoverCheck 11 thetaAboveCell01113130 = true := by
  have h : (thetaAboveCell01113130).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01113130 h
theorem e24KC2ThetaAboveLeaf01113131 :
    adaptiveCoverCheck 11 thetaAboveCell01113131 = true := by
  have h : (thetaAboveCell01113131).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01113131 h
theorem e24KC2ThetaAboveLeaf01113132 :
    adaptiveCoverCheck 11 thetaAboveCell01113132 = true := by
  have h : (thetaAboveCell01113132).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01113132 h
theorem e24KC2ThetaAboveLeaf01113133 :
    adaptiveCoverCheck 11 thetaAboveCell01113133 = true := by
  have h : (thetaAboveCell01113133).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01113133 h
theorem e24KC2ThetaAboveLeaf011132000 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell01113200) = true := by
  have h : ((childLL thetaAboveCell01113200)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell01113200) h
theorem e24KC2ThetaAboveLeaf011132001 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell01113200) = true := by
  have h : ((childLH thetaAboveCell01113200)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell01113200) h
theorem e24KC2ThetaAboveLeaf0111320020 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell01113200)) = true := by
  have h : ((childLL (childHL thetaAboveCell01113200))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell01113200)) h
theorem e24KC2ThetaAboveLeaf0111320021 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell01113200)) = true := by
  have h : ((childLH (childHL thetaAboveCell01113200))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell01113200)) h
theorem e24KC2ThetaAboveLeaf0111320022 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell01113200)) = true := by
  have h : ((childHL (childHL thetaAboveCell01113200))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL thetaAboveCell01113200)) h
theorem e24KC2ThetaAboveLeaf0111320023 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell01113200)) = true := by
  have h : ((childHH (childHL thetaAboveCell01113200))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL thetaAboveCell01113200)) h
theorem e24KC2ThetaAboveLeaf0111320030 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell01113200)) = true := by
  have h : ((childLL (childHH thetaAboveCell01113200))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell01113200)) h
theorem e24KC2ThetaAboveLeaf0111320031 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell01113200)) = true := by
  have h : ((childLH (childHH thetaAboveCell01113200))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell01113200)) h
theorem e24KC2ThetaAboveLeaf0111320032 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell01113200)) = true := by
  have h : ((childHL (childHH thetaAboveCell01113200))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH thetaAboveCell01113200)) h
theorem e24KC2ThetaAboveLeaf0111320033 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell01113200)) = true := by
  have h : ((childHH (childHH thetaAboveCell01113200))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH thetaAboveCell01113200)) h
theorem e24KC2ThetaAboveLeaf011132010 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell01113201) = true := by
  have h : ((childLL thetaAboveCell01113201)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell01113201) h
theorem e24KC2ThetaAboveLeaf011132011 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell01113201) = true := by
  have h : ((childLH thetaAboveCell01113201)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell01113201) h
theorem e24KC2ThetaAboveLeaf0111320120 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell01113201)) = true := by
  have h : ((childLL (childHL thetaAboveCell01113201))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell01113201)) h
theorem e24KC2ThetaAboveLeaf0111320121 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell01113201)) = true := by
  have h : ((childLH (childHL thetaAboveCell01113201))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell01113201)) h
theorem e24KC2ThetaAboveLeaf0111320122 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell01113201)) = true := by
  have h : ((childHL (childHL thetaAboveCell01113201))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL thetaAboveCell01113201)) h
theorem e24KC2ThetaAboveLeaf0111320123 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell01113201)) = true := by
  have h : ((childHH (childHL thetaAboveCell01113201))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL thetaAboveCell01113201)) h
theorem e24KC2ThetaAboveLeaf0111320130 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell01113201)) = true := by
  have h : ((childLL (childHH thetaAboveCell01113201))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell01113201)) h
theorem e24KC2ThetaAboveLeaf0111320131 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell01113201)) = true := by
  have h : ((childLH (childHH thetaAboveCell01113201))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell01113201)) h
theorem e24KC2ThetaAboveLeaf0111320132 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell01113201)) = true := by
  have h : ((childHL (childHH thetaAboveCell01113201))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH thetaAboveCell01113201)) h
theorem e24KC2ThetaAboveLeaf0111320133 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell01113201)) = true := by
  have h : ((childHH (childHH thetaAboveCell01113201))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH thetaAboveCell01113201)) h
theorem e24KC2ThetaAboveLeaf0111320200 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell01113202)) = true := by
  have h : ((childLL (childLL thetaAboveCell01113202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell01113202)) h
theorem e24KC2ThetaAboveLeaf0111320201 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell01113202)) = true := by
  have h : ((childLH (childLL thetaAboveCell01113202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell01113202)) h
theorem e24KC2ThetaAboveLeaf0111320202 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell01113202)) = true := by
  have h : ((childHL (childLL thetaAboveCell01113202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell01113202)) h
theorem e24KC2ThetaAboveLeaf0111320203 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell01113202)) = true := by
  have h : ((childHH (childLL thetaAboveCell01113202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell01113202)) h
theorem e24KC2ThetaAboveLeaf0111320210 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell01113202)) = true := by
  have h : ((childLL (childLH thetaAboveCell01113202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell01113202)) h
theorem e24KC2ThetaAboveLeaf0111320211 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell01113202)) = true := by
  have h : ((childLH (childLH thetaAboveCell01113202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell01113202)) h

end PartE
end GerverSofa

end

end

end

end

end

end

section

/-
Copyright (c) 2026 Dawid Trela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dawid Trela
-/
/-!
# Gerver sofa dependency batch

* `KernelOnly.PartE.E24KC6ProofBatchA7de3be3b4ab1789`.
* `KernelOnly.PartE.E24KC6ProofBatchAad74ad127e30429`.
-/

public section

noncomputable section

section

/-! E24KC6 explicit proof-producing certificate batch. -/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells37514173c1

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells37514173c1

open CertificateCells37514173c1
theorem e24KC2ThetaAboveLeaf0011331022 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell00113310)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHL thetaAboveCell00113310))
    (by
      have h : ((childLL (childHL (childHL thetaAboveCell00113310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHL
        thetaAboveCell00113310))) h)
    (by
      have h : ((childLH (childHL (childHL thetaAboveCell00113310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHL
        thetaAboveCell00113310))) h)
    (by
      have h : ((childHL (childHL (childHL thetaAboveCell00113310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHL
        thetaAboveCell00113310))) h)
    (by
      have h : ((childHH (childHL (childHL thetaAboveCell00113310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHL
        thetaAboveCell00113310))) h)
theorem e24KC2ThetaAboveLeaf0011331023 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell00113310)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHL thetaAboveCell00113310))
    (by
      have h : ((childLL (childHH (childHL thetaAboveCell00113310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHL
        thetaAboveCell00113310))) h)
    (by
      have h : ((childLH (childHH (childHL thetaAboveCell00113310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHL
        thetaAboveCell00113310))) h)
    (by
      have h : ((childHL (childHH (childHL thetaAboveCell00113310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHL
        thetaAboveCell00113310))) h)
    (by
      have h : ((childHH (childHH (childHL thetaAboveCell00113310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHL
        thetaAboveCell00113310))) h)
theorem e24KC2ThetaAboveLeaf0011331032 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell00113310)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHH thetaAboveCell00113310))
    (by
      have h : ((childLL (childHL (childHH thetaAboveCell00113310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHH
        thetaAboveCell00113310))) h)
    (by
      have h : ((childLH (childHL (childHH thetaAboveCell00113310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHH
        thetaAboveCell00113310))) h)
    (by
      have h : ((childHL (childHL (childHH thetaAboveCell00113310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHH
        thetaAboveCell00113310))) h)
    (by
      have h : ((childHH (childHL (childHH thetaAboveCell00113310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHH
        thetaAboveCell00113310))) h)
theorem e24KC2ThetaAboveLeaf0011331033 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell00113310)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHH thetaAboveCell00113310))
    (by
      have h : ((childLL (childHH (childHH thetaAboveCell00113310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHH
        thetaAboveCell00113310))) h)
    (by
      have h : ((childLH (childHH (childHH thetaAboveCell00113310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHH
        thetaAboveCell00113310))) h)
    (by
      have h : ((childHL (childHH (childHH thetaAboveCell00113310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHH
        thetaAboveCell00113310))) h)
    (by
      have h : ((childHH (childHH (childHH thetaAboveCell00113310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHH
        thetaAboveCell00113310))) h)
theorem e24KC2ThetaAboveLeaf0011331122 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell00113311)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHL thetaAboveCell00113311))
    (by
      have h : ((childLL (childHL (childHL thetaAboveCell00113311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHL
        thetaAboveCell00113311))) h)
    (by
      have h : ((childLH (childHL (childHL thetaAboveCell00113311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHL
        thetaAboveCell00113311))) h)
    (by
      have h : ((childHL (childHL (childHL thetaAboveCell00113311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHL
        thetaAboveCell00113311))) h)
    (by
      have h : ((childHH (childHL (childHL thetaAboveCell00113311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHL
        thetaAboveCell00113311))) h)
theorem e24KC2ThetaAboveLeaf0011331123 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell00113311)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHL thetaAboveCell00113311))
    (by
      have h : ((childLL (childHH (childHL thetaAboveCell00113311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHL
        thetaAboveCell00113311))) h)
    (by
      have h : ((childLH (childHH (childHL thetaAboveCell00113311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHL
        thetaAboveCell00113311))) h)
    (by
      have h : ((childHL (childHH (childHL thetaAboveCell00113311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHL
        thetaAboveCell00113311))) h)
    (by
      have h : ((childHH (childHH (childHL thetaAboveCell00113311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHL
        thetaAboveCell00113311))) h)
theorem e24KC2ThetaAboveLeaf0011331132 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell00113311)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHH thetaAboveCell00113311))
    (by
      have h : ((childLL (childHL (childHH thetaAboveCell00113311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHH
        thetaAboveCell00113311))) h)
    (by
      have h : ((childLH (childHL (childHH thetaAboveCell00113311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHH
        thetaAboveCell00113311))) h)
    (by
      have h : ((childHL (childHL (childHH thetaAboveCell00113311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHH
        thetaAboveCell00113311))) h)
    (by
      have h : ((childHH (childHL (childHH thetaAboveCell00113311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHH
        thetaAboveCell00113311))) h)
theorem e24KC2ThetaAboveLeaf0011331133 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell00113311)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHH thetaAboveCell00113311))
    (by
      have h : ((childLL (childHH (childHH thetaAboveCell00113311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHH
        thetaAboveCell00113311))) h)
    (by
      have h : ((childLH (childHH (childHH thetaAboveCell00113311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHH
        thetaAboveCell00113311))) h)
    (by
      have h : ((childHL (childHH (childHH thetaAboveCell00113311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHH
        thetaAboveCell00113311))) h)
    (by
      have h : ((childHH (childHH (childHH thetaAboveCell00113311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHH
        thetaAboveCell00113311))) h)
theorem e24KC2ThetaAboveLeaf0011331200 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell00113312)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childLL thetaAboveCell00113312))
    (by
      have h : ((childLL (childLL (childLL thetaAboveCell00113312)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childLL
        thetaAboveCell00113312))) h)
    (by
      have h : ((childLH (childLL (childLL thetaAboveCell00113312)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childLL
        thetaAboveCell00113312))) h)
    (by
      have h : ((childHL (childLL (childLL thetaAboveCell00113312)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childLL
        thetaAboveCell00113312))) h)
    (by
      have h : ((childHH (childLL (childLL thetaAboveCell00113312)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childLL
        thetaAboveCell00113312))) h)
theorem e24KC2ThetaAboveLeaf0011331201 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell00113312)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childLL thetaAboveCell00113312))
    (by
      have h : ((childLL (childLH (childLL thetaAboveCell00113312)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childLL
        thetaAboveCell00113312))) h)
    (by
      have h : ((childLH (childLH (childLL thetaAboveCell00113312)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childLL
        thetaAboveCell00113312))) h)
    (by
      have h : ((childHL (childLH (childLL thetaAboveCell00113312)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childLL
        thetaAboveCell00113312))) h)
    (by
      have h : ((childHH (childLH (childLL thetaAboveCell00113312)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childLL
        thetaAboveCell00113312))) h)
theorem e24KC2ThetaAboveLeaf0011331210 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell00113312)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childLH thetaAboveCell00113312))
    (by
      have h : ((childLL (childLL (childLH thetaAboveCell00113312)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childLH
        thetaAboveCell00113312))) h)
    (by
      have h : ((childLH (childLL (childLH thetaAboveCell00113312)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childLH
        thetaAboveCell00113312))) h)
    (by
      have h : ((childHL (childLL (childLH thetaAboveCell00113312)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childLH
        thetaAboveCell00113312))) h)
    (by
      have h : ((childHH (childLL (childLH thetaAboveCell00113312)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childLH
        thetaAboveCell00113312))) h)
theorem e24KC2ThetaAboveLeaf0011331211 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell00113312)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childLH thetaAboveCell00113312))
    (by
      have h : ((childLL (childLH (childLH thetaAboveCell00113312)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childLH
        thetaAboveCell00113312))) h)
    (by
      have h : ((childLH (childLH (childLH thetaAboveCell00113312)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childLH
        thetaAboveCell00113312))) h)
    (by
      have h : ((childHL (childLH (childLH thetaAboveCell00113312)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childLH
        thetaAboveCell00113312))) h)
    (by
      have h : ((childHH (childLH (childLH thetaAboveCell00113312)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childLH
        thetaAboveCell00113312))) h)
theorem e24KC2ThetaAboveLeaf0011331300 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell00113313)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childLL thetaAboveCell00113313))
    (by
      have h : ((childLL (childLL (childLL thetaAboveCell00113313)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childLL
        thetaAboveCell00113313))) h)
    (by
      have h : ((childLH (childLL (childLL thetaAboveCell00113313)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childLL
        thetaAboveCell00113313))) h)
    (by
      have h : ((childHL (childLL (childLL thetaAboveCell00113313)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childLL
        thetaAboveCell00113313))) h)
    (by
      have h : ((childHH (childLL (childLL thetaAboveCell00113313)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childLL
        thetaAboveCell00113313))) h)
theorem e24KC2ThetaAboveLeaf0011331301 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell00113313)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childLL thetaAboveCell00113313))
    (by
      have h : ((childLL (childLH (childLL thetaAboveCell00113313)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childLL
        thetaAboveCell00113313))) h)
    (by
      have h : ((childLH (childLH (childLL thetaAboveCell00113313)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childLL
        thetaAboveCell00113313))) h)
    (by
      have h : ((childHL (childLH (childLL thetaAboveCell00113313)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childLL
        thetaAboveCell00113313))) h)
    (by
      have h : ((childHH (childLH (childLL thetaAboveCell00113313)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childLL
        thetaAboveCell00113313))) h)
theorem e24KC2ThetaAboveLeaf0011331310 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell00113313)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childLH thetaAboveCell00113313))
    (by
      have h : ((childLL (childLL (childLH thetaAboveCell00113313)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childLH
        thetaAboveCell00113313))) h)
    (by
      have h : ((childLH (childLL (childLH thetaAboveCell00113313)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childLH
        thetaAboveCell00113313))) h)
    (by
      have h : ((childHL (childLL (childLH thetaAboveCell00113313)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childLH
        thetaAboveCell00113313))) h)
    (by
      have h : ((childHH (childLL (childLH thetaAboveCell00113313)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childLH
        thetaAboveCell00113313))) h)
theorem e24KC2ThetaAboveLeaf0011331311 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell00113313)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childLH thetaAboveCell00113313))
    (by
      have h : ((childLL (childLH (childLH thetaAboveCell00113313)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childLH
        thetaAboveCell00113313))) h)
    (by
      have h : ((childLH (childLH (childLH thetaAboveCell00113313)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childLH
        thetaAboveCell00113313))) h)
    (by
      have h : ((childHL (childLH (childLH thetaAboveCell00113313)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childLH
        thetaAboveCell00113313))) h)
    (by
      have h : ((childHH (childLH (childLH thetaAboveCell00113313)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childLH
        thetaAboveCell00113313))) h)
theorem e24KC2ThetaAboveLeaf0100220022 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell01002200)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHL thetaAboveCell01002200))
    (by
      have h : ((childLL (childHL (childHL thetaAboveCell01002200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHL
        thetaAboveCell01002200))) h)
    (by
      have h : ((childLH (childHL (childHL thetaAboveCell01002200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHL
        thetaAboveCell01002200))) h)
    (by
      have h : ((childHL (childHL (childHL thetaAboveCell01002200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHL
        thetaAboveCell01002200))) h)
    (by
      have h : ((childHH (childHL (childHL thetaAboveCell01002200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHL
        thetaAboveCell01002200))) h)
theorem e24KC2ThetaAboveLeaf0100220023 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell01002200)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHL thetaAboveCell01002200))
    (by
      have h : ((childLL (childHH (childHL thetaAboveCell01002200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHL
        thetaAboveCell01002200))) h)
    (by
      have h : ((childLH (childHH (childHL thetaAboveCell01002200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHL
        thetaAboveCell01002200))) h)
    (by
      have h : ((childHL (childHH (childHL thetaAboveCell01002200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHL
        thetaAboveCell01002200))) h)
    (by
      have h : ((childHH (childHH (childHL thetaAboveCell01002200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHL
        thetaAboveCell01002200))) h)
theorem e24KC2ThetaAboveLeaf0100220032 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell01002200)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHH thetaAboveCell01002200))
    (by
      have h : ((childLL (childHL (childHH thetaAboveCell01002200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHH
        thetaAboveCell01002200))) h)
    (by
      have h : ((childLH (childHL (childHH thetaAboveCell01002200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHH
        thetaAboveCell01002200))) h)
    (by
      have h : ((childHL (childHL (childHH thetaAboveCell01002200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHH
        thetaAboveCell01002200))) h)
    (by
      have h : ((childHH (childHL (childHH thetaAboveCell01002200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHH
        thetaAboveCell01002200))) h)
theorem e24KC2ThetaAboveLeaf0100220033 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell01002200)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHH thetaAboveCell01002200))
    (by
      have h : ((childLL (childHH (childHH thetaAboveCell01002200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHH
        thetaAboveCell01002200))) h)
    (by
      have h : ((childLH (childHH (childHH thetaAboveCell01002200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHH
        thetaAboveCell01002200))) h)
    (by
      have h : ((childHL (childHH (childHH thetaAboveCell01002200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHH
        thetaAboveCell01002200))) h)
    (by
      have h : ((childHH (childHH (childHH thetaAboveCell01002200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHH
        thetaAboveCell01002200))) h)
theorem e24KC2ThetaAboveLeaf0100220122 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell01002201)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHL thetaAboveCell01002201))
    (by
      have h : ((childLL (childHL (childHL thetaAboveCell01002201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHL
        thetaAboveCell01002201))) h)
    (by
      have h : ((childLH (childHL (childHL thetaAboveCell01002201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHL
        thetaAboveCell01002201))) h)
    (by
      have h : ((childHL (childHL (childHL thetaAboveCell01002201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHL
        thetaAboveCell01002201))) h)
    (by
      have h : ((childHH (childHL (childHL thetaAboveCell01002201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHL
        thetaAboveCell01002201))) h)
theorem e24KC2ThetaAboveLeaf0100220123 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell01002201)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHL thetaAboveCell01002201))
    (by
      have h : ((childLL (childHH (childHL thetaAboveCell01002201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHL
        thetaAboveCell01002201))) h)
    (by
      have h : ((childLH (childHH (childHL thetaAboveCell01002201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHL
        thetaAboveCell01002201))) h)
    (by
      have h : ((childHL (childHH (childHL thetaAboveCell01002201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHL
        thetaAboveCell01002201))) h)
    (by
      have h : ((childHH (childHH (childHL thetaAboveCell01002201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHL
        thetaAboveCell01002201))) h)
theorem e24KC2ThetaAboveLeaf0100220132 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell01002201)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHH thetaAboveCell01002201))
    (by
      have h : ((childLL (childHL (childHH thetaAboveCell01002201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHH
        thetaAboveCell01002201))) h)
    (by
      have h : ((childLH (childHL (childHH thetaAboveCell01002201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHH
        thetaAboveCell01002201))) h)
    (by
      have h : ((childHL (childHL (childHH thetaAboveCell01002201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHH
        thetaAboveCell01002201))) h)
    (by
      have h : ((childHH (childHL (childHH thetaAboveCell01002201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHH
        thetaAboveCell01002201))) h)
theorem e24KC2ThetaAboveLeaf0100220133 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell01002201)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHH thetaAboveCell01002201))
    (by
      have h : ((childLL (childHH (childHH thetaAboveCell01002201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHH
        thetaAboveCell01002201))) h)
    (by
      have h : ((childLH (childHH (childHH thetaAboveCell01002201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHH
        thetaAboveCell01002201))) h)
    (by
      have h : ((childHL (childHH (childHH thetaAboveCell01002201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHH
        thetaAboveCell01002201))) h)
    (by
      have h : ((childHH (childHH (childHH thetaAboveCell01002201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHH
        thetaAboveCell01002201))) h)
theorem e24KC2ThetaAboveLeaf0100220200 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell01002202)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childLL thetaAboveCell01002202))
    (by
      have h : ((childLL (childLL (childLL thetaAboveCell01002202)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childLL
        thetaAboveCell01002202))) h)
    (by
      have h : ((childLH (childLL (childLL thetaAboveCell01002202)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childLL
        thetaAboveCell01002202))) h)
    (by
      have h : ((childHL (childLL (childLL thetaAboveCell01002202)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childLL
        thetaAboveCell01002202))) h)
    (by
      have h : ((childHH (childLL (childLL thetaAboveCell01002202)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childLL
        thetaAboveCell01002202))) h)
theorem e24KC2ThetaAboveLeaf0100220201 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell01002202)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childLL thetaAboveCell01002202))
    (by
      have h : ((childLL (childLH (childLL thetaAboveCell01002202)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childLL
        thetaAboveCell01002202))) h)
    (by
      have h : ((childLH (childLH (childLL thetaAboveCell01002202)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childLL
        thetaAboveCell01002202))) h)
    (by
      have h : ((childHL (childLH (childLL thetaAboveCell01002202)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childLL
        thetaAboveCell01002202))) h)
    (by
      have h : ((childHH (childLH (childLL thetaAboveCell01002202)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childLL
        thetaAboveCell01002202))) h)
theorem e24KC2ThetaAboveLeaf0100220210 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell01002202)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childLH thetaAboveCell01002202))
    (by
      have h : ((childLL (childLL (childLH thetaAboveCell01002202)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childLH
        thetaAboveCell01002202))) h)
    (by
      have h : ((childLH (childLL (childLH thetaAboveCell01002202)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childLH
        thetaAboveCell01002202))) h)
    (by
      have h : ((childHL (childLL (childLH thetaAboveCell01002202)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childLH
        thetaAboveCell01002202))) h)
    (by
      have h : ((childHH (childLL (childLH thetaAboveCell01002202)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childLH
        thetaAboveCell01002202))) h)
theorem e24KC2ThetaAboveLeaf0100220211 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell01002202)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childLH thetaAboveCell01002202))
    (by
      have h : ((childLL (childLH (childLH thetaAboveCell01002202)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childLH
        thetaAboveCell01002202))) h)
    (by
      have h : ((childLH (childLH (childLH thetaAboveCell01002202)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childLH
        thetaAboveCell01002202))) h)
    (by
      have h : ((childHL (childLH (childLH thetaAboveCell01002202)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childLH
        thetaAboveCell01002202))) h)
    (by
      have h : ((childHH (childLH (childLH thetaAboveCell01002202)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childLH
        thetaAboveCell01002202))) h)
theorem e24KC2ThetaAboveLeaf0100220212 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell01002202)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childLH thetaAboveCell01002202))
    (by
      have h : ((childLL (childHL (childLH thetaAboveCell01002202)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childLH
        thetaAboveCell01002202))) h)
    (by
      have h : ((childLH (childHL (childLH thetaAboveCell01002202)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childLH
        thetaAboveCell01002202))) h)
    (by
      have h : ((childHL (childHL (childLH thetaAboveCell01002202)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childLH
        thetaAboveCell01002202))) h)
    (by
      have h : ((childHH (childHL (childLH thetaAboveCell01002202)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childLH
        thetaAboveCell01002202))) h)
theorem e24KC2ThetaAboveLeaf0100220213 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell01002202)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childLH thetaAboveCell01002202))
    (by
      have h : ((childLL (childHH (childLH thetaAboveCell01002202)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childLH
        thetaAboveCell01002202))) h)
    (by
      have h : ((childLH (childHH (childLH thetaAboveCell01002202)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childLH
        thetaAboveCell01002202))) h)
    (by
      have h : ((childHL (childHH (childLH thetaAboveCell01002202)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childLH
        thetaAboveCell01002202))) h)
    (by
      have h : ((childHH (childHH (childLH thetaAboveCell01002202)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childLH
        thetaAboveCell01002202))) h)
theorem e24KC2ThetaAboveLeaf0100220300 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell01002203)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childLL thetaAboveCell01002203))
    (by
      have h : ((childLL (childLL (childLL thetaAboveCell01002203)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childLL
        thetaAboveCell01002203))) h)
    (by
      have h : ((childLH (childLL (childLL thetaAboveCell01002203)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childLL
        thetaAboveCell01002203))) h)
    (by
      have h : ((childHL (childLL (childLL thetaAboveCell01002203)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childLL
        thetaAboveCell01002203))) h)
    (by
      have h : ((childHH (childLL (childLL thetaAboveCell01002203)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childLL
        thetaAboveCell01002203))) h)
theorem e24KC2ThetaAboveLeaf0100220301 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell01002203)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childLL thetaAboveCell01002203))
    (by
      have h : ((childLL (childLH (childLL thetaAboveCell01002203)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childLL
        thetaAboveCell01002203))) h)
    (by
      have h : ((childLH (childLH (childLL thetaAboveCell01002203)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childLL
        thetaAboveCell01002203))) h)
    (by
      have h : ((childHL (childLH (childLL thetaAboveCell01002203)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childLL
        thetaAboveCell01002203))) h)
    (by
      have h : ((childHH (childLH (childLL thetaAboveCell01002203)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childLL
        thetaAboveCell01002203))) h)
theorem e24KC2ThetaAboveLeaf0100220302 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell01002203)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childLL thetaAboveCell01002203))
    (by
      have h : ((childLL (childHL (childLL thetaAboveCell01002203)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childLL
        thetaAboveCell01002203))) h)
    (by
      have h : ((childLH (childHL (childLL thetaAboveCell01002203)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childLL
        thetaAboveCell01002203))) h)
    (by
      have h : ((childHL (childHL (childLL thetaAboveCell01002203)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childLL
        thetaAboveCell01002203))) h)
    (by
      have h : ((childHH (childHL (childLL thetaAboveCell01002203)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childLL
        thetaAboveCell01002203))) h)
theorem e24KC2ThetaAboveLeaf0100220303 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell01002203)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childLL thetaAboveCell01002203))
    (by
      have h : ((childLL (childHH (childLL thetaAboveCell01002203)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childLL
        thetaAboveCell01002203))) h)
    (by
      have h : ((childLH (childHH (childLL thetaAboveCell01002203)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childLL
        thetaAboveCell01002203))) h)
    (by
      have h : ((childHL (childHH (childLL thetaAboveCell01002203)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childLL
        thetaAboveCell01002203))) h)
    (by
      have h : ((childHH (childHH (childLL thetaAboveCell01002203)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childLL
        thetaAboveCell01002203))) h)
theorem e24KC2ThetaAboveLeaf0100220310 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell01002203)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childLH thetaAboveCell01002203))
    (by
      have h : ((childLL (childLL (childLH thetaAboveCell01002203)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childLH
        thetaAboveCell01002203))) h)
    (by
      have h : ((childLH (childLL (childLH thetaAboveCell01002203)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childLH
        thetaAboveCell01002203))) h)
    (by
      have h : ((childHL (childLL (childLH thetaAboveCell01002203)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childLH
        thetaAboveCell01002203))) h)
    (by
      have h : ((childHH (childLL (childLH thetaAboveCell01002203)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childLH
        thetaAboveCell01002203))) h)
theorem e24KC2ThetaAboveLeaf0100220311 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell01002203)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childLH thetaAboveCell01002203))
    (by
      have h : ((childLL (childLH (childLH thetaAboveCell01002203)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childLH
        thetaAboveCell01002203))) h)
    (by
      have h : ((childLH (childLH (childLH thetaAboveCell01002203)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childLH
        thetaAboveCell01002203))) h)
    (by
      have h : ((childHL (childLH (childLH thetaAboveCell01002203)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childLH
        thetaAboveCell01002203))) h)
    (by
      have h : ((childHH (childLH (childLH thetaAboveCell01002203)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childLH
        thetaAboveCell01002203))) h)
theorem e24KC2ThetaAboveLeaf0100220312 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell01002203)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childLH thetaAboveCell01002203))
    (by
      have h : ((childLL (childHL (childLH thetaAboveCell01002203)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childLH
        thetaAboveCell01002203))) h)
    (by
      have h : ((childLH (childHL (childLH thetaAboveCell01002203)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childLH
        thetaAboveCell01002203))) h)
    (by
      have h : ((childHL (childHL (childLH thetaAboveCell01002203)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childLH
        thetaAboveCell01002203))) h)
    (by
      have h : ((childHH (childHL (childLH thetaAboveCell01002203)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childLH
        thetaAboveCell01002203))) h)
theorem e24KC2ThetaAboveLeaf0100220313 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell01002203)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childLH thetaAboveCell01002203))
    (by
      have h : ((childLL (childHH (childLH thetaAboveCell01002203)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childLH
        thetaAboveCell01002203))) h)
    (by
      have h : ((childLH (childHH (childLH thetaAboveCell01002203)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childLH
        thetaAboveCell01002203))) h)
    (by
      have h : ((childHL (childHH (childLH thetaAboveCell01002203)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childLH
        thetaAboveCell01002203))) h)
    (by
      have h : ((childHH (childHH (childLH thetaAboveCell01002203)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childLH
        thetaAboveCell01002203))) h)
theorem e24KC2ThetaAboveLeaf0100221022 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell01002210)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHL thetaAboveCell01002210))
    (by
      have h : ((childLL (childHL (childHL thetaAboveCell01002210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHL
        thetaAboveCell01002210))) h)
    (by
      have h : ((childLH (childHL (childHL thetaAboveCell01002210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHL
        thetaAboveCell01002210))) h)
    (by
      have h : ((childHL (childHL (childHL thetaAboveCell01002210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHL
        thetaAboveCell01002210))) h)
    (by
      have h : ((childHH (childHL (childHL thetaAboveCell01002210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHL
        thetaAboveCell01002210))) h)
theorem e24KC2ThetaAboveLeaf0100221023 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell01002210)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHL thetaAboveCell01002210))
    (by
      have h : ((childLL (childHH (childHL thetaAboveCell01002210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHL
        thetaAboveCell01002210))) h)
    (by
      have h : ((childLH (childHH (childHL thetaAboveCell01002210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHL
        thetaAboveCell01002210))) h)
    (by
      have h : ((childHL (childHH (childHL thetaAboveCell01002210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHL
        thetaAboveCell01002210))) h)
    (by
      have h : ((childHH (childHH (childHL thetaAboveCell01002210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHL
        thetaAboveCell01002210))) h)
theorem e24KC2ThetaAboveLeaf0100221032 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell01002210)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHH thetaAboveCell01002210))
    (by
      have h : ((childLL (childHL (childHH thetaAboveCell01002210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHH
        thetaAboveCell01002210))) h)
    (by
      have h : ((childLH (childHL (childHH thetaAboveCell01002210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHH
        thetaAboveCell01002210))) h)
    (by
      have h : ((childHL (childHL (childHH thetaAboveCell01002210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHH
        thetaAboveCell01002210))) h)
    (by
      have h : ((childHH (childHL (childHH thetaAboveCell01002210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHH
        thetaAboveCell01002210))) h)
theorem e24KC2ThetaAboveLeaf0100221033 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell01002210)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHH thetaAboveCell01002210))
    (by
      have h : ((childLL (childHH (childHH thetaAboveCell01002210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHH
        thetaAboveCell01002210))) h)
    (by
      have h : ((childLH (childHH (childHH thetaAboveCell01002210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHH
        thetaAboveCell01002210))) h)
    (by
      have h : ((childHL (childHH (childHH thetaAboveCell01002210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHH
        thetaAboveCell01002210))) h)
    (by
      have h : ((childHH (childHH (childHH thetaAboveCell01002210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHH
        thetaAboveCell01002210))) h)
theorem e24KC2ThetaAboveLeaf0100221122 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell01002211)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHL thetaAboveCell01002211))
    (by
      have h : ((childLL (childHL (childHL thetaAboveCell01002211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHL
        thetaAboveCell01002211))) h)
    (by
      have h : ((childLH (childHL (childHL thetaAboveCell01002211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHL
        thetaAboveCell01002211))) h)
    (by
      have h : ((childHL (childHL (childHL thetaAboveCell01002211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHL
        thetaAboveCell01002211))) h)
    (by
      have h : ((childHH (childHL (childHL thetaAboveCell01002211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHL
        thetaAboveCell01002211))) h)
theorem e24KC2ThetaAboveLeaf0100221123 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell01002211)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHL thetaAboveCell01002211))
    (by
      have h : ((childLL (childHH (childHL thetaAboveCell01002211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHL
        thetaAboveCell01002211))) h)
    (by
      have h : ((childLH (childHH (childHL thetaAboveCell01002211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHL
        thetaAboveCell01002211))) h)
    (by
      have h : ((childHL (childHH (childHL thetaAboveCell01002211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHL
        thetaAboveCell01002211))) h)
    (by
      have h : ((childHH (childHH (childHL thetaAboveCell01002211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHL
        thetaAboveCell01002211))) h)
theorem e24KC2ThetaAboveLeaf0100221132 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell01002211)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHH thetaAboveCell01002211))
    (by
      have h : ((childLL (childHL (childHH thetaAboveCell01002211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHH
        thetaAboveCell01002211))) h)
    (by
      have h : ((childLH (childHL (childHH thetaAboveCell01002211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHH
        thetaAboveCell01002211))) h)
    (by
      have h : ((childHL (childHL (childHH thetaAboveCell01002211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHH
        thetaAboveCell01002211))) h)
    (by
      have h : ((childHH (childHL (childHH thetaAboveCell01002211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHH
        thetaAboveCell01002211))) h)
theorem e24KC2ThetaAboveLeaf0100221133 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell01002211)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHH thetaAboveCell01002211))
    (by
      have h : ((childLL (childHH (childHH thetaAboveCell01002211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHH
        thetaAboveCell01002211))) h)
    (by
      have h : ((childLH (childHH (childHH thetaAboveCell01002211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHH
        thetaAboveCell01002211))) h)
    (by
      have h : ((childHL (childHH (childHH thetaAboveCell01002211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHH
        thetaAboveCell01002211))) h)
    (by
      have h : ((childHH (childHH (childHH thetaAboveCell01002211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHH
        thetaAboveCell01002211))) h)
theorem e24KC2ThetaAboveLeaf0100221200 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell01002212)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childLL thetaAboveCell01002212))
    (by
      have h : ((childLL (childLL (childLL thetaAboveCell01002212)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childLL
        thetaAboveCell01002212))) h)
    (by
      have h : ((childLH (childLL (childLL thetaAboveCell01002212)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childLL
        thetaAboveCell01002212))) h)
    (by
      have h : ((childHL (childLL (childLL thetaAboveCell01002212)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childLL
        thetaAboveCell01002212))) h)
    (by
      have h : ((childHH (childLL (childLL thetaAboveCell01002212)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childLL
        thetaAboveCell01002212))) h)
theorem e24KC2ThetaAboveLeaf0100221201 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell01002212)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childLL thetaAboveCell01002212))
    (by
      have h : ((childLL (childLH (childLL thetaAboveCell01002212)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childLL
        thetaAboveCell01002212))) h)
    (by
      have h : ((childLH (childLH (childLL thetaAboveCell01002212)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childLL
        thetaAboveCell01002212))) h)
    (by
      have h : ((childHL (childLH (childLL thetaAboveCell01002212)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childLL
        thetaAboveCell01002212))) h)
    (by
      have h : ((childHH (childLH (childLL thetaAboveCell01002212)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childLL
        thetaAboveCell01002212))) h)
theorem e24KC2ThetaAboveLeaf0100221202 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell01002212)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childLL thetaAboveCell01002212))
    (by
      have h : ((childLL (childHL (childLL thetaAboveCell01002212)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childLL
        thetaAboveCell01002212))) h)
    (by
      have h : ((childLH (childHL (childLL thetaAboveCell01002212)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childLL
        thetaAboveCell01002212))) h)
    (by
      have h : ((childHL (childHL (childLL thetaAboveCell01002212)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childLL
        thetaAboveCell01002212))) h)
    (by
      have h : ((childHH (childHL (childLL thetaAboveCell01002212)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childLL
        thetaAboveCell01002212))) h)
theorem e24KC2ThetaAboveLeaf0100221210 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell01002212)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childLH thetaAboveCell01002212))
    (by
      have h : ((childLL (childLL (childLH thetaAboveCell01002212)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childLH
        thetaAboveCell01002212))) h)
    (by
      have h : ((childLH (childLL (childLH thetaAboveCell01002212)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childLH
        thetaAboveCell01002212))) h)
    (by
      have h : ((childHL (childLL (childLH thetaAboveCell01002212)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childLH
        thetaAboveCell01002212))) h)
    (by
      have h : ((childHH (childLL (childLH thetaAboveCell01002212)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childLH
        thetaAboveCell01002212))) h)
theorem e24KC2ThetaAboveLeaf0100221211 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell01002212)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childLH thetaAboveCell01002212))
    (by
      have h : ((childLL (childLH (childLH thetaAboveCell01002212)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childLH
        thetaAboveCell01002212))) h)
    (by
      have h : ((childLH (childLH (childLH thetaAboveCell01002212)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childLH
        thetaAboveCell01002212))) h)
    (by
      have h : ((childHL (childLH (childLH thetaAboveCell01002212)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childLH
        thetaAboveCell01002212))) h)
    (by
      have h : ((childHH (childLH (childLH thetaAboveCell01002212)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childLH
        thetaAboveCell01002212))) h)
theorem e24KC2ThetaAboveLeaf0100221300 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell01002213)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childLL thetaAboveCell01002213))
    (by
      have h : ((childLL (childLL (childLL thetaAboveCell01002213)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childLL
        thetaAboveCell01002213))) h)
    (by
      have h : ((childLH (childLL (childLL thetaAboveCell01002213)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childLL
        thetaAboveCell01002213))) h)
    (by
      have h : ((childHL (childLL (childLL thetaAboveCell01002213)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childLL
        thetaAboveCell01002213))) h)
    (by
      have h : ((childHH (childLL (childLL thetaAboveCell01002213)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childLL
        thetaAboveCell01002213))) h)
theorem e24KC2ThetaAboveLeaf0100221301 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell01002213)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childLL thetaAboveCell01002213))
    (by
      have h : ((childLL (childLH (childLL thetaAboveCell01002213)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childLL
        thetaAboveCell01002213))) h)
    (by
      have h : ((childLH (childLH (childLL thetaAboveCell01002213)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childLL
        thetaAboveCell01002213))) h)
    (by
      have h : ((childHL (childLH (childLL thetaAboveCell01002213)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childLL
        thetaAboveCell01002213))) h)
    (by
      have h : ((childHH (childLH (childLL thetaAboveCell01002213)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childLL
        thetaAboveCell01002213))) h)
theorem e24KC2ThetaAboveLeaf0100221310 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell01002213)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childLH thetaAboveCell01002213))
    (by
      have h : ((childLL (childLL (childLH thetaAboveCell01002213)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childLH
        thetaAboveCell01002213))) h)
    (by
      have h : ((childLH (childLL (childLH thetaAboveCell01002213)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childLH
        thetaAboveCell01002213))) h)
    (by
      have h : ((childHL (childLL (childLH thetaAboveCell01002213)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childLH
        thetaAboveCell01002213))) h)
    (by
      have h : ((childHH (childLL (childLH thetaAboveCell01002213)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childLH
        thetaAboveCell01002213))) h)
theorem e24KC2ThetaAboveLeaf0100221311 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell01002213)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childLH thetaAboveCell01002213))
    (by
      have h : ((childLL (childLH (childLH thetaAboveCell01002213)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childLH
        thetaAboveCell01002213))) h)
    (by
      have h : ((childLH (childLH (childLH thetaAboveCell01002213)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childLH
        thetaAboveCell01002213))) h)
    (by
      have h : ((childHL (childLH (childLH thetaAboveCell01002213)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childLH
        thetaAboveCell01002213))) h)
    (by
      have h : ((childHH (childLH (childLH thetaAboveCell01002213)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childLH
        thetaAboveCell01002213))) h)
theorem e24KC2ThetaAboveLeaf0100230022 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell01002300)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHL thetaAboveCell01002300))
    (by
      have h : ((childLL (childHL (childHL thetaAboveCell01002300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHL
        thetaAboveCell01002300))) h)
    (by
      have h : ((childLH (childHL (childHL thetaAboveCell01002300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHL
        thetaAboveCell01002300))) h)
    (by
      have h : ((childHL (childHL (childHL thetaAboveCell01002300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHL
        thetaAboveCell01002300))) h)
    (by
      have h : ((childHH (childHL (childHL thetaAboveCell01002300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHL
        thetaAboveCell01002300))) h)
theorem e24KC2ThetaAboveLeaf0100230023 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell01002300)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHL thetaAboveCell01002300))
    (by
      have h : ((childLL (childHH (childHL thetaAboveCell01002300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHL
        thetaAboveCell01002300))) h)
    (by
      have h : ((childLH (childHH (childHL thetaAboveCell01002300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHL
        thetaAboveCell01002300))) h)
    (by
      have h : ((childHL (childHH (childHL thetaAboveCell01002300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHL
        thetaAboveCell01002300))) h)
    (by
      have h : ((childHH (childHH (childHL thetaAboveCell01002300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHL
        thetaAboveCell01002300))) h)
theorem e24KC2ThetaAboveLeaf0100230032 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell01002300)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHH thetaAboveCell01002300))
    (by
      have h : ((childLL (childHL (childHH thetaAboveCell01002300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHH
        thetaAboveCell01002300))) h)
    (by
      have h : ((childLH (childHL (childHH thetaAboveCell01002300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHH
        thetaAboveCell01002300))) h)
    (by
      have h : ((childHL (childHL (childHH thetaAboveCell01002300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHH
        thetaAboveCell01002300))) h)
    (by
      have h : ((childHH (childHL (childHH thetaAboveCell01002300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHH
        thetaAboveCell01002300))) h)
theorem e24KC2ThetaAboveLeaf0100230033 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell01002300)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHH thetaAboveCell01002300))
    (by
      have h : ((childLL (childHH (childHH thetaAboveCell01002300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHH
        thetaAboveCell01002300))) h)
    (by
      have h : ((childLH (childHH (childHH thetaAboveCell01002300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHH
        thetaAboveCell01002300))) h)
    (by
      have h : ((childHL (childHH (childHH thetaAboveCell01002300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHH
        thetaAboveCell01002300))) h)
    (by
      have h : ((childHH (childHH (childHH thetaAboveCell01002300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHH
        thetaAboveCell01002300))) h)
theorem e24KC2ThetaAboveLeaf0100230122 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell01002301)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHL thetaAboveCell01002301))
    (by
      have h : ((childLL (childHL (childHL thetaAboveCell01002301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHL
        thetaAboveCell01002301))) h)
    (by
      have h : ((childLH (childHL (childHL thetaAboveCell01002301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHL
        thetaAboveCell01002301))) h)
    (by
      have h : ((childHL (childHL (childHL thetaAboveCell01002301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHL
        thetaAboveCell01002301))) h)
    (by
      have h : ((childHH (childHL (childHL thetaAboveCell01002301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHL
        thetaAboveCell01002301))) h)
theorem e24KC2ThetaAboveLeaf0100230123 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell01002301)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHL thetaAboveCell01002301))
    (by
      have h : ((childLL (childHH (childHL thetaAboveCell01002301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHL
        thetaAboveCell01002301))) h)
    (by
      have h : ((childLH (childHH (childHL thetaAboveCell01002301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHL
        thetaAboveCell01002301))) h)
    (by
      have h : ((childHL (childHH (childHL thetaAboveCell01002301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHL
        thetaAboveCell01002301))) h)
    (by
      have h : ((childHH (childHH (childHL thetaAboveCell01002301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHL
        thetaAboveCell01002301))) h)
theorem e24KC2ThetaAboveLeaf0100230132 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell01002301)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHH thetaAboveCell01002301))
    (by
      have h : ((childLL (childHL (childHH thetaAboveCell01002301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHH
        thetaAboveCell01002301))) h)
    (by
      have h : ((childLH (childHL (childHH thetaAboveCell01002301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHH
        thetaAboveCell01002301))) h)
    (by
      have h : ((childHL (childHL (childHH thetaAboveCell01002301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHH
        thetaAboveCell01002301))) h)
    (by
      have h : ((childHH (childHL (childHH thetaAboveCell01002301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHH
        thetaAboveCell01002301))) h)
theorem e24KC2ThetaAboveLeaf0100230133 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell01002301)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHH thetaAboveCell01002301))
    (by
      have h : ((childLL (childHH (childHH thetaAboveCell01002301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHH
        thetaAboveCell01002301))) h)
    (by
      have h : ((childLH (childHH (childHH thetaAboveCell01002301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHH
        thetaAboveCell01002301))) h)
    (by
      have h : ((childHL (childHH (childHH thetaAboveCell01002301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHH
        thetaAboveCell01002301))) h)
    (by
      have h : ((childHH (childHH (childHH thetaAboveCell01002301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHH
        thetaAboveCell01002301))) h)
theorem e24KC2ThetaAboveLeaf0100230200 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell01002302)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childLL thetaAboveCell01002302))
    (by
      have h : ((childLL (childLL (childLL thetaAboveCell01002302)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childLL
        thetaAboveCell01002302))) h)
    (by
      have h : ((childLH (childLL (childLL thetaAboveCell01002302)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childLL
        thetaAboveCell01002302))) h)
    (by
      have h : ((childHL (childLL (childLL thetaAboveCell01002302)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childLL
        thetaAboveCell01002302))) h)
    (by
      have h : ((childHH (childLL (childLL thetaAboveCell01002302)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childLL
        thetaAboveCell01002302))) h)
theorem e24KC2ThetaAboveLeaf0100230201 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell01002302)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childLL thetaAboveCell01002302))
    (by
      have h : ((childLL (childLH (childLL thetaAboveCell01002302)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childLL
        thetaAboveCell01002302))) h)
    (by
      have h : ((childLH (childLH (childLL thetaAboveCell01002302)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childLL
        thetaAboveCell01002302))) h)
    (by
      have h : ((childHL (childLH (childLL thetaAboveCell01002302)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childLL
        thetaAboveCell01002302))) h)
    (by
      have h : ((childHH (childLH (childLL thetaAboveCell01002302)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childLL
        thetaAboveCell01002302))) h)
theorem e24KC2ThetaAboveLeaf0100230210 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell01002302)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childLH thetaAboveCell01002302))
    (by
      have h : ((childLL (childLL (childLH thetaAboveCell01002302)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childLH
        thetaAboveCell01002302))) h)
    (by
      have h : ((childLH (childLL (childLH thetaAboveCell01002302)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childLH
        thetaAboveCell01002302))) h)
    (by
      have h : ((childHL (childLL (childLH thetaAboveCell01002302)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childLH
        thetaAboveCell01002302))) h)
    (by
      have h : ((childHH (childLL (childLH thetaAboveCell01002302)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childLH
        thetaAboveCell01002302))) h)
theorem e24KC2ThetaAboveLeaf0100230211 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell01002302)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childLH thetaAboveCell01002302))
    (by
      have h : ((childLL (childLH (childLH thetaAboveCell01002302)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childLH
        thetaAboveCell01002302))) h)
    (by
      have h : ((childLH (childLH (childLH thetaAboveCell01002302)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childLH
        thetaAboveCell01002302))) h)
    (by
      have h : ((childHL (childLH (childLH thetaAboveCell01002302)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childLH
        thetaAboveCell01002302))) h)
    (by
      have h : ((childHH (childLH (childLH thetaAboveCell01002302)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childLH
        thetaAboveCell01002302))) h)
theorem e24KC2ThetaAboveLeaf0100230300 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell01002303)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childLL thetaAboveCell01002303))
    (by
      have h : ((childLL (childLL (childLL thetaAboveCell01002303)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childLL
        thetaAboveCell01002303))) h)
    (by
      have h : ((childLH (childLL (childLL thetaAboveCell01002303)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childLL
        thetaAboveCell01002303))) h)
    (by
      have h : ((childHL (childLL (childLL thetaAboveCell01002303)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childLL
        thetaAboveCell01002303))) h)
    (by
      have h : ((childHH (childLL (childLL thetaAboveCell01002303)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childLL
        thetaAboveCell01002303))) h)
theorem e24KC2ThetaAboveLeaf0100230301 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell01002303)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childLL thetaAboveCell01002303))
    (by
      have h : ((childLL (childLH (childLL thetaAboveCell01002303)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childLL
        thetaAboveCell01002303))) h)
    (by
      have h : ((childLH (childLH (childLL thetaAboveCell01002303)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childLL
        thetaAboveCell01002303))) h)
    (by
      have h : ((childHL (childLH (childLL thetaAboveCell01002303)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childLL
        thetaAboveCell01002303))) h)
    (by
      have h : ((childHH (childLH (childLL thetaAboveCell01002303)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childLL
        thetaAboveCell01002303))) h)
theorem e24KC2ThetaAboveLeaf0100230310 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell01002303)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childLH thetaAboveCell01002303))
    (by
      have h : ((childLL (childLL (childLH thetaAboveCell01002303)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childLH
        thetaAboveCell01002303))) h)
    (by
      have h : ((childLH (childLL (childLH thetaAboveCell01002303)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childLH
        thetaAboveCell01002303))) h)
    (by
      have h : ((childHL (childLL (childLH thetaAboveCell01002303)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childLH
        thetaAboveCell01002303))) h)
    (by
      have h : ((childHH (childLL (childLH thetaAboveCell01002303)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childLH
        thetaAboveCell01002303))) h)
theorem e24KC2ThetaAboveLeaf0100230311 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell01002303)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childLH thetaAboveCell01002303))
    (by
      have h : ((childLL (childLH (childLH thetaAboveCell01002303)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childLH
        thetaAboveCell01002303))) h)
    (by
      have h : ((childLH (childLH (childLH thetaAboveCell01002303)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childLH
        thetaAboveCell01002303))) h)
    (by
      have h : ((childHL (childLH (childLH thetaAboveCell01002303)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childLH
        thetaAboveCell01002303))) h)
    (by
      have h : ((childHH (childLH (childLH thetaAboveCell01002303)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childLH
        thetaAboveCell01002303))) h)
theorem e24KC2ThetaAboveLeaf0100231022 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell01002310)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHL thetaAboveCell01002310))
    (by
      have h : ((childLL (childHL (childHL thetaAboveCell01002310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHL
        thetaAboveCell01002310))) h)
    (by
      have h : ((childLH (childHL (childHL thetaAboveCell01002310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHL
        thetaAboveCell01002310))) h)
    (by
      have h : ((childHL (childHL (childHL thetaAboveCell01002310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHL
        thetaAboveCell01002310))) h)
    (by
      have h : ((childHH (childHL (childHL thetaAboveCell01002310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHL
        thetaAboveCell01002310))) h)
theorem e24KC2ThetaAboveLeaf0100231023 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell01002310)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHL thetaAboveCell01002310))
    (by
      have h : ((childLL (childHH (childHL thetaAboveCell01002310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHL
        thetaAboveCell01002310))) h)
    (by
      have h : ((childLH (childHH (childHL thetaAboveCell01002310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHL
        thetaAboveCell01002310))) h)
    (by
      have h : ((childHL (childHH (childHL thetaAboveCell01002310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHL
        thetaAboveCell01002310))) h)
    (by
      have h : ((childHH (childHH (childHL thetaAboveCell01002310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHL
        thetaAboveCell01002310))) h)
theorem e24KC2ThetaAboveLeaf0100231032 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell01002310)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHH thetaAboveCell01002310))
    (by
      have h : ((childLL (childHL (childHH thetaAboveCell01002310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHH
        thetaAboveCell01002310))) h)
    (by
      have h : ((childLH (childHL (childHH thetaAboveCell01002310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHH
        thetaAboveCell01002310))) h)
    (by
      have h : ((childHL (childHL (childHH thetaAboveCell01002310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHH
        thetaAboveCell01002310))) h)
    (by
      have h : ((childHH (childHL (childHH thetaAboveCell01002310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHH
        thetaAboveCell01002310))) h)
theorem e24KC2ThetaAboveLeaf0100231033 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell01002310)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHH thetaAboveCell01002310))
    (by
      have h : ((childLL (childHH (childHH thetaAboveCell01002310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHH
        thetaAboveCell01002310))) h)
    (by
      have h : ((childLH (childHH (childHH thetaAboveCell01002310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHH
        thetaAboveCell01002310))) h)
    (by
      have h : ((childHL (childHH (childHH thetaAboveCell01002310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHH
        thetaAboveCell01002310))) h)
    (by
      have h : ((childHH (childHH (childHH thetaAboveCell01002310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHH
        thetaAboveCell01002310))) h)
theorem e24KC2ThetaAboveLeaf0100231122 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell01002311)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHL thetaAboveCell01002311))
    (by
      have h : ((childLL (childHL (childHL thetaAboveCell01002311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHL
        thetaAboveCell01002311))) h)
    (by
      have h : ((childLH (childHL (childHL thetaAboveCell01002311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHL
        thetaAboveCell01002311))) h)
    (by
      have h : ((childHL (childHL (childHL thetaAboveCell01002311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHL
        thetaAboveCell01002311))) h)
    (by
      have h : ((childHH (childHL (childHL thetaAboveCell01002311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHL
        thetaAboveCell01002311))) h)
theorem e24KC2ThetaAboveLeaf0100231123 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell01002311)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHL thetaAboveCell01002311))
    (by
      have h : ((childLL (childHH (childHL thetaAboveCell01002311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHL
        thetaAboveCell01002311))) h)
    (by
      have h : ((childLH (childHH (childHL thetaAboveCell01002311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHL
        thetaAboveCell01002311))) h)
    (by
      have h : ((childHL (childHH (childHL thetaAboveCell01002311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHL
        thetaAboveCell01002311))) h)
    (by
      have h : ((childHH (childHH (childHL thetaAboveCell01002311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHL
        thetaAboveCell01002311))) h)
theorem e24KC2ThetaAboveLeaf0100231132 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell01002311)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHH thetaAboveCell01002311))
    (by
      have h : ((childLL (childHL (childHH thetaAboveCell01002311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHH
        thetaAboveCell01002311))) h)
    (by
      have h : ((childLH (childHL (childHH thetaAboveCell01002311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHH
        thetaAboveCell01002311))) h)
    (by
      have h : ((childHL (childHL (childHH thetaAboveCell01002311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHH
        thetaAboveCell01002311))) h)
    (by
      have h : ((childHH (childHL (childHH thetaAboveCell01002311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHH
        thetaAboveCell01002311))) h)
theorem e24KC2ThetaAboveLeaf0100231133 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell01002311)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHH thetaAboveCell01002311))
    (by
      have h : ((childLL (childHH (childHH thetaAboveCell01002311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHH
        thetaAboveCell01002311))) h)
    (by
      have h : ((childLH (childHH (childHH thetaAboveCell01002311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHH
        thetaAboveCell01002311))) h)
    (by
      have h : ((childHL (childHH (childHH thetaAboveCell01002311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHH
        thetaAboveCell01002311))) h)
    (by
      have h : ((childHH (childHH (childHH thetaAboveCell01002311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHH
        thetaAboveCell01002311))) h)
theorem e24KC2ThetaAboveLeaf0100320022 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell01003200)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHL thetaAboveCell01003200))
    (by
      have h : ((childLL (childHL (childHL thetaAboveCell01003200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHL
        thetaAboveCell01003200))) h)
    (by
      have h : ((childLH (childHL (childHL thetaAboveCell01003200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHL
        thetaAboveCell01003200))) h)
    (by
      have h : ((childHL (childHL (childHL thetaAboveCell01003200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHL
        thetaAboveCell01003200))) h)
    (by
      have h : ((childHH (childHL (childHL thetaAboveCell01003200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHL
        thetaAboveCell01003200))) h)
theorem e24KC2ThetaAboveLeaf0100320023 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell01003200)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHL thetaAboveCell01003200))
    (by
      have h : ((childLL (childHH (childHL thetaAboveCell01003200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHL
        thetaAboveCell01003200))) h)
    (by
      have h : ((childLH (childHH (childHL thetaAboveCell01003200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHL
        thetaAboveCell01003200))) h)
    (by
      have h : ((childHL (childHH (childHL thetaAboveCell01003200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHL
        thetaAboveCell01003200))) h)
    (by
      have h : ((childHH (childHH (childHL thetaAboveCell01003200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHL
        thetaAboveCell01003200))) h)
theorem e24KC2ThetaAboveLeaf0100320032 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell01003200)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHH thetaAboveCell01003200))
    (by
      have h : ((childLL (childHL (childHH thetaAboveCell01003200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHH
        thetaAboveCell01003200))) h)
    (by
      have h : ((childLH (childHL (childHH thetaAboveCell01003200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHH
        thetaAboveCell01003200))) h)
    (by
      have h : ((childHL (childHL (childHH thetaAboveCell01003200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHH
        thetaAboveCell01003200))) h)
    (by
      have h : ((childHH (childHL (childHH thetaAboveCell01003200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHH
        thetaAboveCell01003200))) h)
theorem e24KC2ThetaAboveLeaf0100320033 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell01003200)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHH thetaAboveCell01003200))
    (by
      have h : ((childLL (childHH (childHH thetaAboveCell01003200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHH
        thetaAboveCell01003200))) h)
    (by
      have h : ((childLH (childHH (childHH thetaAboveCell01003200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHH
        thetaAboveCell01003200))) h)
    (by
      have h : ((childHL (childHH (childHH thetaAboveCell01003200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHH
        thetaAboveCell01003200))) h)
    (by
      have h : ((childHH (childHH (childHH thetaAboveCell01003200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHH
        thetaAboveCell01003200))) h)
theorem e24KC2ThetaAboveLeaf0100320122 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell01003201)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHL thetaAboveCell01003201))
    (by
      have h : ((childLL (childHL (childHL thetaAboveCell01003201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHL
        thetaAboveCell01003201))) h)
    (by
      have h : ((childLH (childHL (childHL thetaAboveCell01003201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHL
        thetaAboveCell01003201))) h)
    (by
      have h : ((childHL (childHL (childHL thetaAboveCell01003201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHL
        thetaAboveCell01003201))) h)
    (by
      have h : ((childHH (childHL (childHL thetaAboveCell01003201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHL
        thetaAboveCell01003201))) h)
theorem e24KC2ThetaAboveLeaf0100320123 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell01003201)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHL thetaAboveCell01003201))
    (by
      have h : ((childLL (childHH (childHL thetaAboveCell01003201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHL
        thetaAboveCell01003201))) h)
    (by
      have h : ((childLH (childHH (childHL thetaAboveCell01003201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHL
        thetaAboveCell01003201))) h)
    (by
      have h : ((childHL (childHH (childHL thetaAboveCell01003201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHL
        thetaAboveCell01003201))) h)
    (by
      have h : ((childHH (childHH (childHL thetaAboveCell01003201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHL
        thetaAboveCell01003201))) h)
theorem e24KC2ThetaAboveLeaf0100320132 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell01003201)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHH thetaAboveCell01003201))
    (by
      have h : ((childLL (childHL (childHH thetaAboveCell01003201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHH
        thetaAboveCell01003201))) h)
    (by
      have h : ((childLH (childHL (childHH thetaAboveCell01003201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHH
        thetaAboveCell01003201))) h)
    (by
      have h : ((childHL (childHL (childHH thetaAboveCell01003201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHH
        thetaAboveCell01003201))) h)
    (by
      have h : ((childHH (childHL (childHH thetaAboveCell01003201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHH
        thetaAboveCell01003201))) h)
theorem e24KC2ThetaAboveLeaf0100320133 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell01003201)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHH thetaAboveCell01003201))
    (by
      have h : ((childLL (childHH (childHH thetaAboveCell01003201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHH
        thetaAboveCell01003201))) h)
    (by
      have h : ((childLH (childHH (childHH thetaAboveCell01003201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHH
        thetaAboveCell01003201))) h)
    (by
      have h : ((childHL (childHH (childHH thetaAboveCell01003201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHH
        thetaAboveCell01003201))) h)
    (by
      have h : ((childHH (childHH (childHH thetaAboveCell01003201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHH
        thetaAboveCell01003201))) h)
theorem e24KC2ThetaBelowLeaf111030223 :
    adaptiveCoverCheck 9 (childHH thetaBelowCell11103022) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH thetaBelowCell11103022)
    (by
      have h : ((childLL (childHH thetaBelowCell11103022))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH thetaBelowCell11103022)) h)
    (by
      have h : ((childLH (childHH thetaBelowCell11103022))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH thetaBelowCell11103022)) h)
    (by
      have h : ((childHL (childHH thetaBelowCell11103022))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH thetaBelowCell11103022)) h)
    (by
      have h : ((childHH (childHH thetaBelowCell11103022))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH thetaBelowCell11103022)) h)
theorem e24KC2ThetaBelowLeaf111030232 :
    adaptiveCoverCheck 9 (childHL thetaBelowCell11103023) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL thetaBelowCell11103023)
    (by
      have h : ((childLL (childHL thetaBelowCell11103023))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL thetaBelowCell11103023)) h)
    (by
      have h : ((childLH (childHL thetaBelowCell11103023))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL thetaBelowCell11103023)) h)
    (by
      have h : ((childHL (childHL thetaBelowCell11103023))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL thetaBelowCell11103023)) h)
    (by
      have h : ((childHH (childHL thetaBelowCell11103023))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL thetaBelowCell11103023)) h)
theorem e24KC2ThetaBelowLeaf111030233 :
    adaptiveCoverCheck 9 (childHH thetaBelowCell11103023) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH thetaBelowCell11103023)
    (by
      have h : ((childLL (childHH thetaBelowCell11103023))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH thetaBelowCell11103023)) h)
    (by
      have h : ((childLH (childHH thetaBelowCell11103023))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH thetaBelowCell11103023)) h)
    (by
      have h : ((childHL (childHH thetaBelowCell11103023))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH thetaBelowCell11103023)) h)
    (by
      have h : ((childHH (childHH thetaBelowCell11103023))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH thetaBelowCell11103023)) h)
theorem e24KC2ThetaBelowLeaf111030312 :
    adaptiveCoverCheck 9 (childHL thetaBelowCell11103031) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL thetaBelowCell11103031)
    (by
      have h : ((childLL (childHL thetaBelowCell11103031))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL thetaBelowCell11103031)) h)
    (by
      have h : ((childLH (childHL thetaBelowCell11103031))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL thetaBelowCell11103031)) h)
    (by
      have h : ((childHL (childHL thetaBelowCell11103031))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL thetaBelowCell11103031)) h)
    (by
      have h : ((childHH (childHL thetaBelowCell11103031))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL thetaBelowCell11103031)) h)
theorem e24KC2ThetaBelowLeaf111030313 :
    adaptiveCoverCheck 9 (childHH thetaBelowCell11103031) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH thetaBelowCell11103031)
    (by
      have h : ((childLL (childHH thetaBelowCell11103031))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH thetaBelowCell11103031)) h)
    (by
      have h : ((childLH (childHH thetaBelowCell11103031))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH thetaBelowCell11103031)) h)
    (by
      have h : ((childHL (childHH thetaBelowCell11103031))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH thetaBelowCell11103031)) h)
    (by
      have h : ((childHH (childHH thetaBelowCell11103031))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH thetaBelowCell11103031)) h)
theorem e24KC2ThetaBelowLeaf111030320 :
    adaptiveCoverCheck 9 (childLL thetaBelowCell11103032) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL thetaBelowCell11103032)
    (by
      have h : ((childLL (childLL thetaBelowCell11103032))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL thetaBelowCell11103032)) h)
    (by
      have h : ((childLH (childLL thetaBelowCell11103032))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL thetaBelowCell11103032)) h)
    (by
      have h : ((childHL (childLL thetaBelowCell11103032))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL thetaBelowCell11103032)) h)
    (by
      have h : ((childHH (childLL thetaBelowCell11103032))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL thetaBelowCell11103032)) h)
theorem e24KC2ThetaBelowLeaf111030321 :
    adaptiveCoverCheck 9 (childLH thetaBelowCell11103032) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH thetaBelowCell11103032)
    (by
      have h : ((childLL (childLH thetaBelowCell11103032))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH thetaBelowCell11103032)) h)
    (by
      have h : ((childLH (childLH thetaBelowCell11103032))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH thetaBelowCell11103032)) h)
    (by
      have h : ((childHL (childLH thetaBelowCell11103032))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH thetaBelowCell11103032)) h)
    (by
      have h : ((childHH (childLH thetaBelowCell11103032))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH thetaBelowCell11103032)) h)
theorem e24KC2ThetaBelowLeaf111030322 :
    adaptiveCoverCheck 9 (childHL thetaBelowCell11103032) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL thetaBelowCell11103032)
    (by
      have h : ((childLL (childHL thetaBelowCell11103032))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL thetaBelowCell11103032)) h)
    (by
      have h : ((childLH (childHL thetaBelowCell11103032))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL thetaBelowCell11103032)) h)
    (by
      have h : ((childHL (childHL thetaBelowCell11103032))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL thetaBelowCell11103032)) h)
    (by
      have h : ((childHH (childHL thetaBelowCell11103032))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL thetaBelowCell11103032)) h)
theorem e24KC2ThetaBelowLeaf111030323 :
    adaptiveCoverCheck 9 (childHH thetaBelowCell11103032) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH thetaBelowCell11103032)
    (by
      have h : ((childLL (childHH thetaBelowCell11103032))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH thetaBelowCell11103032)) h)
    (by
      have h : ((childLH (childHH thetaBelowCell11103032))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH thetaBelowCell11103032)) h)
    (by
      have h : ((childHL (childHH thetaBelowCell11103032))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH thetaBelowCell11103032)) h)
    (by
      have h : ((childHH (childHH thetaBelowCell11103032))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH thetaBelowCell11103032)) h)
theorem e24KC2ThetaBelowLeaf111030330 :
    adaptiveCoverCheck 9 (childLL thetaBelowCell11103033) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL thetaBelowCell11103033)
    (by
      have h : ((childLL (childLL thetaBelowCell11103033))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL thetaBelowCell11103033)) h)
    (by
      have h : ((childLH (childLL thetaBelowCell11103033))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL thetaBelowCell11103033)) h)
    (by
      have h : ((childHL (childLL thetaBelowCell11103033))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL thetaBelowCell11103033)) h)
    (by
      have h : ((childHH (childLL thetaBelowCell11103033))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL thetaBelowCell11103033)) h)
theorem e24KC2ThetaBelowLeaf111030331 :
    adaptiveCoverCheck 9 (childLH thetaBelowCell11103033) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH thetaBelowCell11103033)
    (by
      have h : ((childLL (childLH thetaBelowCell11103033))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH thetaBelowCell11103033)) h)
    (by
      have h : ((childLH (childLH thetaBelowCell11103033))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH thetaBelowCell11103033)) h)
    (by
      have h : ((childHL (childLH thetaBelowCell11103033))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH thetaBelowCell11103033)) h)
    (by
      have h : ((childHH (childLH thetaBelowCell11103033))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH thetaBelowCell11103033)) h)
theorem e24KC2ThetaBelowLeaf111030332 :
    adaptiveCoverCheck 9 (childHL thetaBelowCell11103033) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL thetaBelowCell11103033)
    (by
      have h : ((childLL (childHL thetaBelowCell11103033))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL thetaBelowCell11103033)) h)
    (by
      have h : ((childLH (childHL thetaBelowCell11103033))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL thetaBelowCell11103033)) h)
    (by
      have h : ((childHL (childHL thetaBelowCell11103033))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL thetaBelowCell11103033)) h)
    (by
      have h : ((childHH (childHL thetaBelowCell11103033))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL thetaBelowCell11103033)) h)
theorem e24KC2ThetaBelowLeaf111030333 :
    adaptiveCoverCheck 9 (childHH thetaBelowCell11103033) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH thetaBelowCell11103033)
    (by
      have h : ((childLL (childHH thetaBelowCell11103033))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH thetaBelowCell11103033)) h)
    (by
      have h : ((childLH (childHH thetaBelowCell11103033))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH thetaBelowCell11103033)) h)
    (by
      have h : ((childHL (childHH thetaBelowCell11103033))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH thetaBelowCell11103033)) h)
    (by
      have h : ((childHH (childHH thetaBelowCell11103033))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH thetaBelowCell11103033)) h)
theorem e24KC2ThetaBelowLeaf111031202 :
    adaptiveCoverCheck 9 (childHL thetaBelowCell11103120) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL thetaBelowCell11103120)
    (by
      have h : ((childLL (childHL thetaBelowCell11103120))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL thetaBelowCell11103120)) h)
    (by
      have h : ((childLH (childHL thetaBelowCell11103120))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL thetaBelowCell11103120)) h)
    (by
      have h : ((childHL (childHL thetaBelowCell11103120))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL thetaBelowCell11103120)) h)
    (by
      have h : ((childHH (childHL thetaBelowCell11103120))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL thetaBelowCell11103120)) h)
theorem e24KC2ThetaBelowLeaf111031220 :
    adaptiveCoverCheck 9 (childLL thetaBelowCell11103122) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL thetaBelowCell11103122)
    (by
      have h : ((childLL (childLL thetaBelowCell11103122))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL thetaBelowCell11103122)) h)
    (by
      have h : ((childLH (childLL thetaBelowCell11103122))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL thetaBelowCell11103122)) h)
    (by
      have h : ((childHL (childLL thetaBelowCell11103122))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL thetaBelowCell11103122)) h)
    (by
      have h : ((childHH (childLL thetaBelowCell11103122))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL thetaBelowCell11103122)) h)
theorem e24KC2ThetaBelowLeaf111031221 :
    adaptiveCoverCheck 9 (childLH thetaBelowCell11103122) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH thetaBelowCell11103122)
    (by
      have h : ((childLL (childLH thetaBelowCell11103122))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH thetaBelowCell11103122)) h)
    (by
      have h : ((childLH (childLH thetaBelowCell11103122))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH thetaBelowCell11103122)) h)
    (by
      have h : ((childHL (childLH thetaBelowCell11103122))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH thetaBelowCell11103122)) h)
    (by
      have h : ((childHH (childLH thetaBelowCell11103122))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH thetaBelowCell11103122)) h)
theorem e24KC2ThetaBelowLeaf111031222 :
    adaptiveCoverCheck 9 (childHL thetaBelowCell11103122) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL thetaBelowCell11103122)
    (by
      have h : ((childLL (childHL thetaBelowCell11103122))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL thetaBelowCell11103122)) h)
    (by
      have h : ((childLH (childHL thetaBelowCell11103122))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL thetaBelowCell11103122)) h)
    (by
      have h : ((childHL (childHL thetaBelowCell11103122))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL thetaBelowCell11103122)) h)
    (by
      have h : ((childHH (childHL thetaBelowCell11103122))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL thetaBelowCell11103122)) h)
theorem e24KC2ThetaBelowLeaf111031223 :
    adaptiveCoverCheck 9 (childHH thetaBelowCell11103122) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH thetaBelowCell11103122)
    (by
      have h : ((childLL (childHH thetaBelowCell11103122))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH thetaBelowCell11103122)) h)
    (by
      have h : ((childLH (childHH thetaBelowCell11103122))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH thetaBelowCell11103122)) h)
    (by
      have h : ((childHL (childHH thetaBelowCell11103122))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH thetaBelowCell11103122)) h)
    (by
      have h : ((childHH (childHH thetaBelowCell11103122))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH thetaBelowCell11103122)) h)
theorem e24KC2ThetaBelowLeaf111031230 :
    adaptiveCoverCheck 9 (childLL thetaBelowCell11103123) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL thetaBelowCell11103123)
    (by
      have h : ((childLL (childLL thetaBelowCell11103123))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL thetaBelowCell11103123)) h)
    (by
      have h : ((childLH (childLL thetaBelowCell11103123))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL thetaBelowCell11103123)) h)
    (by
      have h : ((childHL (childLL thetaBelowCell11103123))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL thetaBelowCell11103123)) h)
    (by
      have h : ((childHH (childLL thetaBelowCell11103123))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL thetaBelowCell11103123)) h)
theorem e24KC2ThetaBelowLeaf111031231 :
    adaptiveCoverCheck 9 (childLH thetaBelowCell11103123) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH thetaBelowCell11103123)
    (by
      have h : ((childLL (childLH thetaBelowCell11103123))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH thetaBelowCell11103123)) h)
    (by
      have h : ((childLH (childLH thetaBelowCell11103123))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH thetaBelowCell11103123)) h)
    (by
      have h : ((childHL (childLH thetaBelowCell11103123))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH thetaBelowCell11103123)) h)
    (by
      have h : ((childHH (childLH thetaBelowCell11103123))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH thetaBelowCell11103123)) h)
theorem e24KC2ThetaBelowLeaf111031232 :
    adaptiveCoverCheck 9 (childHL thetaBelowCell11103123) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL thetaBelowCell11103123)
    (by
      have h : ((childLL (childHL thetaBelowCell11103123))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL thetaBelowCell11103123)) h)
    (by
      have h : ((childLH (childHL thetaBelowCell11103123))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL thetaBelowCell11103123)) h)
    (by
      have h : ((childHL (childHL thetaBelowCell11103123))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL thetaBelowCell11103123)) h)
    (by
      have h : ((childHH (childHL thetaBelowCell11103123))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL thetaBelowCell11103123)) h)
theorem e24KC2ThetaBelowLeaf111031233 :
    adaptiveCoverCheck 9 (childHH thetaBelowCell11103123) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH thetaBelowCell11103123)
    (by
      have h : ((childLL (childHH thetaBelowCell11103123))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH thetaBelowCell11103123)) h)
    (by
      have h : ((childLH (childHH thetaBelowCell11103123))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH thetaBelowCell11103123)) h)
    (by
      have h : ((childHL (childHH thetaBelowCell11103123))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH thetaBelowCell11103123)) h)
    (by
      have h : ((childHH (childHH thetaBelowCell11103123))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH thetaBelowCell11103123)) h)
theorem e24KC2ThetaBelowLeaf111031320 :
    adaptiveCoverCheck 9 (childLL thetaBelowCell11103132) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL thetaBelowCell11103132)
    (by
      have h : ((childLL (childLL thetaBelowCell11103132))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL thetaBelowCell11103132)) h)
    (by
      have h : ((childLH (childLL thetaBelowCell11103132))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL thetaBelowCell11103132)) h)
    (by
      have h : ((childHL (childLL thetaBelowCell11103132))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL thetaBelowCell11103132)) h)
    (by
      have h : ((childHH (childLL thetaBelowCell11103132))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL thetaBelowCell11103132)) h)
theorem e24KC2ThetaBelowLeaf111031321 :
    adaptiveCoverCheck 9 (childLH thetaBelowCell11103132) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH thetaBelowCell11103132)
    (by
      have h : ((childLL (childLH thetaBelowCell11103132))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH thetaBelowCell11103132)) h)
    (by
      have h : ((childLH (childLH thetaBelowCell11103132))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH thetaBelowCell11103132)) h)
    (by
      have h : ((childHL (childLH thetaBelowCell11103132))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH thetaBelowCell11103132)) h)
    (by
      have h : ((childHH (childLH thetaBelowCell11103132))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH thetaBelowCell11103132)) h)
theorem e24KC2ThetaBelowLeaf111031322 :
    adaptiveCoverCheck 9 (childHL thetaBelowCell11103132) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL thetaBelowCell11103132)
    (by
      have h : ((childLL (childHL thetaBelowCell11103132))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL thetaBelowCell11103132)) h)
    (by
      have h : ((childLH (childHL thetaBelowCell11103132))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL thetaBelowCell11103132)) h)
    (by
      have h : ((childHL (childHL thetaBelowCell11103132))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL thetaBelowCell11103132)) h)
    (by
      have h : ((childHH (childHL thetaBelowCell11103132))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL thetaBelowCell11103132)) h)
theorem e24KC2ThetaBelowLeaf111031323 :
    adaptiveCoverCheck 9 (childHH thetaBelowCell11103132) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH thetaBelowCell11103132)
    (by
      have h : ((childLL (childHH thetaBelowCell11103132))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH thetaBelowCell11103132)) h)
    (by
      have h : ((childLH (childHH thetaBelowCell11103132))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH thetaBelowCell11103132)) h)
    (by
      have h : ((childHL (childHH thetaBelowCell11103132))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH thetaBelowCell11103132)) h)
    (by
      have h : ((childHH (childHH thetaBelowCell11103132))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH thetaBelowCell11103132)) h)
theorem e24KC2ThetaBelowLeaf111031330 :
    adaptiveCoverCheck 9 (childLL thetaBelowCell11103133) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL thetaBelowCell11103133)
    (by
      have h : ((childLL (childLL thetaBelowCell11103133))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL thetaBelowCell11103133)) h)
    (by
      have h : ((childLH (childLL thetaBelowCell11103133))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL thetaBelowCell11103133)) h)
    (by
      have h : ((childHL (childLL thetaBelowCell11103133))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL thetaBelowCell11103133)) h)
    (by
      have h : ((childHH (childLL thetaBelowCell11103133))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL thetaBelowCell11103133)) h)
theorem e24KC2ThetaBelowLeaf111031331 :
    adaptiveCoverCheck 9 (childLH thetaBelowCell11103133) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH thetaBelowCell11103133)
    (by
      have h : ((childLL (childLH thetaBelowCell11103133))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH thetaBelowCell11103133)) h)
    (by
      have h : ((childLH (childLH thetaBelowCell11103133))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH thetaBelowCell11103133)) h)
    (by
      have h : ((childHL (childLH thetaBelowCell11103133))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH thetaBelowCell11103133)) h)
    (by
      have h : ((childHH (childLH thetaBelowCell11103133))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH thetaBelowCell11103133)) h)
theorem e24KC2ThetaBelowLeaf111031332 :
    adaptiveCoverCheck 9 (childHL thetaBelowCell11103133) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL thetaBelowCell11103133)
    (by
      have h : ((childLL (childHL thetaBelowCell11103133))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL thetaBelowCell11103133)) h)
    (by
      have h : ((childLH (childHL thetaBelowCell11103133))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL thetaBelowCell11103133)) h)
    (by
      have h : ((childHL (childHL thetaBelowCell11103133))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL thetaBelowCell11103133)) h)
    (by
      have h : ((childHH (childHL thetaBelowCell11103133))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL thetaBelowCell11103133)) h)
theorem e24KC2ThetaBelowLeaf111031333 :
    adaptiveCoverCheck 9 (childHH thetaBelowCell11103133) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH thetaBelowCell11103133)
    (by
      have h : ((childLL (childHH thetaBelowCell11103133))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH thetaBelowCell11103133)) h)
    (by
      have h : ((childLH (childHH thetaBelowCell11103133))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH thetaBelowCell11103133)) h)
    (by
      have h : ((childHL (childHH thetaBelowCell11103133))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH thetaBelowCell11103133)) h)
    (by
      have h : ((childHH (childHH thetaBelowCell11103133))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH thetaBelowCell11103133)) h)
theorem e24KC2ThetaBelowLeaf111032100 :
    adaptiveCoverCheck 9 (childLL thetaBelowCell11103210) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL thetaBelowCell11103210)
    (by
      have h : ((childLL (childLL thetaBelowCell11103210))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL thetaBelowCell11103210)) h)
    (by
      have h : ((childLH (childLL thetaBelowCell11103210))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL thetaBelowCell11103210)) h)
    (by
      have h : ((childHL (childLL thetaBelowCell11103210))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL thetaBelowCell11103210)) h)
    (by
      have h : ((childHH (childLL thetaBelowCell11103210))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL thetaBelowCell11103210)) h)
theorem e24KC2ThetaBelowLeaf111032101 :
    adaptiveCoverCheck 9 (childLH thetaBelowCell11103210) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH thetaBelowCell11103210)
    (by
      have h : ((childLL (childLH thetaBelowCell11103210))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH thetaBelowCell11103210)) h)
    (by
      have h : ((childLH (childLH thetaBelowCell11103210))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH thetaBelowCell11103210)) h)
    (by
      have h : ((childHL (childLH thetaBelowCell11103210))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH thetaBelowCell11103210)) h)
    (by
      have h : ((childHH (childLH thetaBelowCell11103210))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH thetaBelowCell11103210)) h)
theorem e24KC2ThetaBelowLeaf111032110 :
    adaptiveCoverCheck 9 (childLL thetaBelowCell11103211) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL thetaBelowCell11103211)
    (by
      have h : ((childLL (childLL thetaBelowCell11103211))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL thetaBelowCell11103211)) h)
    (by
      have h : ((childLH (childLL thetaBelowCell11103211))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL thetaBelowCell11103211)) h)
    (by
      have h : ((childHL (childLL thetaBelowCell11103211))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL thetaBelowCell11103211)) h)
    (by
      have h : ((childHH (childLL thetaBelowCell11103211))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL thetaBelowCell11103211)) h)
theorem e24KC2ThetaBelowLeaf111032111 :
    adaptiveCoverCheck 9 (childLH thetaBelowCell11103211) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH thetaBelowCell11103211)
    (by
      have h : ((childLL (childLH thetaBelowCell11103211))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH thetaBelowCell11103211)) h)
    (by
      have h : ((childLH (childLH thetaBelowCell11103211))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH thetaBelowCell11103211)) h)
    (by
      have h : ((childHL (childLH thetaBelowCell11103211))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH thetaBelowCell11103211)) h)
    (by
      have h : ((childHH (childLH thetaBelowCell11103211))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH thetaBelowCell11103211)) h)
theorem e24KC2ThetaBelowLeaf111033000 :
    adaptiveCoverCheck 9 (childLL thetaBelowCell11103300) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL thetaBelowCell11103300)
    (by
      have h : ((childLL (childLL thetaBelowCell11103300))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL thetaBelowCell11103300)) h)
    (by
      have h : ((childLH (childLL thetaBelowCell11103300))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL thetaBelowCell11103300)) h)
    (by
      have h : ((childHL (childLL thetaBelowCell11103300))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL thetaBelowCell11103300)) h)
    (by
      have h : ((childHH (childLL thetaBelowCell11103300))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL thetaBelowCell11103300)) h)
theorem e24KC2ThetaBelowLeaf111033001 :
    adaptiveCoverCheck 9 (childLH thetaBelowCell11103300) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH thetaBelowCell11103300)
    (by
      have h : ((childLL (childLH thetaBelowCell11103300))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH thetaBelowCell11103300)) h)
    (by
      have h : ((childLH (childLH thetaBelowCell11103300))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH thetaBelowCell11103300)) h)
    (by
      have h : ((childHL (childLH thetaBelowCell11103300))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH thetaBelowCell11103300)) h)
    (by
      have h : ((childHH (childLH thetaBelowCell11103300))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH thetaBelowCell11103300)) h)
theorem e24KC2ThetaBelowLeaf111033010 :
    adaptiveCoverCheck 9 (childLL thetaBelowCell11103301) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL thetaBelowCell11103301)
    (by
      have h : ((childLL (childLL thetaBelowCell11103301))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL thetaBelowCell11103301)) h)
    (by
      have h : ((childLH (childLL thetaBelowCell11103301))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL thetaBelowCell11103301)) h)
    (by
      have h : ((childHL (childLL thetaBelowCell11103301))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL thetaBelowCell11103301)) h)
    (by
      have h : ((childHH (childLL thetaBelowCell11103301))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL thetaBelowCell11103301)) h)
theorem e24KC2ThetaBelowLeaf111033011 :
    adaptiveCoverCheck 9 (childLH thetaBelowCell11103301) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH thetaBelowCell11103301)
    (by
      have h : ((childLL (childLH thetaBelowCell11103301))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH thetaBelowCell11103301)) h)
    (by
      have h : ((childLH (childLH thetaBelowCell11103301))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH thetaBelowCell11103301)) h)
    (by
      have h : ((childHL (childLH thetaBelowCell11103301))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH thetaBelowCell11103301)) h)
    (by
      have h : ((childHH (childLH thetaBelowCell11103301))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH thetaBelowCell11103301)) h)
theorem e24KC2ThetaBelowLeaf111033100 :
    adaptiveCoverCheck 9 (childLL thetaBelowCell11103310) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL thetaBelowCell11103310)
    (by
      have h : ((childLL (childLL thetaBelowCell11103310))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL thetaBelowCell11103310)) h)
    (by
      have h : ((childLH (childLL thetaBelowCell11103310))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL thetaBelowCell11103310)) h)
    (by
      have h : ((childHL (childLL thetaBelowCell11103310))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL thetaBelowCell11103310)) h)
    (by
      have h : ((childHH (childLL thetaBelowCell11103310))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL thetaBelowCell11103310)) h)
theorem e24KC2ThetaBelowLeaf111033101 :
    adaptiveCoverCheck 9 (childLH thetaBelowCell11103310) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH thetaBelowCell11103310)
    (by
      have h : ((childLL (childLH thetaBelowCell11103310))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH thetaBelowCell11103310)) h)
    (by
      have h : ((childLH (childLH thetaBelowCell11103310))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH thetaBelowCell11103310)) h)
    (by
      have h : ((childHL (childLH thetaBelowCell11103310))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH thetaBelowCell11103310)) h)
    (by
      have h : ((childHH (childLH thetaBelowCell11103310))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH thetaBelowCell11103310)) h)
theorem e24KC2ThetaBelowLeaf111033110 :
    adaptiveCoverCheck 9 (childLL thetaBelowCell11103311) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL thetaBelowCell11103311)
    (by
      have h : ((childLL (childLL thetaBelowCell11103311))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL thetaBelowCell11103311)) h)
    (by
      have h : ((childLH (childLL thetaBelowCell11103311))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL thetaBelowCell11103311)) h)
    (by
      have h : ((childHL (childLL thetaBelowCell11103311))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL thetaBelowCell11103311)) h)
    (by
      have h : ((childHH (childLL thetaBelowCell11103311))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL thetaBelowCell11103311)) h)
theorem e24KC2ThetaBelowLeaf111033111 :
    adaptiveCoverCheck 9 (childLH thetaBelowCell11103311) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH thetaBelowCell11103311)
    (by
      have h : ((childLL (childLH thetaBelowCell11103311))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH thetaBelowCell11103311)) h)
    (by
      have h : ((childLH (childLH thetaBelowCell11103311))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH thetaBelowCell11103311)) h)
    (by
      have h : ((childHL (childLH thetaBelowCell11103311))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH thetaBelowCell11103311)) h)
    (by
      have h : ((childHH (childLH thetaBelowCell11103311))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH thetaBelowCell11103311)) h)
theorem e24KC2ThetaBelowLeaf111120220 :
    adaptiveCoverCheck 9 (childLL thetaBelowCell11112022) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL thetaBelowCell11112022)
    (by
      have h : ((childLL (childLL thetaBelowCell11112022))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL thetaBelowCell11112022)) h)
    (by
      have h : ((childLH (childLL thetaBelowCell11112022))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL thetaBelowCell11112022)) h)
    (by
      have h : ((childHL (childLL thetaBelowCell11112022))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL thetaBelowCell11112022)) h)
    (by
      have h : ((childHH (childLL thetaBelowCell11112022))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL thetaBelowCell11112022)) h)
theorem e24KC2ThetaBelowLeaf111120221 :
    adaptiveCoverCheck 9 (childLH thetaBelowCell11112022) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH thetaBelowCell11112022)
    (by
      have h : ((childLL (childLH thetaBelowCell11112022))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH thetaBelowCell11112022)) h)
    (by
      have h : ((childLH (childLH thetaBelowCell11112022))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH thetaBelowCell11112022)) h)
    (by
      have h : ((childHL (childLH thetaBelowCell11112022))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH thetaBelowCell11112022)) h)
    (by
      have h : ((childHH (childLH thetaBelowCell11112022))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH thetaBelowCell11112022)) h)
theorem e24KC2ThetaBelowLeaf111120222 :
    adaptiveCoverCheck 9 (childHL thetaBelowCell11112022) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL thetaBelowCell11112022)
    (by
      have h : ((childLL (childHL thetaBelowCell11112022))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL thetaBelowCell11112022)) h)
    (by
      have h : ((childLH (childHL thetaBelowCell11112022))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL thetaBelowCell11112022)) h)
    (by
      have h : ((childHL (childHL thetaBelowCell11112022))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL thetaBelowCell11112022)) h)
    (by
      have h : ((childHH (childHL thetaBelowCell11112022))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL thetaBelowCell11112022)) h)
theorem e24KC2ThetaBelowLeaf111120223 :
    adaptiveCoverCheck 9 (childHH thetaBelowCell11112022) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH thetaBelowCell11112022)
    (by
      have h : ((childLL (childHH thetaBelowCell11112022))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH thetaBelowCell11112022)) h)
    (by
      have h : ((childLH (childHH thetaBelowCell11112022))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH thetaBelowCell11112022)) h)
    (by
      have h : ((childHL (childHH thetaBelowCell11112022))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH thetaBelowCell11112022)) h)
    (by
      have h : ((childHH (childHH thetaBelowCell11112022))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH thetaBelowCell11112022)) h)
theorem e24KC2ThetaBelowLeaf111120230 :
    adaptiveCoverCheck 9 (childLL thetaBelowCell11112023) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL thetaBelowCell11112023)
    (by
      have h : ((childLL (childLL thetaBelowCell11112023))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL thetaBelowCell11112023)) h)
    (by
      have h : ((childLH (childLL thetaBelowCell11112023))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL thetaBelowCell11112023)) h)
    (by
      have h : ((childHL (childLL thetaBelowCell11112023))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL thetaBelowCell11112023)) h)
    (by
      have h : ((childHH (childLL thetaBelowCell11112023))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL thetaBelowCell11112023)) h)
theorem e24KC2ThetaBelowLeaf111120231 :
    adaptiveCoverCheck 9 (childLH thetaBelowCell11112023) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH thetaBelowCell11112023)
    (by
      have h : ((childLL (childLH thetaBelowCell11112023))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH thetaBelowCell11112023)) h)
    (by
      have h : ((childLH (childLH thetaBelowCell11112023))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH thetaBelowCell11112023)) h)
    (by
      have h : ((childHL (childLH thetaBelowCell11112023))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH thetaBelowCell11112023)) h)
    (by
      have h : ((childHH (childLH thetaBelowCell11112023))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH thetaBelowCell11112023)) h)
theorem e24KC2ThetaBelowLeaf111120232 :
    adaptiveCoverCheck 9 (childHL thetaBelowCell11112023) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL thetaBelowCell11112023)
    (by
      have h : ((childLL (childHL thetaBelowCell11112023))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL thetaBelowCell11112023)) h)
    (by
      have h : ((childLH (childHL thetaBelowCell11112023))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL thetaBelowCell11112023)) h)
    (by
      have h : ((childHL (childHL thetaBelowCell11112023))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL thetaBelowCell11112023)) h)
    (by
      have h : ((childHH (childHL thetaBelowCell11112023))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL thetaBelowCell11112023)) h)
theorem e24KC2ThetaBelowLeaf111120233 :
    adaptiveCoverCheck 9 (childHH thetaBelowCell11112023) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH thetaBelowCell11112023)
    (by
      have h : ((childLL (childHH thetaBelowCell11112023))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH thetaBelowCell11112023)) h)
    (by
      have h : ((childLH (childHH thetaBelowCell11112023))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH thetaBelowCell11112023)) h)
    (by
      have h : ((childHL (childHH thetaBelowCell11112023))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH thetaBelowCell11112023)) h)
    (by
      have h : ((childHH (childHH thetaBelowCell11112023))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH thetaBelowCell11112023)) h)
theorem e24KC2ThetaBelowLeaf111120320 :
    adaptiveCoverCheck 9 (childLL thetaBelowCell11112032) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL thetaBelowCell11112032)
    (by
      have h : ((childLL (childLL thetaBelowCell11112032))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL thetaBelowCell11112032)) h)
    (by
      have h : ((childLH (childLL thetaBelowCell11112032))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL thetaBelowCell11112032)) h)
    (by
      have h : ((childHL (childLL thetaBelowCell11112032))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL thetaBelowCell11112032)) h)
    (by
      have h : ((childHH (childLL thetaBelowCell11112032))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL thetaBelowCell11112032)) h)
theorem e24KC2ThetaBelowLeaf111120321 :
    adaptiveCoverCheck 9 (childLH thetaBelowCell11112032) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH thetaBelowCell11112032)
    (by
      have h : ((childLL (childLH thetaBelowCell11112032))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH thetaBelowCell11112032)) h)
    (by
      have h : ((childLH (childLH thetaBelowCell11112032))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH thetaBelowCell11112032)) h)
    (by
      have h : ((childHL (childLH thetaBelowCell11112032))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH thetaBelowCell11112032)) h)
    (by
      have h : ((childHH (childLH thetaBelowCell11112032))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH thetaBelowCell11112032)) h)
theorem e24KC2ThetaBelowLeaf111120322 :
    adaptiveCoverCheck 9 (childHL thetaBelowCell11112032) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL thetaBelowCell11112032)
    (by
      have h : ((childLL (childHL thetaBelowCell11112032))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL thetaBelowCell11112032)) h)
    (by
      have h : ((childLH (childHL thetaBelowCell11112032))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL thetaBelowCell11112032)) h)
    (by
      have h : ((childHL (childHL thetaBelowCell11112032))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL thetaBelowCell11112032)) h)
    (by
      have h : ((childHH (childHL thetaBelowCell11112032))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL thetaBelowCell11112032)) h)
theorem e24KC2ThetaBelowLeaf111120323 :
    adaptiveCoverCheck 9 (childHH thetaBelowCell11112032) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH thetaBelowCell11112032)
    (by
      have h : ((childLL (childHH thetaBelowCell11112032))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH thetaBelowCell11112032)) h)
    (by
      have h : ((childLH (childHH thetaBelowCell11112032))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH thetaBelowCell11112032)) h)
    (by
      have h : ((childHL (childHH thetaBelowCell11112032))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH thetaBelowCell11112032)) h)
    (by
      have h : ((childHH (childHH thetaBelowCell11112032))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH thetaBelowCell11112032)) h)
theorem e24KC2ThetaBelowLeaf111120330 :
    adaptiveCoverCheck 9 (childLL thetaBelowCell11112033) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL thetaBelowCell11112033)
    (by
      have h : ((childLL (childLL thetaBelowCell11112033))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL thetaBelowCell11112033)) h)
    (by
      have h : ((childLH (childLL thetaBelowCell11112033))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL thetaBelowCell11112033)) h)
    (by
      have h : ((childHL (childLL thetaBelowCell11112033))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL thetaBelowCell11112033)) h)
    (by
      have h : ((childHH (childLL thetaBelowCell11112033))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL thetaBelowCell11112033)) h)
theorem e24KC2ThetaBelowLeaf111120331 :
    adaptiveCoverCheck 9 (childLH thetaBelowCell11112033) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH thetaBelowCell11112033)
    (by
      have h : ((childLL (childLH thetaBelowCell11112033))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH thetaBelowCell11112033)) h)
    (by
      have h : ((childLH (childLH thetaBelowCell11112033))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH thetaBelowCell11112033)) h)
    (by
      have h : ((childHL (childLH thetaBelowCell11112033))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH thetaBelowCell11112033)) h)
    (by
      have h : ((childHH (childLH thetaBelowCell11112033))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH thetaBelowCell11112033)) h)
theorem e24KC2ThetaBelowLeaf111120332 :
    adaptiveCoverCheck 9 (childHL thetaBelowCell11112033) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL thetaBelowCell11112033)
    (by
      have h : ((childLL (childHL thetaBelowCell11112033))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL thetaBelowCell11112033)) h)
    (by
      have h : ((childLH (childHL thetaBelowCell11112033))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL thetaBelowCell11112033)) h)
    (by
      have h : ((childHL (childHL thetaBelowCell11112033))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL thetaBelowCell11112033)) h)
    (by
      have h : ((childHH (childHL thetaBelowCell11112033))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL thetaBelowCell11112033)) h)
theorem e24KC2ThetaBelowLeaf111120333 :
    adaptiveCoverCheck 9 (childHH thetaBelowCell11112033) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH thetaBelowCell11112033)
    (by
      have h : ((childLL (childHH thetaBelowCell11112033))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH thetaBelowCell11112033)) h)
    (by
      have h : ((childLH (childHH thetaBelowCell11112033))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH thetaBelowCell11112033)) h)
    (by
      have h : ((childHL (childHH thetaBelowCell11112033))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH thetaBelowCell11112033)) h)
    (by
      have h : ((childHH (childHH thetaBelowCell11112033))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH thetaBelowCell11112033)) h)
theorem e24KC2ThetaBelowLeaf111121220 :
    adaptiveCoverCheck 9 (childLL thetaBelowCell11112122) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL thetaBelowCell11112122)
    (by
      have h : ((childLL (childLL thetaBelowCell11112122))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL thetaBelowCell11112122)) h)
    (by
      have h : ((childLH (childLL thetaBelowCell11112122))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL thetaBelowCell11112122)) h)
    (by
      have h : ((childHL (childLL thetaBelowCell11112122))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL thetaBelowCell11112122)) h)
    (by
      have h : ((childHH (childLL thetaBelowCell11112122))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL thetaBelowCell11112122)) h)
theorem e24KC2ThetaBelowLeaf111121221 :
    adaptiveCoverCheck 9 (childLH thetaBelowCell11112122) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH thetaBelowCell11112122)
    (by
      have h : ((childLL (childLH thetaBelowCell11112122))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH thetaBelowCell11112122)) h)
    (by
      have h : ((childLH (childLH thetaBelowCell11112122))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH thetaBelowCell11112122)) h)
    (by
      have h : ((childHL (childLH thetaBelowCell11112122))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH thetaBelowCell11112122)) h)
    (by
      have h : ((childHH (childLH thetaBelowCell11112122))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH thetaBelowCell11112122)) h)
theorem e24KC2ThetaBelowLeaf111121222 :
    adaptiveCoverCheck 9 (childHL thetaBelowCell11112122) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL thetaBelowCell11112122)
    (by
      have h : ((childLL (childHL thetaBelowCell11112122))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL thetaBelowCell11112122)) h)
    (by
      have h : ((childLH (childHL thetaBelowCell11112122))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL thetaBelowCell11112122)) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childHL thetaBelowCell11112122))
        (by
          have h : ((childLL (childHL (childHL thetaBelowCell11112122)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHL (childHL
            thetaBelowCell11112122))) h)
        (by
          have h : ((childLH (childHL (childHL thetaBelowCell11112122)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHL (childHL
            thetaBelowCell11112122))) h)
        (by
          have h : ((childHL (childHL (childHL thetaBelowCell11112122)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHL (childHL
            thetaBelowCell11112122))) h)
        (by
          have h : ((childHH (childHL (childHL thetaBelowCell11112122)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHL (childHL
            thetaBelowCell11112122))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childHL thetaBelowCell11112122))
        (by
          have h : ((childLL (childHH (childHL thetaBelowCell11112122)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHH (childHL
            thetaBelowCell11112122))) h)
        (by
          have h : ((childLH (childHH (childHL thetaBelowCell11112122)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHH (childHL
            thetaBelowCell11112122))) h)
        (by
          have h : ((childHL (childHH (childHL thetaBelowCell11112122)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHH (childHL
            thetaBelowCell11112122))) h)
        (by
          have h : ((childHH (childHH (childHL thetaBelowCell11112122)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHH (childHL
            thetaBelowCell11112122))) h))
theorem e24KC2ThetaBelowLeaf111121223 :
    adaptiveCoverCheck 9 (childHH thetaBelowCell11112122) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH thetaBelowCell11112122)
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childHH thetaBelowCell11112122))
        (by
          have h : ((childLL (childLL (childHH thetaBelowCell11112122)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLL (childHH
            thetaBelowCell11112122))) h)
        (by
          have h : ((childLH (childLL (childHH thetaBelowCell11112122)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLL (childHH
            thetaBelowCell11112122))) h)
        (by
          have h : ((childHL (childLL (childHH thetaBelowCell11112122)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLL (childHH
            thetaBelowCell11112122))) h)
        (by
          have h : ((childHH (childLL (childHH thetaBelowCell11112122)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLL (childHH
            thetaBelowCell11112122))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childHH thetaBelowCell11112122))
        (by
          have h : ((childLL (childLH (childHH thetaBelowCell11112122)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLH (childHH
            thetaBelowCell11112122))) h)
        (by
          have h : ((childLH (childLH (childHH thetaBelowCell11112122)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLH (childHH
            thetaBelowCell11112122))) h)
        (by
          have h : ((childHL (childLH (childHH thetaBelowCell11112122)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLH (childHH
            thetaBelowCell11112122))) h)
        (by
          have h : ((childHH (childLH (childHH thetaBelowCell11112122)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLH (childHH
            thetaBelowCell11112122))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childHH thetaBelowCell11112122))
        (by
          have h : ((childLL (childHL (childHH thetaBelowCell11112122)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHL (childHH
            thetaBelowCell11112122))) h)
        (by
          have h : ((childLH (childHL (childHH thetaBelowCell11112122)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHL (childHH
            thetaBelowCell11112122))) h)
        (by
          have h : ((childHL (childHL (childHH thetaBelowCell11112122)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHL (childHH
            thetaBelowCell11112122))) h)
        (by
          have h : ((childHH (childHL (childHH thetaBelowCell11112122)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHL (childHH
            thetaBelowCell11112122))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childHH thetaBelowCell11112122))
        (by
          have h : ((childLL (childHH (childHH thetaBelowCell11112122)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHH (childHH
            thetaBelowCell11112122))) h)
        (by
          have h : ((childLH (childHH (childHH thetaBelowCell11112122)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHH (childHH
            thetaBelowCell11112122))) h)
        (by
          have h : ((childHL (childHH (childHH thetaBelowCell11112122)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHH (childHH
            thetaBelowCell11112122))) h)
        (by
          have h : ((childHH (childHH (childHH thetaBelowCell11112122)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHH (childHH
            thetaBelowCell11112122))) h))
theorem e24KC2ThetaBelowLeaf111121230 :
    adaptiveCoverCheck 9 (childLL thetaBelowCell11112123) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL thetaBelowCell11112123)
    (by
      have h : ((childLL (childLL thetaBelowCell11112123))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL thetaBelowCell11112123)) h)
    (by
      have h : ((childLH (childLL thetaBelowCell11112123))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL thetaBelowCell11112123)) h)
    (by
      have h : ((childHL (childLL thetaBelowCell11112123))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL thetaBelowCell11112123)) h)
    (by
      have h : ((childHH (childLL thetaBelowCell11112123))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL thetaBelowCell11112123)) h)
theorem e24KC2ThetaBelowLeaf111121231 :
    adaptiveCoverCheck 9 (childLH thetaBelowCell11112123) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH thetaBelowCell11112123)
    (by
      have h : ((childLL (childLH thetaBelowCell11112123))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH thetaBelowCell11112123)) h)
    (by
      have h : ((childLH (childLH thetaBelowCell11112123))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH thetaBelowCell11112123)) h)
    (by
      have h : ((childHL (childLH thetaBelowCell11112123))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH thetaBelowCell11112123)) h)
    (by
      have h : ((childHH (childLH thetaBelowCell11112123))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH thetaBelowCell11112123)) h)
theorem e24KC2ThetaBelowLeaf111121232 :
    adaptiveCoverCheck 9 (childHL thetaBelowCell11112123) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL thetaBelowCell11112123)
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childHL thetaBelowCell11112123))
        (by
          have h : ((childLL (childLL (childHL thetaBelowCell11112123)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLL (childHL
            thetaBelowCell11112123))) h)
        (by
          have h : ((childLH (childLL (childHL thetaBelowCell11112123)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLL (childHL
            thetaBelowCell11112123))) h)
        (by
          have h : ((childHL (childLL (childHL thetaBelowCell11112123)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLL (childHL
            thetaBelowCell11112123))) h)
        (by
          have h : ((childHH (childLL (childHL thetaBelowCell11112123)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLL (childHL
            thetaBelowCell11112123))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childHL thetaBelowCell11112123))
        (by
          have h : ((childLL (childLH (childHL thetaBelowCell11112123)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLH (childHL
            thetaBelowCell11112123))) h)
        (by
          have h : ((childLH (childLH (childHL thetaBelowCell11112123)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLH (childHL
            thetaBelowCell11112123))) h)
        (by
          have h : ((childHL (childLH (childHL thetaBelowCell11112123)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLH (childHL
            thetaBelowCell11112123))) h)
        (by
          have h : ((childHH (childLH (childHL thetaBelowCell11112123)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLH (childHL
            thetaBelowCell11112123))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childHL thetaBelowCell11112123))
        (by
          have h : ((childLL (childHL (childHL thetaBelowCell11112123)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHL (childHL
            thetaBelowCell11112123))) h)
        (by
          have h : ((childLH (childHL (childHL thetaBelowCell11112123)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHL (childHL
            thetaBelowCell11112123))) h)
        (by
          have h : ((childHL (childHL (childHL thetaBelowCell11112123)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHL (childHL
            thetaBelowCell11112123))) h)
        (by
          have h : ((childHH (childHL (childHL thetaBelowCell11112123)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHL (childHL
            thetaBelowCell11112123))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childHL thetaBelowCell11112123))
        (by
          have h : ((childLL (childHH (childHL thetaBelowCell11112123)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHH (childHL
            thetaBelowCell11112123))) h)
        (by
          have h : ((childLH (childHH (childHL thetaBelowCell11112123)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHH (childHL
            thetaBelowCell11112123))) h)
        (by
          have h : ((childHL (childHH (childHL thetaBelowCell11112123)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHH (childHL
            thetaBelowCell11112123))) h)
        (by
          have h : ((childHH (childHH (childHL thetaBelowCell11112123)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHH (childHL
            thetaBelowCell11112123))) h))
theorem e24KC2ThetaBelowLeaf111121233 :
    adaptiveCoverCheck 9 (childHH thetaBelowCell11112123) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH thetaBelowCell11112123)
    (by
      have h : ((childLL (childHH thetaBelowCell11112123))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH thetaBelowCell11112123)) h)
    (by
      have h : ((childLH (childHH thetaBelowCell11112123))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH thetaBelowCell11112123)) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childHH thetaBelowCell11112123))
        (by
          have h : ((childLL (childHL (childHH thetaBelowCell11112123)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHL (childHH
            thetaBelowCell11112123))) h)
        (by
          have h : ((childLH (childHL (childHH thetaBelowCell11112123)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHL (childHH
            thetaBelowCell11112123))) h)
        (by
          have h : ((childHL (childHL (childHH thetaBelowCell11112123)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHL (childHH
            thetaBelowCell11112123))) h)
        (by
          have h : ((childHH (childHL (childHH thetaBelowCell11112123)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHL (childHH
            thetaBelowCell11112123))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childHH thetaBelowCell11112123))
        (by
          have h : ((childLL (childHH (childHH thetaBelowCell11112123)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHH (childHH
            thetaBelowCell11112123))) h)
        (by
          have h : ((childLH (childHH (childHH thetaBelowCell11112123)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHH (childHH
            thetaBelowCell11112123))) h)
        (by
          have h : ((childHL (childHH (childHH thetaBelowCell11112123)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHH (childHH
            thetaBelowCell11112123))) h)
        (by
          have h : ((childHH (childHH (childHH thetaBelowCell11112123)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHH (childHH
            thetaBelowCell11112123))) h))
theorem e24KC2ThetaBelowLeaf111121322 :
    adaptiveCoverCheck 9 (childHL thetaBelowCell11112132) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL thetaBelowCell11112132)
    (by
      have h : ((childLL (childHL thetaBelowCell11112132))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL thetaBelowCell11112132)) h)
    (by
      have h : ((childLH (childHL thetaBelowCell11112132))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL thetaBelowCell11112132)) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childHL thetaBelowCell11112132))
        (by
          have h : ((childLL (childHL (childHL thetaBelowCell11112132)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHL (childHL
            thetaBelowCell11112132))) h)
        (by
          have h : ((childLH (childHL (childHL thetaBelowCell11112132)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHL (childHL
            thetaBelowCell11112132))) h)
        (by
          have h : ((childHL (childHL (childHL thetaBelowCell11112132)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHL (childHL
            thetaBelowCell11112132))) h)
        (by
          have h : ((childHH (childHL (childHL thetaBelowCell11112132)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHL (childHL
            thetaBelowCell11112132))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childHL thetaBelowCell11112132))
        (by
          have h : ((childLL (childHH (childHL thetaBelowCell11112132)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHH (childHL
            thetaBelowCell11112132))) h)
        (by
          have h : ((childLH (childHH (childHL thetaBelowCell11112132)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHH (childHL
            thetaBelowCell11112132))) h)
        (by
          have h : ((childHL (childHH (childHL thetaBelowCell11112132)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHH (childHL
            thetaBelowCell11112132))) h)
        (by
          have h : ((childHH (childHH (childHL thetaBelowCell11112132)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHH (childHL
            thetaBelowCell11112132))) h))
theorem e24KC2ThetaBelowLeaf111121323 :
    adaptiveCoverCheck 9 (childHH thetaBelowCell11112132) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH thetaBelowCell11112132)
    (by
      have h : ((childLL (childHH thetaBelowCell11112132))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH thetaBelowCell11112132)) h)
    (by
      have h : ((childLH (childHH thetaBelowCell11112132))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH thetaBelowCell11112132)) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childHH thetaBelowCell11112132))
        (by
          have h : ((childLL (childHL (childHH thetaBelowCell11112132)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHL (childHH
            thetaBelowCell11112132))) h)
        (by
          have h : ((childLH (childHL (childHH thetaBelowCell11112132)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHL (childHH
            thetaBelowCell11112132))) h)
        (by
          have h : ((childHL (childHL (childHH thetaBelowCell11112132)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHL (childHH
            thetaBelowCell11112132))) h)
        (by
          have h : ((childHH (childHL (childHH thetaBelowCell11112132)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHL (childHH
            thetaBelowCell11112132))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childHH thetaBelowCell11112132))
        (by
          have h : ((childLL (childHH (childHH thetaBelowCell11112132)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHH (childHH
            thetaBelowCell11112132))) h)
        (by
          have h : ((childLH (childHH (childHH thetaBelowCell11112132)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHH (childHH
            thetaBelowCell11112132))) h)
        (by
          have h : ((childHL (childHH (childHH thetaBelowCell11112132)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHH (childHH
            thetaBelowCell11112132))) h)
        (by
          have h : ((childHH (childHH (childHH thetaBelowCell11112132)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHH (childHH
            thetaBelowCell11112132))) h))
theorem e24KC2ThetaBelowLeaf111121332 :
    adaptiveCoverCheck 9 (childHL thetaBelowCell11112133) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL thetaBelowCell11112133)
    (by
      have h : ((childLL (childHL thetaBelowCell11112133))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL thetaBelowCell11112133)) h)
    (by
      have h : ((childLH (childHL thetaBelowCell11112133))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL thetaBelowCell11112133)) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childHL thetaBelowCell11112133))
        (by
          have h : ((childLL (childHL (childHL thetaBelowCell11112133)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHL (childHL
            thetaBelowCell11112133))) h)
        (by
          have h : ((childLH (childHL (childHL thetaBelowCell11112133)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHL (childHL
            thetaBelowCell11112133))) h)
        (by
          have h : ((childHL (childHL (childHL thetaBelowCell11112133)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHL (childHL
            thetaBelowCell11112133))) h)
        (by
          have h : ((childHH (childHL (childHL thetaBelowCell11112133)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHL (childHL
            thetaBelowCell11112133))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childHL thetaBelowCell11112133))
        (by
          have h : ((childLL (childHH (childHL thetaBelowCell11112133)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHH (childHL
            thetaBelowCell11112133))) h)
        (by
          have h : ((childLH (childHH (childHL thetaBelowCell11112133)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHH (childHL
            thetaBelowCell11112133))) h)
        (by
          have h : ((childHL (childHH (childHL thetaBelowCell11112133)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHH (childHL
            thetaBelowCell11112133))) h)
        (by
          have h : ((childHH (childHH (childHL thetaBelowCell11112133)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHH (childHL
            thetaBelowCell11112133))) h))
theorem e24KC2ThetaBelowLeaf111121333 :
    adaptiveCoverCheck 9 (childHH thetaBelowCell11112133) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH thetaBelowCell11112133)
    (by
      have h : ((childLL (childHH thetaBelowCell11112133))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH thetaBelowCell11112133)) h)
    (by
      have h : ((childLH (childHH thetaBelowCell11112133))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH thetaBelowCell11112133)) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childHH thetaBelowCell11112133))
        (by
          have h : ((childLL (childHL (childHH thetaBelowCell11112133)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHL (childHH
            thetaBelowCell11112133))) h)
        (by
          have h : ((childLH (childHL (childHH thetaBelowCell11112133)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHL (childHH
            thetaBelowCell11112133))) h)
        (by
          have h : ((childHL (childHL (childHH thetaBelowCell11112133)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHL (childHH
            thetaBelowCell11112133))) h)
        (by
          have h : ((childHH (childHL (childHH thetaBelowCell11112133)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHL (childHH
            thetaBelowCell11112133))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childHH thetaBelowCell11112133))
        (by
          have h : ((childLL (childHH (childHH thetaBelowCell11112133)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHH (childHH
            thetaBelowCell11112133))) h)
        (by
          have h : ((childLH (childHH (childHH thetaBelowCell11112133)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHH (childHH
            thetaBelowCell11112133))) h)
        (by
          have h : ((childHL (childHH (childHH thetaBelowCell11112133)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHH (childHH
            thetaBelowCell11112133))) h)
        (by
          have h : ((childHH (childHH (childHH thetaBelowCell11112133)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHH (childHH
            thetaBelowCell11112133))) h))
theorem e24KC2ThetaBelowLeaf111122000 :
    adaptiveCoverCheck 9 (childLL thetaBelowCell11112200) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL thetaBelowCell11112200)
    (by
      have h : ((childLL (childLL thetaBelowCell11112200))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL thetaBelowCell11112200)) h)
    (by
      have h : ((childLH (childLL thetaBelowCell11112200))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL thetaBelowCell11112200)) h)
    (by
      have h : ((childHL (childLL thetaBelowCell11112200))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL thetaBelowCell11112200)) h)
    (by
      have h : ((childHH (childLL thetaBelowCell11112200))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL thetaBelowCell11112200)) h)
theorem e24KC2ThetaBelowLeaf111122001 :
    adaptiveCoverCheck 9 (childLH thetaBelowCell11112200) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH thetaBelowCell11112200)
    (by
      have h : ((childLL (childLH thetaBelowCell11112200))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH thetaBelowCell11112200)) h)
    (by
      have h : ((childLH (childLH thetaBelowCell11112200))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH thetaBelowCell11112200)) h)
    (by
      have h : ((childHL (childLH thetaBelowCell11112200))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH thetaBelowCell11112200)) h)
    (by
      have h : ((childHH (childLH thetaBelowCell11112200))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH thetaBelowCell11112200)) h)
theorem e24KC2ThetaBelowLeaf111122010 :
    adaptiveCoverCheck 9 (childLL thetaBelowCell11112201) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL thetaBelowCell11112201)
    (by
      have h : ((childLL (childLL thetaBelowCell11112201))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL thetaBelowCell11112201)) h)
    (by
      have h : ((childLH (childLL thetaBelowCell11112201))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL thetaBelowCell11112201)) h)
    (by
      have h : ((childHL (childLL thetaBelowCell11112201))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL thetaBelowCell11112201)) h)
    (by
      have h : ((childHH (childLL thetaBelowCell11112201))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL thetaBelowCell11112201)) h)
theorem e24KC2ThetaBelowLeaf111122011 :
    adaptiveCoverCheck 9 (childLH thetaBelowCell11112201) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH thetaBelowCell11112201)
    (by
      have h : ((childLL (childLH thetaBelowCell11112201))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH thetaBelowCell11112201)) h)
    (by
      have h : ((childLH (childLH thetaBelowCell11112201))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH thetaBelowCell11112201)) h)
    (by
      have h : ((childHL (childLH thetaBelowCell11112201))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH thetaBelowCell11112201)) h)
    (by
      have h : ((childHH (childLH thetaBelowCell11112201))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH thetaBelowCell11112201)) h)
theorem e24KC2ThetaBelowLeaf111122100 :
    adaptiveCoverCheck 9 (childLL thetaBelowCell11112210) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL thetaBelowCell11112210)
    (by
      have h : ((childLL (childLL thetaBelowCell11112210))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL thetaBelowCell11112210)) h)
    (by
      have h : ((childLH (childLL thetaBelowCell11112210))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL thetaBelowCell11112210)) h)
    (by
      have h : ((childHL (childLL thetaBelowCell11112210))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL thetaBelowCell11112210)) h)
    (by
      have h : ((childHH (childLL thetaBelowCell11112210))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL thetaBelowCell11112210)) h)
theorem e24KC2ThetaBelowLeaf111122101 :
    adaptiveCoverCheck 9 (childLH thetaBelowCell11112210) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH thetaBelowCell11112210)
    (by
      have h : ((childLL (childLH thetaBelowCell11112210))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH thetaBelowCell11112210)) h)
    (by
      have h : ((childLH (childLH thetaBelowCell11112210))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH thetaBelowCell11112210)) h)
    (by
      have h : ((childHL (childLH thetaBelowCell11112210))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH thetaBelowCell11112210)) h)
    (by
      have h : ((childHH (childLH thetaBelowCell11112210))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH thetaBelowCell11112210)) h)
theorem e24KC2ThetaBelowLeaf111122110 :
    adaptiveCoverCheck 9 (childLL thetaBelowCell11112211) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL thetaBelowCell11112211)
    (by
      have h : ((childLL (childLL thetaBelowCell11112211))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL thetaBelowCell11112211)) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLL thetaBelowCell11112211))
        (by
          have h : ((childLL (childLH (childLL thetaBelowCell11112211)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLH (childLL
            thetaBelowCell11112211))) h)
        (by
          have h : ((childLH (childLH (childLL thetaBelowCell11112211)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLH (childLL
            thetaBelowCell11112211))) h)
        (by
          have h : ((childHL (childLH (childLL thetaBelowCell11112211)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLH (childLL
            thetaBelowCell11112211))) h)
        (by
          have h : ((childHH (childLH (childLL thetaBelowCell11112211)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLH (childLL
            thetaBelowCell11112211))) h))
    (by
      have h : ((childHL (childLL thetaBelowCell11112211))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL thetaBelowCell11112211)) h)
    (by
      have h : ((childHH (childLL thetaBelowCell11112211))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL thetaBelowCell11112211)) h)
theorem e24KC2ThetaBelowLeaf111122111 :
    adaptiveCoverCheck 9 (childLH thetaBelowCell11112211) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH thetaBelowCell11112211)
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLH thetaBelowCell11112211))
        (by
          have h : ((childLL (childLL (childLH thetaBelowCell11112211)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLL (childLH
            thetaBelowCell11112211))) h)
        (by
          have h : ((childLH (childLL (childLH thetaBelowCell11112211)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLL (childLH
            thetaBelowCell11112211))) h)
        (by
          have h : ((childHL (childLL (childLH thetaBelowCell11112211)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLL (childLH
            thetaBelowCell11112211))) h)
        (by
          have h : ((childHH (childLL (childLH thetaBelowCell11112211)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLL (childLH
            thetaBelowCell11112211))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLH thetaBelowCell11112211))
        (by
          have h : ((childLL (childLH (childLH thetaBelowCell11112211)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLH (childLH
            thetaBelowCell11112211))) h)
        (by
          have h : ((childLH (childLH (childLH thetaBelowCell11112211)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLH (childLH
            thetaBelowCell11112211))) h)
        (by
          have h : ((childHL (childLH (childLH thetaBelowCell11112211)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLH (childLH
            thetaBelowCell11112211))) h)
        (by
          have h : ((childHH (childLH (childLH thetaBelowCell11112211)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLH (childLH
            thetaBelowCell11112211))) h))
    (by
      have h : ((childHL (childLH thetaBelowCell11112211))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH thetaBelowCell11112211)) h)
    (by
      have h : ((childHH (childLH thetaBelowCell11112211))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH thetaBelowCell11112211)) h)
theorem e24KC2ThetaBelowLeaf111122113 :
    adaptiveCoverCheck 9 (childHH thetaBelowCell11112211) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH thetaBelowCell11112211)
    (by
      have h : ((childLL (childHH thetaBelowCell11112211))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH thetaBelowCell11112211)) h)
    (by
      have h : ((childLH (childHH thetaBelowCell11112211))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH thetaBelowCell11112211)) h)
    (by
      have h : ((childHL (childHH thetaBelowCell11112211))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH thetaBelowCell11112211)) h)
    (by
      have h : ((childHH (childHH thetaBelowCell11112211))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH thetaBelowCell11112211)) h)
theorem e24KC2ThetaBelowLeaf111123000 :
    adaptiveCoverCheck 9 (childLL thetaBelowCell11112300) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL thetaBelowCell11112300)
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLL thetaBelowCell11112300))
        (by
          have h : ((childLL (childLL (childLL thetaBelowCell11112300)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLL (childLL
            thetaBelowCell11112300))) h)
        (by
          have h : ((childLH (childLL (childLL thetaBelowCell11112300)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLL (childLL
            thetaBelowCell11112300))) h)
        (by
          have h : ((childHL (childLL (childLL thetaBelowCell11112300)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLL (childLL
            thetaBelowCell11112300))) h)
        (by
          have h : ((childHH (childLL (childLL thetaBelowCell11112300)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLL (childLL
            thetaBelowCell11112300))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLL thetaBelowCell11112300))
        (by
          have h : ((childLL (childLH (childLL thetaBelowCell11112300)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLH (childLL
            thetaBelowCell11112300))) h)
        (by
          have h : ((childLH (childLH (childLL thetaBelowCell11112300)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLH (childLL
            thetaBelowCell11112300))) h)
        (by
          have h : ((childHL (childLH (childLL thetaBelowCell11112300)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLH (childLL
            thetaBelowCell11112300))) h)
        (by
          have h : ((childHH (childLH (childLL thetaBelowCell11112300)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLH (childLL
            thetaBelowCell11112300))) h))
    (by
      have h : ((childHL (childLL thetaBelowCell11112300))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL thetaBelowCell11112300)) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLL thetaBelowCell11112300))
        (by
          have h : ((childLL (childHH (childLL thetaBelowCell11112300)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHH (childLL
            thetaBelowCell11112300))) h)
        (by
          have h : ((childLH (childHH (childLL thetaBelowCell11112300)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHH (childLL
            thetaBelowCell11112300))) h)
        (by
          have h : ((childHL (childHH (childLL thetaBelowCell11112300)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHH (childLL
            thetaBelowCell11112300))) h)
        (by
          have h : ((childHH (childHH (childLL thetaBelowCell11112300)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHH (childLL
            thetaBelowCell11112300))) h))
theorem e24KC2ThetaBelowLeaf111123001 :
    adaptiveCoverCheck 9 (childLH thetaBelowCell11112300) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH thetaBelowCell11112300)
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLH thetaBelowCell11112300))
        (by
          have h : ((childLL (childLL (childLH thetaBelowCell11112300)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLL (childLH
            thetaBelowCell11112300))) h)
        (by
          have h : ((childLH (childLL (childLH thetaBelowCell11112300)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLL (childLH
            thetaBelowCell11112300))) h)
        (by
          have h : ((childHL (childLL (childLH thetaBelowCell11112300)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLL (childLH
            thetaBelowCell11112300))) h)
        (by
          have h : ((childHH (childLL (childLH thetaBelowCell11112300)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLL (childLH
            thetaBelowCell11112300))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLH thetaBelowCell11112300))
        (by
          have h : ((childLL (childLH (childLH thetaBelowCell11112300)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLH (childLH
            thetaBelowCell11112300))) h)
        (by
          have h : ((childLH (childLH (childLH thetaBelowCell11112300)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLH (childLH
            thetaBelowCell11112300))) h)
        (by
          have h : ((childHL (childLH (childLH thetaBelowCell11112300)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLH (childLH
            thetaBelowCell11112300))) h)
        (by
          have h : ((childHH (childLH (childLH thetaBelowCell11112300)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLH (childLH
            thetaBelowCell11112300))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLH thetaBelowCell11112300))
        (by
          have h : ((childLL (childHL (childLH thetaBelowCell11112300)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHL (childLH
            thetaBelowCell11112300))) h)
        (by
          have h : ((childLH (childHL (childLH thetaBelowCell11112300)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHL (childLH
            thetaBelowCell11112300))) h)
        (by
          have h : ((childHL (childHL (childLH thetaBelowCell11112300)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHL (childLH
            thetaBelowCell11112300))) h)
        (by
          have h : ((childHH (childHL (childLH thetaBelowCell11112300)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHL (childLH
            thetaBelowCell11112300))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLH thetaBelowCell11112300))
        (by
          have h : ((childLL (childHH (childLH thetaBelowCell11112300)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHH (childLH
            thetaBelowCell11112300))) h)
        (by
          have h : ((childLH (childHH (childLH thetaBelowCell11112300)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHH (childLH
            thetaBelowCell11112300))) h)
        (by
          have h : ((childHL (childHH (childLH thetaBelowCell11112300)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHH (childLH
            thetaBelowCell11112300))) h)
        (by
          have h : ((childHH (childHH (childLH thetaBelowCell11112300)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHH (childLH
            thetaBelowCell11112300))) h))
theorem e24KC2ThetaBelowLeaf111123002 :
    adaptiveCoverCheck 9 (childHL thetaBelowCell11112300) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL thetaBelowCell11112300)
    (by
      have h : ((childLL (childHL thetaBelowCell11112300))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL thetaBelowCell11112300)) h)
    (by
      have h : ((childLH (childHL thetaBelowCell11112300))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL thetaBelowCell11112300)) h)
    (by
      have h : ((childHL (childHL thetaBelowCell11112300))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL thetaBelowCell11112300)) h)
    (by
      have h : ((childHH (childHL thetaBelowCell11112300))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL thetaBelowCell11112300)) h)
theorem e24KC2ThetaBelowLeaf111123003 :
    adaptiveCoverCheck 9 (childHH thetaBelowCell11112300) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH thetaBelowCell11112300)
    (by
      have h : ((childLL (childHH thetaBelowCell11112300))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH thetaBelowCell11112300)) h)
    (by
      have h : ((childLH (childHH thetaBelowCell11112300))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH thetaBelowCell11112300)) h)
    (by
      have h : ((childHL (childHH thetaBelowCell11112300))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH thetaBelowCell11112300)) h)
    (by
      have h : ((childHH (childHH thetaBelowCell11112300))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH thetaBelowCell11112300)) h)
theorem e24KC2ThetaBelowLeaf111123010 :
    adaptiveCoverCheck 9 (childLL thetaBelowCell11112301) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL thetaBelowCell11112301)
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLL thetaBelowCell11112301))
        (by
          have h : ((childLL (childLL (childLL thetaBelowCell11112301)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLL (childLL
            thetaBelowCell11112301))) h)
        (by
          have h : ((childLH (childLL (childLL thetaBelowCell11112301)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLL (childLL
            thetaBelowCell11112301))) h)
        (by
          have h : ((childHL (childLL (childLL thetaBelowCell11112301)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLL (childLL
            thetaBelowCell11112301))) h)
        (by
          have h : ((childHH (childLL (childLL thetaBelowCell11112301)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLL (childLL
            thetaBelowCell11112301))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLL thetaBelowCell11112301))
        (by
          have h : ((childLL (childLH (childLL thetaBelowCell11112301)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLH (childLL
            thetaBelowCell11112301))) h)
        (by
          have h : ((childLH (childLH (childLL thetaBelowCell11112301)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLH (childLL
            thetaBelowCell11112301))) h)
        (by
          have h : ((childHL (childLH (childLL thetaBelowCell11112301)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLH (childLL
            thetaBelowCell11112301))) h)
        (by
          have h : ((childHH (childLH (childLL thetaBelowCell11112301)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLH (childLL
            thetaBelowCell11112301))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLL thetaBelowCell11112301))
        (by
          have h : ((childLL (childHL (childLL thetaBelowCell11112301)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHL (childLL
            thetaBelowCell11112301))) h)
        (by
          have h : ((childLH (childHL (childLL thetaBelowCell11112301)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHL (childLL
            thetaBelowCell11112301))) h)
        (by
          have h : ((childHL (childHL (childLL thetaBelowCell11112301)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHL (childLL
            thetaBelowCell11112301))) h)
        (by
          have h : ((childHH (childHL (childLL thetaBelowCell11112301)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHL (childLL
            thetaBelowCell11112301))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLL thetaBelowCell11112301))
        (by
          have h : ((childLL (childHH (childLL thetaBelowCell11112301)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHH (childLL
            thetaBelowCell11112301))) h)
        (by
          have h : ((childLH (childHH (childLL thetaBelowCell11112301)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHH (childLL
            thetaBelowCell11112301))) h)
        (by
          have h : ((childHL (childHH (childLL thetaBelowCell11112301)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHH (childLL
            thetaBelowCell11112301))) h)
        (by
          have h : ((childHH (childHH (childLL thetaBelowCell11112301)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHH (childLL
            thetaBelowCell11112301))) h))
theorem e24KC2ThetaBelowLeaf111123011 :
    adaptiveCoverCheck 9 (childLH thetaBelowCell11112301) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH thetaBelowCell11112301)
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLH thetaBelowCell11112301))
        (by
          have h : ((childLL (childLL (childLH thetaBelowCell11112301)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLL (childLH
            thetaBelowCell11112301))) h)
        (by
          have h : ((childLH (childLL (childLH thetaBelowCell11112301)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLL (childLH
            thetaBelowCell11112301))) h)
        (by
          have h : ((childHL (childLL (childLH thetaBelowCell11112301)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLL (childLH
            thetaBelowCell11112301))) h)
        (by
          have h : ((childHH (childLL (childLH thetaBelowCell11112301)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLL (childLH
            thetaBelowCell11112301))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLH thetaBelowCell11112301))
        (by
          have h : ((childLL (childLH (childLH thetaBelowCell11112301)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLH (childLH
            thetaBelowCell11112301))) h)
        (by
          have h : ((childLH (childLH (childLH thetaBelowCell11112301)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLH (childLH
            thetaBelowCell11112301))) h)
        (by
          have h : ((childHL (childLH (childLH thetaBelowCell11112301)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLH (childLH
            thetaBelowCell11112301))) h)
        (by
          have h : ((childHH (childLH (childLH thetaBelowCell11112301)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLH (childLH
            thetaBelowCell11112301))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLH thetaBelowCell11112301))
        (by
          have h : ((childLL (childHL (childLH thetaBelowCell11112301)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHL (childLH
            thetaBelowCell11112301))) h)
        (by
          have h : ((childLH (childHL (childLH thetaBelowCell11112301)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHL (childLH
            thetaBelowCell11112301))) h)
        (by
          have h : ((childHL (childHL (childLH thetaBelowCell11112301)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHL (childLH
            thetaBelowCell11112301))) h)
        (by
          have h : ((childHH (childHL (childLH thetaBelowCell11112301)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHL (childLH
            thetaBelowCell11112301))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLH thetaBelowCell11112301))
        (by
          have h : ((childLL (childHH (childLH thetaBelowCell11112301)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHH (childLH
            thetaBelowCell11112301))) h)
        (by
          have h : ((childLH (childHH (childLH thetaBelowCell11112301)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHH (childLH
            thetaBelowCell11112301))) h)
        (by
          have h : ((childHL (childHH (childLH thetaBelowCell11112301)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHH (childLH
            thetaBelowCell11112301))) h)
        (by
          have h : ((childHH (childHH (childLH thetaBelowCell11112301)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHH (childLH
            thetaBelowCell11112301))) h))
theorem e24KC2ThetaBelowLeaf111123012 :
    adaptiveCoverCheck 9 (childHL thetaBelowCell11112301) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL thetaBelowCell11112301)
    (by
      have h : ((childLL (childHL thetaBelowCell11112301))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL thetaBelowCell11112301)) h)
    (by
      have h : ((childLH (childHL thetaBelowCell11112301))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL thetaBelowCell11112301)) h)
    (by
      have h : ((childHL (childHL thetaBelowCell11112301))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL thetaBelowCell11112301)) h)
    (by
      have h : ((childHH (childHL thetaBelowCell11112301))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL thetaBelowCell11112301)) h)
theorem e24KC2ThetaBelowLeaf111123013 :
    adaptiveCoverCheck 9 (childHH thetaBelowCell11112301) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH thetaBelowCell11112301)
    (by
      have h : ((childLL (childHH thetaBelowCell11112301))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH thetaBelowCell11112301)) h)
    (by
      have h : ((childLH (childHH thetaBelowCell11112301))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH thetaBelowCell11112301)) h)
    (by
      have h : ((childHL (childHH thetaBelowCell11112301))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH thetaBelowCell11112301)) h)
    (by
      have h : ((childHH (childHH thetaBelowCell11112301))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH thetaBelowCell11112301)) h)
theorem e24KC2ThetaBelowLeaf111123100 :
    adaptiveCoverCheck 9 (childLL thetaBelowCell11112310) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL thetaBelowCell11112310)
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLL thetaBelowCell11112310))
        (by
          have h : ((childLL (childLL (childLL thetaBelowCell11112310)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLL (childLL
            thetaBelowCell11112310))) h)
        (by
          have h : ((childLH (childLL (childLL thetaBelowCell11112310)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLL (childLL
            thetaBelowCell11112310))) h)
        (by
          have h : ((childHL (childLL (childLL thetaBelowCell11112310)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLL (childLL
            thetaBelowCell11112310))) h)
        (by
          have h : ((childHH (childLL (childLL thetaBelowCell11112310)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLL (childLL
            thetaBelowCell11112310))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLL thetaBelowCell11112310))
        (by
          have h : ((childLL (childLH (childLL thetaBelowCell11112310)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLH (childLL
            thetaBelowCell11112310))) h)
        (by
          have h : ((childLH (childLH (childLL thetaBelowCell11112310)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLH (childLL
            thetaBelowCell11112310))) h)
        (by
          have h : ((childHL (childLH (childLL thetaBelowCell11112310)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLH (childLL
            thetaBelowCell11112310))) h)
        (by
          have h : ((childHH (childLH (childLL thetaBelowCell11112310)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLH (childLL
            thetaBelowCell11112310))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLL thetaBelowCell11112310))
        (by
          have h : ((childLL (childHL (childLL thetaBelowCell11112310)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHL (childLL
            thetaBelowCell11112310))) h)
        (by
          have h : ((childLH (childHL (childLL thetaBelowCell11112310)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHL (childLL
            thetaBelowCell11112310))) h)
        (by
          have h : ((childHL (childHL (childLL thetaBelowCell11112310)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHL (childLL
            thetaBelowCell11112310))) h)
        (by
          have h : ((childHH (childHL (childLL thetaBelowCell11112310)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHL (childLL
            thetaBelowCell11112310))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLL thetaBelowCell11112310))
        (by
          have h : ((childLL (childHH (childLL thetaBelowCell11112310)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHH (childLL
            thetaBelowCell11112310))) h)
        (by
          have h : ((childLH (childHH (childLL thetaBelowCell11112310)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHH (childLL
            thetaBelowCell11112310))) h)
        (by
          have h : ((childHL (childHH (childLL thetaBelowCell11112310)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHH (childLL
            thetaBelowCell11112310))) h)
        (by
          have h : ((childHH (childHH (childLL thetaBelowCell11112310)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHH (childLL
            thetaBelowCell11112310))) h))
theorem e24KC2ThetaBelowLeaf111123101 :
    adaptiveCoverCheck 9 (childLH thetaBelowCell11112310) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH thetaBelowCell11112310)
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLH thetaBelowCell11112310))
        (by
          have h : ((childLL (childLL (childLH thetaBelowCell11112310)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLL (childLH
            thetaBelowCell11112310))) h)
        (by
          have h : ((childLH (childLL (childLH thetaBelowCell11112310)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLL (childLH
            thetaBelowCell11112310))) h)
        (by
          have h : ((childHL (childLL (childLH thetaBelowCell11112310)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLL (childLH
            thetaBelowCell11112310))) h)
        (by
          have h : ((childHH (childLL (childLH thetaBelowCell11112310)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLL (childLH
            thetaBelowCell11112310))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLH thetaBelowCell11112310))
        (by
          have h : ((childLL (childLH (childLH thetaBelowCell11112310)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLH (childLH
            thetaBelowCell11112310))) h)
        (by
          have h : ((childLH (childLH (childLH thetaBelowCell11112310)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLH (childLH
            thetaBelowCell11112310))) h)
        (by
          have h : ((childHL (childLH (childLH thetaBelowCell11112310)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLH (childLH
            thetaBelowCell11112310))) h)
        (by
          have h : ((childHH (childLH (childLH thetaBelowCell11112310)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLH (childLH
            thetaBelowCell11112310))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLH thetaBelowCell11112310))
        (by
          have h : ((childLL (childHL (childLH thetaBelowCell11112310)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHL (childLH
            thetaBelowCell11112310))) h)
        (by
          have h : ((childLH (childHL (childLH thetaBelowCell11112310)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHL (childLH
            thetaBelowCell11112310))) h)
        (by
          have h : ((childHL (childHL (childLH thetaBelowCell11112310)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHL (childLH
            thetaBelowCell11112310))) h)
        (by
          have h : ((childHH (childHL (childLH thetaBelowCell11112310)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHL (childLH
            thetaBelowCell11112310))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLH thetaBelowCell11112310))
        (by
          have h : ((childLL (childHH (childLH thetaBelowCell11112310)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHH (childLH
            thetaBelowCell11112310))) h)
        (by
          have h : ((childLH (childHH (childLH thetaBelowCell11112310)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHH (childLH
            thetaBelowCell11112310))) h)
        (by
          have h : ((childHL (childHH (childLH thetaBelowCell11112310)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHH (childLH
            thetaBelowCell11112310))) h)
        (by
          have h : ((childHH (childHH (childLH thetaBelowCell11112310)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHH (childLH
            thetaBelowCell11112310))) h))
theorem e24KC2ThetaBelowLeaf111123102 :
    adaptiveCoverCheck 9 (childHL thetaBelowCell11112310) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL thetaBelowCell11112310)
    (by
      have h : ((childLL (childHL thetaBelowCell11112310))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL thetaBelowCell11112310)) h)
    (by
      have h : ((childLH (childHL thetaBelowCell11112310))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL thetaBelowCell11112310)) h)
    (by
      have h : ((childHL (childHL thetaBelowCell11112310))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL thetaBelowCell11112310)) h)
    (by
      have h : ((childHH (childHL thetaBelowCell11112310))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL thetaBelowCell11112310)) h)
theorem e24KC2ThetaBelowLeaf111123103 :
    adaptiveCoverCheck 9 (childHH thetaBelowCell11112310) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH thetaBelowCell11112310)
    (by
      have h : ((childLL (childHH thetaBelowCell11112310))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH thetaBelowCell11112310)) h)
    (by
      have h : ((childLH (childHH thetaBelowCell11112310))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH thetaBelowCell11112310)) h)
    (by
      have h : ((childHL (childHH thetaBelowCell11112310))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH thetaBelowCell11112310)) h)
    (by
      have h : ((childHH (childHH thetaBelowCell11112310))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH thetaBelowCell11112310)) h)
theorem e24KC2ThetaBelowLeaf111123110 :
    adaptiveCoverCheck 9 (childLL thetaBelowCell11112311) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL thetaBelowCell11112311)
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLL thetaBelowCell11112311))
        (by
          have h : ((childLL (childLL (childLL thetaBelowCell11112311)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLL (childLL
            thetaBelowCell11112311))) h)
        (by
          have h : ((childLH (childLL (childLL thetaBelowCell11112311)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLL (childLL
            thetaBelowCell11112311))) h)
        (by
          have h : ((childHL (childLL (childLL thetaBelowCell11112311)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLL (childLL
            thetaBelowCell11112311))) h)
        (by
          have h : ((childHH (childLL (childLL thetaBelowCell11112311)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLL (childLL
            thetaBelowCell11112311))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLL thetaBelowCell11112311))
        (by
          have h : ((childLL (childLH (childLL thetaBelowCell11112311)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLH (childLL
            thetaBelowCell11112311))) h)
        (by
          have h : ((childLH (childLH (childLL thetaBelowCell11112311)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLH (childLL
            thetaBelowCell11112311))) h)
        (by
          have h : ((childHL (childLH (childLL thetaBelowCell11112311)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLH (childLL
            thetaBelowCell11112311))) h)
        (by
          have h : ((childHH (childLH (childLL thetaBelowCell11112311)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLH (childLL
            thetaBelowCell11112311))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLL thetaBelowCell11112311))
        (by
          have h : ((childLL (childHL (childLL thetaBelowCell11112311)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHL (childLL
            thetaBelowCell11112311))) h)
        (by
          have h : ((childLH (childHL (childLL thetaBelowCell11112311)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHL (childLL
            thetaBelowCell11112311))) h)
        (by
          have h : ((childHL (childHL (childLL thetaBelowCell11112311)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHL (childLL
            thetaBelowCell11112311))) h)
        (by
          have h : ((childHH (childHL (childLL thetaBelowCell11112311)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHL (childLL
            thetaBelowCell11112311))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLL thetaBelowCell11112311))
        (by
          have h : ((childLL (childHH (childLL thetaBelowCell11112311)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHH (childLL
            thetaBelowCell11112311))) h)
        (by
          have h : ((childLH (childHH (childLL thetaBelowCell11112311)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHH (childLL
            thetaBelowCell11112311))) h)
        (by
          have h : ((childHL (childHH (childLL thetaBelowCell11112311)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHH (childLL
            thetaBelowCell11112311))) h)
        (by
          have h : ((childHH (childHH (childLL thetaBelowCell11112311)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHH (childLL
            thetaBelowCell11112311))) h))
theorem e24KC2ThetaBelowLeaf111123111 :
    adaptiveCoverCheck 9 (childLH thetaBelowCell11112311) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH thetaBelowCell11112311)
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLH thetaBelowCell11112311))
        (by
          have h : ((childLL (childLL (childLH thetaBelowCell11112311)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLL (childLH
            thetaBelowCell11112311))) h)
        (by
          have h : ((childLH (childLL (childLH thetaBelowCell11112311)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLL (childLH
            thetaBelowCell11112311))) h)
        (by
          have h : ((childHL (childLL (childLH thetaBelowCell11112311)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLL (childLH
            thetaBelowCell11112311))) h)
        (by
          have h : ((childHH (childLL (childLH thetaBelowCell11112311)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLL (childLH
            thetaBelowCell11112311))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLH thetaBelowCell11112311))
        (by
          have h : ((childLL (childLH (childLH thetaBelowCell11112311)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLH (childLH
            thetaBelowCell11112311))) h)
        (by
          have h : ((childLH (childLH (childLH thetaBelowCell11112311)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLH (childLH
            thetaBelowCell11112311))) h)
        (by
          have h : ((childHL (childLH (childLH thetaBelowCell11112311)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLH (childLH
            thetaBelowCell11112311))) h)
        (by
          have h : ((childHH (childLH (childLH thetaBelowCell11112311)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLH (childLH
            thetaBelowCell11112311))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLH thetaBelowCell11112311))
        (by
          have h : ((childLL (childHL (childLH thetaBelowCell11112311)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHL (childLH
            thetaBelowCell11112311))) h)
        (by
          have h : ((childLH (childHL (childLH thetaBelowCell11112311)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHL (childLH
            thetaBelowCell11112311))) h)
        (by
          have h : ((childHL (childHL (childLH thetaBelowCell11112311)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHL (childLH
            thetaBelowCell11112311))) h)
        (by
          have h : ((childHH (childHL (childLH thetaBelowCell11112311)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHL (childLH
            thetaBelowCell11112311))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLH thetaBelowCell11112311))
        (by
          have h : ((childLL (childHH (childLH thetaBelowCell11112311)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHH (childLH
            thetaBelowCell11112311))) h)
        (by
          have h : ((childLH (childHH (childLH thetaBelowCell11112311)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHH (childLH
            thetaBelowCell11112311))) h)
        (by
          have h : ((childHL (childHH (childLH thetaBelowCell11112311)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHH (childLH
            thetaBelowCell11112311))) h)
        (by
          have h : ((childHH (childHH (childLH thetaBelowCell11112311)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHH (childLH
            thetaBelowCell11112311))) h))
theorem e24KC2ThetaBelowLeaf111123112 :
    adaptiveCoverCheck 9 (childHL thetaBelowCell11112311) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL thetaBelowCell11112311)
    (by
      have h : ((childLL (childHL thetaBelowCell11112311))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL thetaBelowCell11112311)) h)
    (by
      have h : ((childLH (childHL thetaBelowCell11112311))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL thetaBelowCell11112311)) h)
    (by
      have h : ((childHL (childHL thetaBelowCell11112311))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL thetaBelowCell11112311)) h)
    (by
      have h : ((childHH (childHL thetaBelowCell11112311))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL thetaBelowCell11112311)) h)
theorem e24KC2ThetaBelowLeaf111123113 :
    adaptiveCoverCheck 9 (childHH thetaBelowCell11112311) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH thetaBelowCell11112311)
    (by
      have h : ((childLL (childHH thetaBelowCell11112311))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH thetaBelowCell11112311)) h)
    (by
      have h : ((childLH (childHH thetaBelowCell11112311))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH thetaBelowCell11112311)) h)
    (by
      have h : ((childHL (childHH thetaBelowCell11112311))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH thetaBelowCell11112311)) h)
    (by
      have h : ((childHH (childHH thetaBelowCell11112311))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH thetaBelowCell11112311)) h)
theorem e24KC2ThetaBelowLeaf111130222 :
    adaptiveCoverCheck 9 (childHL thetaBelowCell11113022) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL thetaBelowCell11113022)
    (by
      have h : ((childLL (childHL thetaBelowCell11113022))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL thetaBelowCell11113022)) h)
    (by
      have h : ((childLH (childHL thetaBelowCell11113022))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL thetaBelowCell11113022)) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childHL thetaBelowCell11113022))
        (by
          have h : ((childLL (childHL (childHL thetaBelowCell11113022)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHL (childHL
            thetaBelowCell11113022))) h)
        (by
          have h : ((childLH (childHL (childHL thetaBelowCell11113022)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHL (childHL
            thetaBelowCell11113022))) h)
        (by
          have h : ((childHL (childHL (childHL thetaBelowCell11113022)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHL (childHL
            thetaBelowCell11113022))) h)
        (by
          have h : ((childHH (childHL (childHL thetaBelowCell11113022)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHL (childHL
            thetaBelowCell11113022))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childHL thetaBelowCell11113022))
        (by
          have h : ((childLL (childHH (childHL thetaBelowCell11113022)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHH (childHL
            thetaBelowCell11113022))) h)
        (by
          have h : ((childLH (childHH (childHL thetaBelowCell11113022)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHH (childHL
            thetaBelowCell11113022))) h)
        (by
          have h : ((childHL (childHH (childHL thetaBelowCell11113022)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHH (childHL
            thetaBelowCell11113022))) h)
        (by
          have h : ((childHH (childHH (childHL thetaBelowCell11113022)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHH (childHL
            thetaBelowCell11113022))) h))
theorem e24KC2ThetaBelowLeaf111130223 :
    adaptiveCoverCheck 9 (childHH thetaBelowCell11113022) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH thetaBelowCell11113022)
    (by
      have h : ((childLL (childHH thetaBelowCell11113022))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH thetaBelowCell11113022)) h)
    (by
      have h : ((childLH (childHH thetaBelowCell11113022))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH thetaBelowCell11113022)) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childHH thetaBelowCell11113022))
        (by
          have h : ((childLL (childHL (childHH thetaBelowCell11113022)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHL (childHH
            thetaBelowCell11113022))) h)
        (by
          have h : ((childLH (childHL (childHH thetaBelowCell11113022)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHL (childHH
            thetaBelowCell11113022))) h)
        (by
          have h : ((childHL (childHL (childHH thetaBelowCell11113022)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHL (childHH
            thetaBelowCell11113022))) h)
        (by
          have h : ((childHH (childHL (childHH thetaBelowCell11113022)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHL (childHH
            thetaBelowCell11113022))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childHH thetaBelowCell11113022))
        (by
          have h : ((childLL (childHH (childHH thetaBelowCell11113022)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHH (childHH
            thetaBelowCell11113022))) h)
        (by
          have h : ((childLH (childHH (childHH thetaBelowCell11113022)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHH (childHH
            thetaBelowCell11113022))) h)
        (by
          have h : ((childHL (childHH (childHH thetaBelowCell11113022)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHH (childHH
            thetaBelowCell11113022))) h)
        (by
          have h : ((childHH (childHH (childHH thetaBelowCell11113022)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHH (childHH
            thetaBelowCell11113022))) h))
theorem e24KC2ThetaBelowLeaf111130232 :
    adaptiveCoverCheck 9 (childHL thetaBelowCell11113023) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL thetaBelowCell11113023)
    (by
      have h : ((childLL (childHL thetaBelowCell11113023))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL thetaBelowCell11113023)) h)
    (by
      have h : ((childLH (childHL thetaBelowCell11113023))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL thetaBelowCell11113023)) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childHL thetaBelowCell11113023))
        (by
          have h : ((childLL (childHL (childHL thetaBelowCell11113023)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHL (childHL
            thetaBelowCell11113023))) h)
        (by
          have h : ((childLH (childHL (childHL thetaBelowCell11113023)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHL (childHL
            thetaBelowCell11113023))) h)
        (by
          have h : ((childHL (childHL (childHL thetaBelowCell11113023)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHL (childHL
            thetaBelowCell11113023))) h)
        (by
          have h : ((childHH (childHL (childHL thetaBelowCell11113023)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHL (childHL
            thetaBelowCell11113023))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childHL thetaBelowCell11113023))
        (by
          have h : ((childLL (childHH (childHL thetaBelowCell11113023)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHH (childHL
            thetaBelowCell11113023))) h)
        (by
          have h : ((childLH (childHH (childHL thetaBelowCell11113023)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHH (childHL
            thetaBelowCell11113023))) h)
        (by
          have h : ((childHL (childHH (childHL thetaBelowCell11113023)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHH (childHL
            thetaBelowCell11113023))) h)
        (by
          have h : ((childHH (childHH (childHL thetaBelowCell11113023)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHH (childHL
            thetaBelowCell11113023))) h))
theorem e24KC2ThetaBelowLeaf111130233 :
    adaptiveCoverCheck 9 (childHH thetaBelowCell11113023) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH thetaBelowCell11113023)
    (by
      have h : ((childLL (childHH thetaBelowCell11113023))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH thetaBelowCell11113023)) h)
    (by
      have h : ((childLH (childHH thetaBelowCell11113023))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH thetaBelowCell11113023)) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childHH thetaBelowCell11113023))
        (by
          have h : ((childLL (childHL (childHH thetaBelowCell11113023)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHL (childHH
            thetaBelowCell11113023))) h)
        (by
          have h : ((childLH (childHL (childHH thetaBelowCell11113023)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHL (childHH
            thetaBelowCell11113023))) h)
        (by
          have h : ((childHL (childHL (childHH thetaBelowCell11113023)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHL (childHH
            thetaBelowCell11113023))) h)
        (by
          have h : ((childHH (childHL (childHH thetaBelowCell11113023)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHL (childHH
            thetaBelowCell11113023))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childHH thetaBelowCell11113023))
        (by
          have h : ((childLL (childHH (childHH thetaBelowCell11113023)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHH (childHH
            thetaBelowCell11113023))) h)
        (by
          have h : ((childLH (childHH (childHH thetaBelowCell11113023)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHH (childHH
            thetaBelowCell11113023))) h)
        (by
          have h : ((childHL (childHH (childHH thetaBelowCell11113023)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHH (childHH
            thetaBelowCell11113023))) h)
        (by
          have h : ((childHH (childHH (childHH thetaBelowCell11113023)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHH (childHH
            thetaBelowCell11113023))) h))
theorem e24KC2ThetaBelowLeaf111130322 :
    adaptiveCoverCheck 9 (childHL thetaBelowCell11113032) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL thetaBelowCell11113032)
    (by
      have h : ((childLL (childHL thetaBelowCell11113032))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL thetaBelowCell11113032)) h)
    (by
      have h : ((childLH (childHL thetaBelowCell11113032))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL thetaBelowCell11113032)) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childHL thetaBelowCell11113032))
        (by
          have h : ((childLL (childHL (childHL thetaBelowCell11113032)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHL (childHL
            thetaBelowCell11113032))) h)
        (by
          have h : ((childLH (childHL (childHL thetaBelowCell11113032)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHL (childHL
            thetaBelowCell11113032))) h)
        (by
          have h : ((childHL (childHL (childHL thetaBelowCell11113032)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHL (childHL
            thetaBelowCell11113032))) h)
        (by
          have h : ((childHH (childHL (childHL thetaBelowCell11113032)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHL (childHL
            thetaBelowCell11113032))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childHL thetaBelowCell11113032))
        (by
          have h : ((childLL (childHH (childHL thetaBelowCell11113032)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHH (childHL
            thetaBelowCell11113032))) h)
        (by
          have h : ((childLH (childHH (childHL thetaBelowCell11113032)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHH (childHL
            thetaBelowCell11113032))) h)
        (by
          have h : ((childHL (childHH (childHL thetaBelowCell11113032)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHH (childHL
            thetaBelowCell11113032))) h)
        (by
          have h : ((childHH (childHH (childHL thetaBelowCell11113032)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHH (childHL
            thetaBelowCell11113032))) h))
theorem e24KC2ThetaBelowLeaf111130323 :
    adaptiveCoverCheck 9 (childHH thetaBelowCell11113032) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH thetaBelowCell11113032)
    (by
      have h : ((childLL (childHH thetaBelowCell11113032))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH thetaBelowCell11113032)) h)
    (by
      have h : ((childLH (childHH thetaBelowCell11113032))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH thetaBelowCell11113032)) h)
    (by
      have h : ((childHL (childHH thetaBelowCell11113032))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH thetaBelowCell11113032)) h)
    (by
      have h : ((childHH (childHH thetaBelowCell11113032))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH thetaBelowCell11113032)) h)
theorem e24KC2ThetaBelowLeaf111130332 :
    adaptiveCoverCheck 9 (childHL thetaBelowCell11113033) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL thetaBelowCell11113033)
    (by
      have h : ((childLL (childHL thetaBelowCell11113033))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL thetaBelowCell11113033)) h)
    (by
      have h : ((childLH (childHL thetaBelowCell11113033))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL thetaBelowCell11113033)) h)
    (by
      have h : ((childHL (childHL thetaBelowCell11113033))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL thetaBelowCell11113033)) h)
    (by
      have h : ((childHH (childHL thetaBelowCell11113033))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL thetaBelowCell11113033)) h)
theorem e24KC2ThetaBelowLeaf111130333 :
    adaptiveCoverCheck 9 (childHH thetaBelowCell11113033) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH thetaBelowCell11113033)
    (by
      have h : ((childLL (childHH thetaBelowCell11113033))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH thetaBelowCell11113033)) h)
    (by
      have h : ((childLH (childHH thetaBelowCell11113033))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH thetaBelowCell11113033)) h)
    (by
      have h : ((childHL (childHH thetaBelowCell11113033))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH thetaBelowCell11113033)) h)
    (by
      have h : ((childHH (childHH thetaBelowCell11113033))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH thetaBelowCell11113033)) h)
theorem e24KC2ThetaBelowLeaf111131222 :
    adaptiveCoverCheck 9 (childHL thetaBelowCell11113122) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL thetaBelowCell11113122)
    (by
      have h : ((childLL (childHL thetaBelowCell11113122))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL thetaBelowCell11113122)) h)
    (by
      have h : ((childLH (childHL thetaBelowCell11113122))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL thetaBelowCell11113122)) h)
    (by
      have h : ((childHL (childHL thetaBelowCell11113122))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL thetaBelowCell11113122)) h)
    (by
      have h : ((childHH (childHL thetaBelowCell11113122))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL thetaBelowCell11113122)) h)
theorem e24KC2ThetaBelowLeaf111131223 :
    adaptiveCoverCheck 9 (childHH thetaBelowCell11113122) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH thetaBelowCell11113122)
    (by
      have h : ((childLL (childHH thetaBelowCell11113122))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH thetaBelowCell11113122)) h)
    (by
      have h : ((childLH (childHH thetaBelowCell11113122))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH thetaBelowCell11113122)) h)
    (by
      have h : ((childHL (childHH thetaBelowCell11113122))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH thetaBelowCell11113122)) h)
    (by
      have h : ((childHH (childHH thetaBelowCell11113122))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH thetaBelowCell11113122)) h)
theorem e24KC2ThetaBelowLeaf111131232 :
    adaptiveCoverCheck 9 (childHL thetaBelowCell11113123) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL thetaBelowCell11113123)
    (by
      have h : ((childLL (childHL thetaBelowCell11113123))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL thetaBelowCell11113123)) h)
    (by
      have h : ((childLH (childHL thetaBelowCell11113123))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL thetaBelowCell11113123)) h)
    (by
      have h : ((childHL (childHL thetaBelowCell11113123))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL thetaBelowCell11113123)) h)
    (by
      have h : ((childHH (childHL thetaBelowCell11113123))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL thetaBelowCell11113123)) h)
theorem e24KC2ThetaBelowLeaf111131233 :
    adaptiveCoverCheck 9 (childHH thetaBelowCell11113123) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH thetaBelowCell11113123)
    (by
      have h : ((childLL (childHH thetaBelowCell11113123))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH thetaBelowCell11113123)) h)
    (by
      have h : ((childLH (childHH thetaBelowCell11113123))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH thetaBelowCell11113123)) h)
    (by
      have h : ((childHL (childHH thetaBelowCell11113123))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH thetaBelowCell11113123)) h)
    (by
      have h : ((childHH (childHH thetaBelowCell11113123))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH thetaBelowCell11113123)) h)
theorem e24KC2ThetaBelowLeaf111131322 :
    adaptiveCoverCheck 9 (childHL thetaBelowCell11113132) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL thetaBelowCell11113132)
    (by
      have h : ((childLL (childHL thetaBelowCell11113132))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL thetaBelowCell11113132)) h)
    (by
      have h : ((childLH (childHL thetaBelowCell11113132))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL thetaBelowCell11113132)) h)
    (by
      have h : ((childHL (childHL thetaBelowCell11113132))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL thetaBelowCell11113132)) h)
    (by
      have h : ((childHH (childHL thetaBelowCell11113132))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL thetaBelowCell11113132)) h)
theorem e24KC2ThetaBelowLeaf111131323 :
    adaptiveCoverCheck 9 (childHH thetaBelowCell11113132) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH thetaBelowCell11113132)
    (by
      have h : ((childLL (childHH thetaBelowCell11113132))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH thetaBelowCell11113132)) h)
    (by
      have h : ((childLH (childHH thetaBelowCell11113132))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH thetaBelowCell11113132)) h)
    (by
      have h : ((childHL (childHH thetaBelowCell11113132))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH thetaBelowCell11113132)) h)
    (by
      have h : ((childHH (childHH thetaBelowCell11113132))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH thetaBelowCell11113132)) h)
theorem e24KC2ThetaBelowLeaf111131332 :
    adaptiveCoverCheck 9 (childHL thetaBelowCell11113133) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL thetaBelowCell11113133)
    (by
      have h : ((childLL (childHL thetaBelowCell11113133))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL thetaBelowCell11113133)) h)
    (by
      have h : ((childLH (childHL thetaBelowCell11113133))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL thetaBelowCell11113133)) h)
    (by
      have h : ((childHL (childHL thetaBelowCell11113133))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL thetaBelowCell11113133)) h)
    (by
      have h : ((childHH (childHL thetaBelowCell11113133))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL thetaBelowCell11113133)) h)
theorem e24KC2ThetaBelowLeaf111131333 :
    adaptiveCoverCheck 9 (childHH thetaBelowCell11113133) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH thetaBelowCell11113133)
    (by
      have h : ((childLL (childHH thetaBelowCell11113133))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH thetaBelowCell11113133)) h)
    (by
      have h : ((childLH (childHH thetaBelowCell11113133))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH thetaBelowCell11113133)) h)
    (by
      have h : ((childHL (childHH thetaBelowCell11113133))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH thetaBelowCell11113133)) h)
    (by
      have h : ((childHH (childHH thetaBelowCell11113133))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH thetaBelowCell11113133)) h)
theorem e24KC2ThetaBelowLeaf111132000 :
    adaptiveCoverCheck 9 (childLL thetaBelowCell11113200) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL thetaBelowCell11113200)
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLL thetaBelowCell11113200))
        (by
          have h : ((childLL (childLL (childLL thetaBelowCell11113200)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLL (childLL
            thetaBelowCell11113200))) h)
        (by
          have h : ((childLH (childLL (childLL thetaBelowCell11113200)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLL (childLL
            thetaBelowCell11113200))) h)
        (by
          have h : ((childHL (childLL (childLL thetaBelowCell11113200)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLL (childLL
            thetaBelowCell11113200))) h)
        (by
          have h : ((childHH (childLL (childLL thetaBelowCell11113200)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLL (childLL
            thetaBelowCell11113200))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLL thetaBelowCell11113200))
        (by
          have h : ((childLL (childLH (childLL thetaBelowCell11113200)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLH (childLL
            thetaBelowCell11113200))) h)
        (by
          have h : ((childLH (childLH (childLL thetaBelowCell11113200)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLH (childLL
            thetaBelowCell11113200))) h)
        (by
          have h : ((childHL (childLH (childLL thetaBelowCell11113200)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLH (childLL
            thetaBelowCell11113200))) h)
        (by
          have h : ((childHH (childLH (childLL thetaBelowCell11113200)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLH (childLL
            thetaBelowCell11113200))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLL thetaBelowCell11113200))
        (by
          have h : ((childLL (childHL (childLL thetaBelowCell11113200)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHL (childLL
            thetaBelowCell11113200))) h)
        (by
          have h : ((childLH (childHL (childLL thetaBelowCell11113200)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHL (childLL
            thetaBelowCell11113200))) h)
        (by
          have h : ((childHL (childHL (childLL thetaBelowCell11113200)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHL (childLL
            thetaBelowCell11113200))) h)
        (by
          have h : ((childHH (childHL (childLL thetaBelowCell11113200)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHL (childLL
            thetaBelowCell11113200))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLL thetaBelowCell11113200))
        (by
          have h : ((childLL (childHH (childLL thetaBelowCell11113200)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHH (childLL
            thetaBelowCell11113200))) h)
        (by
          have h : ((childLH (childHH (childLL thetaBelowCell11113200)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHH (childLL
            thetaBelowCell11113200))) h)
        (by
          have h : ((childHL (childHH (childLL thetaBelowCell11113200)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHH (childLL
            thetaBelowCell11113200))) h)
        (by
          have h : ((childHH (childHH (childLL thetaBelowCell11113200)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHH (childLL
            thetaBelowCell11113200))) h))
theorem e24KC2ThetaBelowLeaf111132001 :
    adaptiveCoverCheck 9 (childLH thetaBelowCell11113200) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH thetaBelowCell11113200)
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLH thetaBelowCell11113200))
        (by
          have h : ((childLL (childLL (childLH thetaBelowCell11113200)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLL (childLH
            thetaBelowCell11113200))) h)
        (by
          have h : ((childLH (childLL (childLH thetaBelowCell11113200)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLL (childLH
            thetaBelowCell11113200))) h)
        (by
          have h : ((childHL (childLL (childLH thetaBelowCell11113200)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLL (childLH
            thetaBelowCell11113200))) h)
        (by
          have h : ((childHH (childLL (childLH thetaBelowCell11113200)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLL (childLH
            thetaBelowCell11113200))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLH thetaBelowCell11113200))
        (by
          have h : ((childLL (childLH (childLH thetaBelowCell11113200)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLH (childLH
            thetaBelowCell11113200))) h)
        (by
          have h : ((childLH (childLH (childLH thetaBelowCell11113200)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLH (childLH
            thetaBelowCell11113200))) h)
        (by
          have h : ((childHL (childLH (childLH thetaBelowCell11113200)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLH (childLH
            thetaBelowCell11113200))) h)
        (by
          have h : ((childHH (childLH (childLH thetaBelowCell11113200)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLH (childLH
            thetaBelowCell11113200))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLH thetaBelowCell11113200))
        (by
          have h : ((childLL (childHL (childLH thetaBelowCell11113200)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHL (childLH
            thetaBelowCell11113200))) h)
        (by
          have h : ((childLH (childHL (childLH thetaBelowCell11113200)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHL (childLH
            thetaBelowCell11113200))) h)
        (by
          have h : ((childHL (childHL (childLH thetaBelowCell11113200)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHL (childLH
            thetaBelowCell11113200))) h)
        (by
          have h : ((childHH (childHL (childLH thetaBelowCell11113200)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHL (childLH
            thetaBelowCell11113200))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLH thetaBelowCell11113200))
        (by
          have h : ((childLL (childHH (childLH thetaBelowCell11113200)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHH (childLH
            thetaBelowCell11113200))) h)
        (by
          have h : ((childLH (childHH (childLH thetaBelowCell11113200)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHH (childLH
            thetaBelowCell11113200))) h)
        (by
          have h : ((childHL (childHH (childLH thetaBelowCell11113200)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHH (childLH
            thetaBelowCell11113200))) h)
        (by
          have h : ((childHH (childHH (childLH thetaBelowCell11113200)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHH (childLH
            thetaBelowCell11113200))) h))
theorem e24KC2ThetaBelowLeaf111132002 :
    adaptiveCoverCheck 9 (childHL thetaBelowCell11113200) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL thetaBelowCell11113200)
    (by
      have h : ((childLL (childHL thetaBelowCell11113200))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL thetaBelowCell11113200)) h)
    (by
      have h : ((childLH (childHL thetaBelowCell11113200))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL thetaBelowCell11113200)) h)
    (by
      have h : ((childHL (childHL thetaBelowCell11113200))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL thetaBelowCell11113200)) h)
    (by
      have h : ((childHH (childHL thetaBelowCell11113200))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL thetaBelowCell11113200)) h)
theorem e24KC2ThetaBelowLeaf111132003 :
    adaptiveCoverCheck 9 (childHH thetaBelowCell11113200) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH thetaBelowCell11113200)
    (by
      have h : ((childLL (childHH thetaBelowCell11113200))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH thetaBelowCell11113200)) h)
    (by
      have h : ((childLH (childHH thetaBelowCell11113200))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH thetaBelowCell11113200)) h)
    (by
      have h : ((childHL (childHH thetaBelowCell11113200))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH thetaBelowCell11113200)) h)
    (by
      have h : ((childHH (childHH thetaBelowCell11113200))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH thetaBelowCell11113200)) h)
theorem e24KC2ThetaBelowLeaf111132010 :
    adaptiveCoverCheck 9 (childLL thetaBelowCell11113201) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL thetaBelowCell11113201)
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLL thetaBelowCell11113201))
        (by
          have h : ((childLL (childLL (childLL thetaBelowCell11113201)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLL (childLL
            thetaBelowCell11113201))) h)
        (by
          have h : ((childLH (childLL (childLL thetaBelowCell11113201)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLL (childLL
            thetaBelowCell11113201))) h)
        (by
          have h : ((childHL (childLL (childLL thetaBelowCell11113201)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLL (childLL
            thetaBelowCell11113201))) h)
        (by
          have h : ((childHH (childLL (childLL thetaBelowCell11113201)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLL (childLL
            thetaBelowCell11113201))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLL thetaBelowCell11113201))
        (by
          have h : ((childLL (childLH (childLL thetaBelowCell11113201)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLH (childLL
            thetaBelowCell11113201))) h)
        (by
          have h : ((childLH (childLH (childLL thetaBelowCell11113201)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLH (childLL
            thetaBelowCell11113201))) h)
        (by
          have h : ((childHL (childLH (childLL thetaBelowCell11113201)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLH (childLL
            thetaBelowCell11113201))) h)
        (by
          have h : ((childHH (childLH (childLL thetaBelowCell11113201)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLH (childLL
            thetaBelowCell11113201))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLL thetaBelowCell11113201))
        (by
          have h : ((childLL (childHL (childLL thetaBelowCell11113201)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHL (childLL
            thetaBelowCell11113201))) h)
        (by
          have h : ((childLH (childHL (childLL thetaBelowCell11113201)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHL (childLL
            thetaBelowCell11113201))) h)
        (by
          have h : ((childHL (childHL (childLL thetaBelowCell11113201)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHL (childLL
            thetaBelowCell11113201))) h)
        (by
          have h : ((childHH (childHL (childLL thetaBelowCell11113201)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHL (childLL
            thetaBelowCell11113201))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLL thetaBelowCell11113201))
        (by
          have h : ((childLL (childHH (childLL thetaBelowCell11113201)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHH (childLL
            thetaBelowCell11113201))) h)
        (by
          exact adaptiveCoverCheck_succ_of_children 6 (childLH (childHH (childLL
            thetaBelowCell11113201)))
            (by
              have h : (thetaBelowCell111132010310).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132010310 h)
            (by
              have h : (thetaBelowCell111132010311).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132010311 h)
            (by
              have h : (thetaBelowCell111132010312).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132010312 h)
            (by
              have h : (thetaBelowCell111132010313).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132010313 h))
        (by
          have h : ((childHL (childHH (childLL thetaBelowCell11113201)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHH (childLL
            thetaBelowCell11113201))) h)
        (by
          have h : ((childHH (childHH (childLL thetaBelowCell11113201)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHH (childLL
            thetaBelowCell11113201))) h))
theorem cover_subtree_b3391292f833 :
    adaptiveCoverCheck 8 (childLH (childLH thetaBelowCell11113201)) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLH thetaBelowCell11113201))
    (by
      have h : ((childLL (childLH (childLH thetaBelowCell11113201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLH (childLH
        thetaBelowCell11113201))) h)
    (by
      have h : ((childLH (childLH (childLH thetaBelowCell11113201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLH (childLH
        thetaBelowCell11113201))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 6 (childHL (childLH (childLH
        thetaBelowCell11113201)))
        (by
          have h : (thetaBelowCell111132011120).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132011120 h)
        (by
          have h : (thetaBelowCell111132011121).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132011121 h)
        (by
          have h : (thetaBelowCell111132011122).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132011122 h)
        (by
          have h : (thetaBelowCell111132011123).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132011123 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 (childHH (childLH (childLH
        thetaBelowCell11113201)))
        (by
          have h : (thetaBelowCell111132011130).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132011130 h)
        (by
          have h : (thetaBelowCell111132011131).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132011131 h)
        (by
          have h : (thetaBelowCell111132011132).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132011132 h)
        (by
          have h : (thetaBelowCell111132011133).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132011133 h))

theorem cover_subtree_3e9c61b8ab9c :
    adaptiveCoverCheck 8 (childHL (childLH thetaBelowCell11113201)) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLH thetaBelowCell11113201))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 (childLL (childHL (childLH
        thetaBelowCell11113201)))
        (by
          have h : (thetaBelowCell111132011200).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132011200 h)
        (by
          have h : (thetaBelowCell111132011201).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132011201 h)
        (by
          have h : (thetaBelowCell111132011202).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132011202 h)
        (by
          have h : (thetaBelowCell111132011203).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132011203 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 (childLH (childHL (childLH
        thetaBelowCell11113201)))
        (by
          have h : (thetaBelowCell111132011210).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132011210 h)
        (by
          have h : (thetaBelowCell111132011211).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132011211 h)
        (by
          have h : (thetaBelowCell111132011212).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132011212 h)
        (by
          have h : (thetaBelowCell111132011213).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132011213 h))
    (by
      have h : ((childHL (childHL (childLH thetaBelowCell11113201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHL (childLH
        thetaBelowCell11113201))) h)
    (by
      have h : ((childHH (childHL (childLH thetaBelowCell11113201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHL (childLH
        thetaBelowCell11113201))) h)

theorem cover_subtree_466ff371217d :
    adaptiveCoverCheck 8 (childHH (childLH thetaBelowCell11113201)) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLH thetaBelowCell11113201))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 (childLL (childHH (childLH
        thetaBelowCell11113201)))
        (by
          have h : (thetaBelowCell111132011300).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132011300 h)
        (by
          have h : (thetaBelowCell111132011301).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132011301 h)
        (by
          have h : (thetaBelowCell111132011302).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132011302 h)
        (by
          have h : (thetaBelowCell111132011303).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132011303 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 (childLH (childHH (childLH
        thetaBelowCell11113201)))
        (by
          have h : (thetaBelowCell111132011310).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132011310 h)
        (by
          have h : (thetaBelowCell111132011311).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132011311 h)
        (by
          have h : (thetaBelowCell111132011312).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132011312 h)
        (by
          have h : (thetaBelowCell111132011313).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132011313 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 (childHL (childHH (childLH
        thetaBelowCell11113201)))
        (by
          have h : (thetaBelowCell111132011320).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132011320 h)
        (by
          have h : (thetaBelowCell111132011321).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132011321 h)
        (by
          have h : (thetaBelowCell111132011322).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132011322 h)
        (by
          have h : (thetaBelowCell111132011323).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132011323 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 (childHH (childHH (childLH
        thetaBelowCell11113201)))
        (by
          have h : (thetaBelowCell111132011330).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132011330 h)
        (by
          have h : (thetaBelowCell111132011331).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132011331 h)
        (by
          have h : (thetaBelowCell111132011332).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132011332 h)
        (by
          have h : (thetaBelowCell111132011333).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132011333 h))

theorem e24KC2ThetaBelowLeaf111132011 :
    adaptiveCoverCheck 9 (childLH thetaBelowCell11113201) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH thetaBelowCell11113201)
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLH thetaBelowCell11113201))
        (by
          have h : ((childLL (childLL (childLH thetaBelowCell11113201)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLL (childLH
            thetaBelowCell11113201))) h)
        (by
          have h : ((childLH (childLL (childLH thetaBelowCell11113201)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLL (childLH
            thetaBelowCell11113201))) h)
        (by
          have h : ((childHL (childLL (childLH thetaBelowCell11113201)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLL (childLH
            thetaBelowCell11113201))) h)
        (by
          have h : ((childHH (childLL (childLH thetaBelowCell11113201)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLL (childLH
            thetaBelowCell11113201))) h))
    cover_subtree_b3391292f833
    cover_subtree_3e9c61b8ab9c
    cover_subtree_466ff371217d
theorem e24KC2ThetaBelowLeaf111132012 :
    adaptiveCoverCheck 9 (childHL thetaBelowCell11113201) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL thetaBelowCell11113201)
    (by
      have h : ((childLL (childHL thetaBelowCell11113201))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL thetaBelowCell11113201)) h)
    (by
      have h : ((childLH (childHL thetaBelowCell11113201))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL thetaBelowCell11113201)) h)
    (by
      have h : ((childHL (childHL thetaBelowCell11113201))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL thetaBelowCell11113201)) h)
    (by
      have h : ((childHH (childHL thetaBelowCell11113201))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL thetaBelowCell11113201)) h)
theorem e24KC2ThetaBelowLeaf111132013 :
    adaptiveCoverCheck 9 (childHH thetaBelowCell11113201) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH thetaBelowCell11113201)
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childHH thetaBelowCell11113201))
        (by
          have h : ((childLL (childLL (childHH thetaBelowCell11113201)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLL (childHH
            thetaBelowCell11113201))) h)
        (by
          have h : ((childLH (childLL (childHH thetaBelowCell11113201)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLL (childHH
            thetaBelowCell11113201))) h)
        (by
          have h : ((childHL (childLL (childHH thetaBelowCell11113201)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLL (childHH
            thetaBelowCell11113201))) h)
        (by
          have h : ((childHH (childLL (childHH thetaBelowCell11113201)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLL (childHH
            thetaBelowCell11113201))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childHH thetaBelowCell11113201))
        (by
          have h : ((childLL (childLH (childHH thetaBelowCell11113201)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childLH (childHH
            thetaBelowCell11113201))) h)
        (by
          have h : ((childLH (childLH (childHH thetaBelowCell11113201)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLH (childHH
            thetaBelowCell11113201))) h)
        (by
          have h : ((childHL (childLH (childHH thetaBelowCell11113201)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childLH (childHH
            thetaBelowCell11113201))) h)
        (by
          have h : ((childHH (childLH (childHH thetaBelowCell11113201)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childLH (childHH
            thetaBelowCell11113201))) h))
    (by
      have h : ((childHL (childHH thetaBelowCell11113201))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH thetaBelowCell11113201)) h)
    (by
      have h : ((childHH (childHH thetaBelowCell11113201))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH thetaBelowCell11113201)) h)
theorem cover_subtree_7f4f4b92c5ab :
    adaptiveCoverCheck 8 (childLL (childLL thetaBelowCell11113210)) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLL thetaBelowCell11113210))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 (childLL (childLL (childLL
        thetaBelowCell11113210)))
        (by
          have h : (thetaBelowCell111132100000).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132100000 h)
        (by
          have h : (thetaBelowCell111132100001).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132100001 h)
        (by
          have h : (thetaBelowCell111132100002).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132100002 h)
        (by
          have h : (thetaBelowCell111132100003).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132100003 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 (childLH (childLL (childLL
        thetaBelowCell11113210)))
        (by
          have h : (thetaBelowCell111132100010).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132100010 h)
        (by
          have h : (thetaBelowCell111132100011).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132100011 h)
        (by
          have h : (thetaBelowCell111132100012).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132100012 h)
        (by
          have h : (thetaBelowCell111132100013).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132100013 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 (childHL (childLL (childLL
        thetaBelowCell11113210)))
        (by
          have h : (thetaBelowCell111132100020).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132100020 h)
        (by
          have h : (thetaBelowCell111132100021).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132100021 h)
        (by
          have h : (thetaBelowCell111132100022).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132100022 h)
        (by
          have h : (thetaBelowCell111132100023).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132100023 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 (childHH (childLL (childLL
        thetaBelowCell11113210)))
        (by
          have h : (thetaBelowCell111132100030).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132100030 h)
        (by
          have h : (thetaBelowCell111132100031).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132100031 h)
        (by
          have h : (thetaBelowCell111132100032).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132100032 h)
        (by
          have h : (thetaBelowCell111132100033).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132100033 h))

theorem cover_subtree_c689c5c4108b :
    adaptiveCoverCheck 8 (childLH (childLL thetaBelowCell11113210)) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLL thetaBelowCell11113210))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 (childLL (childLH (childLL
        thetaBelowCell11113210)))
        (by
          have h : (thetaBelowCell111132100100).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132100100 h)
        (by
          have h : (thetaBelowCell111132100101).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132100101 h)
        (by
          have h : (thetaBelowCell111132100102).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132100102 h)
        (by
          have h : (thetaBelowCell111132100103).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132100103 h))
    (by
      have h : ((childLH (childLH (childLL thetaBelowCell11113210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childLH (childLL
        thetaBelowCell11113210))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 6 (childHL (childLH (childLL
        thetaBelowCell11113210)))
        (by
          have h : (thetaBelowCell111132100120).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132100120 h)
        (by
          have h : (thetaBelowCell111132100121).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132100121 h)
        (by
          have h : (thetaBelowCell111132100122).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132100122 h)
        (by
          have h : (thetaBelowCell111132100123).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132100123 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 (childHH (childLH (childLL
        thetaBelowCell11113210)))
        (by
          have h : (thetaBelowCell111132100130).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132100130 h)
        (by
          have h : (thetaBelowCell111132100131).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132100131 h)
        (by
          have h : (thetaBelowCell111132100132).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132100132 h)
        (by
          have h : (thetaBelowCell111132100133).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132100133 h))

theorem cover_subtree_9df392f82d53 :
    adaptiveCoverCheck 8 (childHL (childLL thetaBelowCell11113210)) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLL thetaBelowCell11113210))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 (childLL (childHL (childLL
        thetaBelowCell11113210)))
        (by
          have h : (thetaBelowCell111132100200).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132100200 h)
        (by
          have h : (thetaBelowCell111132100201).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132100201 h)
        (by
          have h : (thetaBelowCell111132100202).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132100202 h)
        (by
          have h : (thetaBelowCell111132100203).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132100203 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 (childLH (childHL (childLL
        thetaBelowCell11113210)))
        (by
          have h : (thetaBelowCell111132100210).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132100210 h)
        (by
          have h : (thetaBelowCell111132100211).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132100211 h)
        (by
          have h : (thetaBelowCell111132100212).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132100212 h)
        (by
          have h : (thetaBelowCell111132100213).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132100213 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 (childHL (childHL (childLL
        thetaBelowCell11113210)))
        (by
          have h : (thetaBelowCell111132100220).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132100220 h)
        (by
          have h : (thetaBelowCell111132100221).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132100221 h)
        (by
          have h : (thetaBelowCell111132100222).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132100222 h)
        (by
          have h : (thetaBelowCell111132100223).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132100223 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 (childHH (childHL (childLL
        thetaBelowCell11113210)))
        (by
          have h : (thetaBelowCell111132100230).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132100230 h)
        (by
          have h : (thetaBelowCell111132100231).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132100231 h)
        (by
          have h : (thetaBelowCell111132100232).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132100232 h)
        (by
          have h : (thetaBelowCell111132100233).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132100233 h))

theorem cover_subtree_f50cdc547dbb :
    adaptiveCoverCheck 8 (childHH (childLL thetaBelowCell11113210)) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLL thetaBelowCell11113210))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 (childLL (childHH (childLL
        thetaBelowCell11113210)))
        (by
          have h : (thetaBelowCell111132100300).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132100300 h)
        (by
          have h : (thetaBelowCell111132100301).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132100301 h)
        (by
          have h : (thetaBelowCell111132100302).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132100302 h)
        (by
          have h : (thetaBelowCell111132100303).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132100303 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 (childLH (childHH (childLL
        thetaBelowCell11113210)))
        (by
          have h : (thetaBelowCell111132100310).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132100310 h)
        (by
          have h : (thetaBelowCell111132100311).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132100311 h)
        (by
          have h : (thetaBelowCell111132100312).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132100312 h)
        (by
          have h : (thetaBelowCell111132100313).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132100313 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 (childHL (childHH (childLL
        thetaBelowCell11113210)))
        (by
          have h : (thetaBelowCell111132100320).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132100320 h)
        (by
          have h : (thetaBelowCell111132100321).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132100321 h)
        (by
          have h : (thetaBelowCell111132100322).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132100322 h)
        (by
          have h : (thetaBelowCell111132100323).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132100323 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 (childHH (childHH (childLL
        thetaBelowCell11113210)))
        (by
          have h : (thetaBelowCell111132100330).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132100330 h)
        (by
          have h : (thetaBelowCell111132100331).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132100331 h)
        (by
          have h : (thetaBelowCell111132100332).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132100332 h)
        (by
          have h : (thetaBelowCell111132100333).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111132100333 h))

theorem e24KC2ThetaBelowLeaf111132100 :
    adaptiveCoverCheck 9 (childLL thetaBelowCell11113210) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL thetaBelowCell11113210)
    cover_subtree_7f4f4b92c5ab
    cover_subtree_c689c5c4108b
    cover_subtree_9df392f82d53
    cover_subtree_f50cdc547dbb

end PartE
end GerverSofa

end

end

end

section

/-! E24KC6 explicit proof-producing certificate batch. -/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells00c658e5bf

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells00c658e5bf

open CertificateCells00c658e5bf
theorem e24KC2ThetaBelowLeaf111133120 :
    adaptiveCoverCheck 9 (childLL thetaBelowCell11113312) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL thetaBelowCell11113312)
    (by
      have h : ((childLL (childLL thetaBelowCell11113312))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL thetaBelowCell11113312)) h)
    (by
      have h : ((childLH (childLL thetaBelowCell11113312))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL thetaBelowCell11113312)) h)
    (by
      have h : ((childHL (childLL thetaBelowCell11113312))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL thetaBelowCell11113312)) h)
    (by
      have h : ((childHH (childLL thetaBelowCell11113312))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL thetaBelowCell11113312)) h)
theorem e24KC2ThetaBelowLeaf111133121 :
    adaptiveCoverCheck 9 (childLH thetaBelowCell11113312) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH thetaBelowCell11113312)
    (by
      have h : ((childLL (childLH thetaBelowCell11113312))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH thetaBelowCell11113312)) h)
    (by
      have h : ((childLH (childLH thetaBelowCell11113312))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH thetaBelowCell11113312)) h)
    (by
      have h : ((childHL (childLH thetaBelowCell11113312))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH thetaBelowCell11113312)) h)
    (by
      have h : ((childHH (childLH thetaBelowCell11113312))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH thetaBelowCell11113312)) h)
theorem e24KC2ThetaBelowLeaf111133130 :
    adaptiveCoverCheck 9 (childLL thetaBelowCell11113313) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL thetaBelowCell11113313)
    (by
      have h : ((childLL (childLL thetaBelowCell11113313))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL thetaBelowCell11113313)) h)
    (by
      have h : ((childLH (childLL thetaBelowCell11113313))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL thetaBelowCell11113313)) h)
    (by
      have h : ((childHL (childLL thetaBelowCell11113313))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL thetaBelowCell11113313)) h)
    (by
      have h : ((childHH (childLL thetaBelowCell11113313))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL thetaBelowCell11113313)) h)
theorem e24KC2ThetaBelowLeaf111133131 :
    adaptiveCoverCheck 9 (childLH thetaBelowCell11113313) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH thetaBelowCell11113313)
    (by
      have h : ((childLL (childLH thetaBelowCell11113313))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH thetaBelowCell11113313)) h)
    (by
      have h : ((childLH (childLH thetaBelowCell11113313))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH thetaBelowCell11113313)) h)
    (by
      have h : ((childHL (childLH thetaBelowCell11113313))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH thetaBelowCell11113313)) h)
    (by
      have h : ((childHH (childLH thetaBelowCell11113313))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH thetaBelowCell11113313)) h)

end PartE
end GerverSofa

end

end

end

end

end

end
