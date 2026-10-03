/-
Copyright (c) 2026 Dawid Trela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dawid Trela
-/
module

public import LeanPool.MovingSofa.GerverSofa.KernelOnly.Core.Bundle005
/-!
# Gerver sofa: related certificate and semantic modules

* `GerverSofa.KernelOnly.PartE.Certificates.Batch011`.
* `GerverSofa.KernelOnly.PartE.Certificates.Batch013`.
-/

public section

noncomputable section

namespace GerverSofa.PartE.CertificateCells0c0d0adfef

/-- Subcell `1000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell1000 : AngleCell :=
  childLL (childLL (childLL (childLH e24ThetaAboveRoot)))

/-- Subcell `1001` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell1001 : AngleCell :=
  childLH (childLL (childLL (childLH e24ThetaAboveRoot)))

/-- Subcell `10003202` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10003202 : AngleCell :=
  childHL (childLL (childHL (childHH thetaAboveCell1000)))

/-- Subcell `10003203` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10003203 : AngleCell :=
  childHH (childLL (childHL (childHH thetaAboveCell1000)))

/-- Subcell `10003210` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10003210 : AngleCell :=
  childLL (childLH (childHL (childHH thetaAboveCell1000)))

/-- Subcell `10003211` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10003211 : AngleCell :=
  childLH (childLH (childHL (childHH thetaAboveCell1000)))

/-- Subcell `10003212` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10003212 : AngleCell :=
  childHL (childLH (childHL (childHH thetaAboveCell1000)))

/-- Subcell `10003213` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10003213 : AngleCell :=
  childHH (childLH (childHL (childHH thetaAboveCell1000)))

/-- Subcell `10003220` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10003220 : AngleCell :=
  childLL (childHL (childHL (childHH thetaAboveCell1000)))

/-- Subcell `10003221` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10003221 : AngleCell :=
  childLH (childHL (childHL (childHH thetaAboveCell1000)))

/-- Subcell `10003222` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10003222 : AngleCell :=
  childHL (childHL (childHL (childHH thetaAboveCell1000)))

/-- Subcell `10003223` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10003223 : AngleCell :=
  childHH (childHL (childHL (childHH thetaAboveCell1000)))

/-- Subcell `10003230` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10003230 : AngleCell :=
  childLL (childHH (childHL (childHH thetaAboveCell1000)))

/-- Subcell `10003231` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10003231 : AngleCell :=
  childLH (childHH (childHL (childHH thetaAboveCell1000)))

/-- Subcell `10003232` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10003232 : AngleCell :=
  childHL (childHH (childHL (childHH thetaAboveCell1000)))

/-- Subcell `10003233` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10003233 : AngleCell :=
  childHH (childHH (childHL (childHH thetaAboveCell1000)))

/-- Subcell `10003300` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10003300 : AngleCell :=
  childLL (childLL (childHH (childHH thetaAboveCell1000)))

/-- Subcell `10003301` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10003301 : AngleCell :=
  childLH (childLL (childHH (childHH thetaAboveCell1000)))

/-- Subcell `10003302` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10003302 : AngleCell :=
  childHL (childLL (childHH (childHH thetaAboveCell1000)))

/-- Subcell `10003303` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10003303 : AngleCell :=
  childHH (childLL (childHH (childHH thetaAboveCell1000)))

/-- Subcell `10003310` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10003310 : AngleCell :=
  childLL (childLH (childHH (childHH thetaAboveCell1000)))

/-- Subcell `10003311` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10003311 : AngleCell :=
  childLH (childLH (childHH (childHH thetaAboveCell1000)))

/-- Subcell `10003312` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10003312 : AngleCell :=
  childHL (childLH (childHH (childHH thetaAboveCell1000)))

/-- Subcell `10003313` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10003313 : AngleCell :=
  childHH (childLH (childHH (childHH thetaAboveCell1000)))

/-- Subcell `10003320` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10003320 : AngleCell :=
  childLL (childHL (childHH (childHH thetaAboveCell1000)))

/-- Subcell `10003321` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10003321 : AngleCell :=
  childLH (childHL (childHH (childHH thetaAboveCell1000)))

/-- Subcell `10003322` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10003322 : AngleCell :=
  childHL (childHL (childHH (childHH thetaAboveCell1000)))

/-- Subcell `10003323` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10003323 : AngleCell :=
  childHH (childHL (childHH (childHH thetaAboveCell1000)))

/-- Subcell `10003330` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10003330 : AngleCell :=
  childLL (childHH (childHH (childHH thetaAboveCell1000)))

/-- Subcell `10003331` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10003331 : AngleCell :=
  childLH (childHH (childHH (childHH thetaAboveCell1000)))

/-- Subcell `10003332` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10003332 : AngleCell :=
  childHL (childHH (childHH (childHH thetaAboveCell1000)))

/-- Subcell `10003333` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10003333 : AngleCell :=
  childHH (childHH (childHH (childHH thetaAboveCell1000)))

/-- Subcell `10012020` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10012020 : AngleCell :=
  childLL (childHL (childLL (childHL thetaAboveCell1001)))

/-- Subcell `10012021` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10012021 : AngleCell :=
  childLH (childHL (childLL (childHL thetaAboveCell1001)))

/-- Subcell `10012022` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10012022 : AngleCell :=
  childHL (childHL (childLL (childHL thetaAboveCell1001)))

/-- Subcell `10012023` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10012023 : AngleCell :=
  childHH (childHL (childLL (childHL thetaAboveCell1001)))

/-- Subcell `10012030` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10012030 : AngleCell :=
  childLL (childHH (childLL (childHL thetaAboveCell1001)))

/-- Subcell `10012031` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10012031 : AngleCell :=
  childLH (childHH (childLL (childHL thetaAboveCell1001)))

/-- Subcell `10012032` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10012032 : AngleCell :=
  childHL (childHH (childLL (childHL thetaAboveCell1001)))

/-- Subcell `10012033` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10012033 : AngleCell :=
  childHH (childHH (childLL (childHL thetaAboveCell1001)))

/-- Subcell `10012120` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10012120 : AngleCell :=
  childLL (childHL (childLH (childHL thetaAboveCell1001)))

/-- Subcell `10012121` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10012121 : AngleCell :=
  childLH (childHL (childLH (childHL thetaAboveCell1001)))

/-- Subcell `10012122` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10012122 : AngleCell :=
  childHL (childHL (childLH (childHL thetaAboveCell1001)))

/-- Subcell `10012123` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10012123 : AngleCell :=
  childHH (childHL (childLH (childHL thetaAboveCell1001)))

/-- Subcell `10012130` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10012130 : AngleCell :=
  childLL (childHH (childLH (childHL thetaAboveCell1001)))

/-- Subcell `10012131` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10012131 : AngleCell :=
  childLH (childHH (childLH (childHL thetaAboveCell1001)))

/-- Subcell `10012132` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10012132 : AngleCell :=
  childHL (childHH (childLH (childHL thetaAboveCell1001)))

/-- Subcell `10012133` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10012133 : AngleCell :=
  childHH (childHH (childLH (childHL thetaAboveCell1001)))

/-- Subcell `10012200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10012200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell1001)))

/-- Subcell `10012201` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10012201 : AngleCell :=
  childLH (childLL (childHL (childHL thetaAboveCell1001)))

/-- Subcell `10012202` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10012202 : AngleCell :=
  childHL (childLL (childHL (childHL thetaAboveCell1001)))

/-- Subcell `10012203` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10012203 : AngleCell :=
  childHH (childLL (childHL (childHL thetaAboveCell1001)))

/-- Subcell `10012210` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10012210 : AngleCell :=
  childLL (childLH (childHL (childHL thetaAboveCell1001)))

/-- Subcell `10012211` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10012211 : AngleCell :=
  childLH (childLH (childHL (childHL thetaAboveCell1001)))

/-- Subcell `10012212` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10012212 : AngleCell :=
  childHL (childLH (childHL (childHL thetaAboveCell1001)))

/-- Subcell `10012213` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10012213 : AngleCell :=
  childHH (childLH (childHL (childHL thetaAboveCell1001)))

/-- Subcell `10012220` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10012220 : AngleCell :=
  childLL (childHL (childHL (childHL thetaAboveCell1001)))

/-- Subcell `10012221` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10012221 : AngleCell :=
  childLH (childHL (childHL (childHL thetaAboveCell1001)))

/-- Subcell `10012222` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10012222 : AngleCell :=
  childHL (childHL (childHL (childHL thetaAboveCell1001)))

/-- Subcell `10012223` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10012223 : AngleCell :=
  childHH (childHL (childHL (childHL thetaAboveCell1001)))

/-- Subcell `10012230` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10012230 : AngleCell :=
  childLL (childHH (childHL (childHL thetaAboveCell1001)))

/-- Subcell `10012231` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10012231 : AngleCell :=
  childLH (childHH (childHL (childHL thetaAboveCell1001)))

/-- Subcell `10012232` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10012232 : AngleCell :=
  childHL (childHH (childHL (childHL thetaAboveCell1001)))

/-- Subcell `10012233` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10012233 : AngleCell :=
  childHH (childHH (childHL (childHL thetaAboveCell1001)))

/-- Subcell `10012300` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10012300 : AngleCell :=
  childLL (childLL (childHH (childHL thetaAboveCell1001)))

/-- Subcell `10012301` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10012301 : AngleCell :=
  childLH (childLL (childHH (childHL thetaAboveCell1001)))

/-- Subcell `10012302` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10012302 : AngleCell :=
  childHL (childLL (childHH (childHL thetaAboveCell1001)))

/-- Subcell `10012303` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10012303 : AngleCell :=
  childHH (childLL (childHH (childHL thetaAboveCell1001)))

/-- Subcell `10012310` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10012310 : AngleCell :=
  childLL (childLH (childHH (childHL thetaAboveCell1001)))

/-- Subcell `10012311` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10012311 : AngleCell :=
  childLH (childLH (childHH (childHL thetaAboveCell1001)))

/-- Subcell `10012312` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10012312 : AngleCell :=
  childHL (childLH (childHH (childHL thetaAboveCell1001)))

/-- Subcell `10012313` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10012313 : AngleCell :=
  childHH (childLH (childHH (childHL thetaAboveCell1001)))

/-- Subcell `10012320` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10012320 : AngleCell :=
  childLL (childHL (childHH (childHL thetaAboveCell1001)))

/-- Subcell `10012321` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10012321 : AngleCell :=
  childLH (childHL (childHH (childHL thetaAboveCell1001)))

/-- Subcell `10012322` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10012322 : AngleCell :=
  childHL (childHL (childHH (childHL thetaAboveCell1001)))

/-- Subcell `10012323` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10012323 : AngleCell :=
  childHH (childHL (childHH (childHL thetaAboveCell1001)))

/-- Subcell `10012330` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10012330 : AngleCell :=
  childLL (childHH (childHH (childHL thetaAboveCell1001)))

/-- Subcell `10012331` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10012331 : AngleCell :=
  childLH (childHH (childHH (childHL thetaAboveCell1001)))

/-- Subcell `10012332` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10012332 : AngleCell :=
  childHL (childHH (childHH (childHL thetaAboveCell1001)))

/-- Subcell `10012333` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10012333 : AngleCell :=
  childHH (childHH (childHH (childHL thetaAboveCell1001)))

/-- Subcell `10013020` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10013020 : AngleCell :=
  childLL (childHL (childLL (childHH thetaAboveCell1001)))

/-- Subcell `10013021` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10013021 : AngleCell :=
  childLH (childHL (childLL (childHH thetaAboveCell1001)))

/-- Subcell `10013022` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10013022 : AngleCell :=
  childHL (childHL (childLL (childHH thetaAboveCell1001)))

/-- Subcell `10013023` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10013023 : AngleCell :=
  childHH (childHL (childLL (childHH thetaAboveCell1001)))

/-- Subcell `10013030` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10013030 : AngleCell :=
  childLL (childHH (childLL (childHH thetaAboveCell1001)))

/-- Subcell `10013031` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10013031 : AngleCell :=
  childLH (childHH (childLL (childHH thetaAboveCell1001)))

/-- Subcell `10013032` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10013032 : AngleCell :=
  childHL (childHH (childLL (childHH thetaAboveCell1001)))

/-- Subcell `10013033` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10013033 : AngleCell :=
  childHH (childHH (childLL (childHH thetaAboveCell1001)))

/-- Subcell `10013120` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10013120 : AngleCell :=
  childLL (childHL (childLH (childHH thetaAboveCell1001)))

/-- Subcell `10013121` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10013121 : AngleCell :=
  childLH (childHL (childLH (childHH thetaAboveCell1001)))

/-- Subcell `10013122` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10013122 : AngleCell :=
  childHL (childHL (childLH (childHH thetaAboveCell1001)))

/-- Subcell `10013123` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10013123 : AngleCell :=
  childHH (childHL (childLH (childHH thetaAboveCell1001)))

/-- Subcell `10013130` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10013130 : AngleCell :=
  childLL (childHH (childLH (childHH thetaAboveCell1001)))

/-- Subcell `10013131` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10013131 : AngleCell :=
  childLH (childHH (childLH (childHH thetaAboveCell1001)))

/-- Subcell `10013132` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10013132 : AngleCell :=
  childHL (childHH (childLH (childHH thetaAboveCell1001)))

/-- Subcell `10013133` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10013133 : AngleCell :=
  childHH (childHH (childLH (childHH thetaAboveCell1001)))

/-- Subcell `10013200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10013200 : AngleCell :=
  childLL (childLL (childHL (childHH thetaAboveCell1001)))

/-- Subcell `10013201` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10013201 : AngleCell :=
  childLH (childLL (childHL (childHH thetaAboveCell1001)))

/-- Subcell `10013202` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10013202 : AngleCell :=
  childHL (childLL (childHL (childHH thetaAboveCell1001)))

/-- Subcell `10013203` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10013203 : AngleCell :=
  childHH (childLL (childHL (childHH thetaAboveCell1001)))

end GerverSofa.PartE.CertificateCells0c0d0adfef

namespace GerverSofa.PartE.CertificateCells660a83a47d

/-- Subcell `1001` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell1001 : AngleCell :=
  childLH (childLL (childLL (childLH e24ThetaAboveRoot)))

/-- Subcell `1002` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell1002 : AngleCell :=
  childHL (childLL (childLL (childLH e24ThetaAboveRoot)))

/-- Subcell `1003` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell1003 : AngleCell :=
  childHH (childLL (childLL (childLH e24ThetaAboveRoot)))

/-- Subcell `1010` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell1010 : AngleCell :=
  childLL (childLH (childLL (childLH e24ThetaAboveRoot)))

/-- Subcell `10013203` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10013203 : AngleCell :=
  childHH (childLL (childHL (childHH thetaAboveCell1001)))

/-- Subcell `10013210` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10013210 : AngleCell :=
  childLL (childLH (childHL (childHH thetaAboveCell1001)))

/-- Subcell `10013211` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10013211 : AngleCell :=
  childLH (childLH (childHL (childHH thetaAboveCell1001)))

/-- Subcell `10013212` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10013212 : AngleCell :=
  childHL (childLH (childHL (childHH thetaAboveCell1001)))

/-- Subcell `10013213` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10013213 : AngleCell :=
  childHH (childLH (childHL (childHH thetaAboveCell1001)))

/-- Subcell `10013220` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10013220 : AngleCell :=
  childLL (childHL (childHL (childHH thetaAboveCell1001)))

/-- Subcell `10013221` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10013221 : AngleCell :=
  childLH (childHL (childHL (childHH thetaAboveCell1001)))

/-- Subcell `10013222` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10013222 : AngleCell :=
  childHL (childHL (childHL (childHH thetaAboveCell1001)))

/-- Subcell `10013223` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10013223 : AngleCell :=
  childHH (childHL (childHL (childHH thetaAboveCell1001)))

/-- Subcell `10013230` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10013230 : AngleCell :=
  childLL (childHH (childHL (childHH thetaAboveCell1001)))

/-- Subcell `10013231` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10013231 : AngleCell :=
  childLH (childHH (childHL (childHH thetaAboveCell1001)))

/-- Subcell `10013232` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10013232 : AngleCell :=
  childHL (childHH (childHL (childHH thetaAboveCell1001)))

/-- Subcell `10013233` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10013233 : AngleCell :=
  childHH (childHH (childHL (childHH thetaAboveCell1001)))

/-- Subcell `10013300` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10013300 : AngleCell :=
  childLL (childLL (childHH (childHH thetaAboveCell1001)))

/-- Subcell `10013301` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10013301 : AngleCell :=
  childLH (childLL (childHH (childHH thetaAboveCell1001)))

/-- Subcell `10013302` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10013302 : AngleCell :=
  childHL (childLL (childHH (childHH thetaAboveCell1001)))

/-- Subcell `10013303` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10013303 : AngleCell :=
  childHH (childLL (childHH (childHH thetaAboveCell1001)))

/-- Subcell `10013310` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10013310 : AngleCell :=
  childLL (childLH (childHH (childHH thetaAboveCell1001)))

/-- Subcell `10013311` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10013311 : AngleCell :=
  childLH (childLH (childHH (childHH thetaAboveCell1001)))

/-- Subcell `10013312` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10013312 : AngleCell :=
  childHL (childLH (childHH (childHH thetaAboveCell1001)))

/-- Subcell `10013313` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10013313 : AngleCell :=
  childHH (childLH (childHH (childHH thetaAboveCell1001)))

/-- Subcell `10013320` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10013320 : AngleCell :=
  childLL (childHL (childHH (childHH thetaAboveCell1001)))

/-- Subcell `10013321` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10013321 : AngleCell :=
  childLH (childHL (childHH (childHH thetaAboveCell1001)))

/-- Subcell `10013322` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10013322 : AngleCell :=
  childHL (childHL (childHH (childHH thetaAboveCell1001)))

/-- Subcell `10013323` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10013323 : AngleCell :=
  childHH (childHL (childHH (childHH thetaAboveCell1001)))

/-- Subcell `10013330` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10013330 : AngleCell :=
  childLL (childHH (childHH (childHH thetaAboveCell1001)))

/-- Subcell `10013331` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10013331 : AngleCell :=
  childLH (childHH (childHH (childHH thetaAboveCell1001)))

/-- Subcell `10013332` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10013332 : AngleCell :=
  childHL (childHH (childHH (childHH thetaAboveCell1001)))

/-- Subcell `10013333` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10013333 : AngleCell :=
  childHH (childHH (childHH (childHH thetaAboveCell1001)))

/-- Subcell `10102020` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10102020 : AngleCell :=
  childLL (childHL (childLL (childHL thetaAboveCell1010)))

/-- Subcell `10102021` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10102021 : AngleCell :=
  childLH (childHL (childLL (childHL thetaAboveCell1010)))

/-- Subcell `10102022` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10102022 : AngleCell :=
  childHL (childHL (childLL (childHL thetaAboveCell1010)))

/-- Subcell `10102023` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10102023 : AngleCell :=
  childHH (childHL (childLL (childHL thetaAboveCell1010)))

/-- Subcell `10102030` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10102030 : AngleCell :=
  childLL (childHH (childLL (childHL thetaAboveCell1010)))

/-- Subcell `10102031` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10102031 : AngleCell :=
  childLH (childHH (childLL (childHL thetaAboveCell1010)))

/-- Subcell `10102032` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10102032 : AngleCell :=
  childHL (childHH (childLL (childHL thetaAboveCell1010)))

/-- Subcell `10102033` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10102033 : AngleCell :=
  childHH (childHH (childLL (childHL thetaAboveCell1010)))

/-- Subcell `10102200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10102200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell1010)))

/-- Subcell `10102201` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10102201 : AngleCell :=
  childLH (childLL (childHL (childHL thetaAboveCell1010)))

/-- Subcell `10102202` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10102202 : AngleCell :=
  childHL (childLL (childHL (childHL thetaAboveCell1010)))

/-- Subcell `10102203` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10102203 : AngleCell :=
  childHH (childLL (childHL (childHL thetaAboveCell1010)))

/-- Subcell `10102210` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10102210 : AngleCell :=
  childLL (childLH (childHL (childHL thetaAboveCell1010)))

/-- Subcell `10102211` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10102211 : AngleCell :=
  childLH (childLH (childHL (childHL thetaAboveCell1010)))

/-- Subcell `10102212` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10102212 : AngleCell :=
  childHL (childLH (childHL (childHL thetaAboveCell1010)))

/-- Subcell `10102213` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10102213 : AngleCell :=
  childHH (childLH (childHL (childHL thetaAboveCell1010)))

/-- Subcell `10102220` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10102220 : AngleCell :=
  childLL (childHL (childHL (childHL thetaAboveCell1010)))

/-- Subcell `10102221` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10102221 : AngleCell :=
  childLH (childHL (childHL (childHL thetaAboveCell1010)))

/-- Subcell `10102222` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10102222 : AngleCell :=
  childHL (childHL (childHL (childHL thetaAboveCell1010)))

/-- Subcell `10102223` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10102223 : AngleCell :=
  childHH (childHL (childHL (childHL thetaAboveCell1010)))

/-- Subcell `10102230` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10102230 : AngleCell :=
  childLL (childHH (childHL (childHL thetaAboveCell1010)))

/-- Subcell `10102231` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10102231 : AngleCell :=
  childLH (childHH (childHL (childHL thetaAboveCell1010)))

/-- Subcell `10102232` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10102232 : AngleCell :=
  childHL (childHH (childHL (childHL thetaAboveCell1010)))

/-- Subcell `10102233` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10102233 : AngleCell :=
  childHH (childHH (childHL (childHL thetaAboveCell1010)))

/-- Subcell `10102300` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10102300 : AngleCell :=
  childLL (childLL (childHH (childHL thetaAboveCell1010)))

/-- Subcell `10102301` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10102301 : AngleCell :=
  childLH (childLL (childHH (childHL thetaAboveCell1010)))

/-- Subcell `10102302` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10102302 : AngleCell :=
  childHL (childLL (childHH (childHL thetaAboveCell1010)))

/-- Subcell `10102303` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10102303 : AngleCell :=
  childHH (childLL (childHH (childHL thetaAboveCell1010)))

/-- Subcell `10102310` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10102310 : AngleCell :=
  childLL (childLH (childHH (childHL thetaAboveCell1010)))

/-- Subcell `10102311` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10102311 : AngleCell :=
  childLH (childLH (childHH (childHL thetaAboveCell1010)))

/-- Subcell `10102312` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10102312 : AngleCell :=
  childHL (childLH (childHH (childHL thetaAboveCell1010)))

/-- Subcell `10102313` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10102313 : AngleCell :=
  childHH (childLH (childHH (childHL thetaAboveCell1010)))

/-- Subcell `10102320` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10102320 : AngleCell :=
  childLL (childHL (childHH (childHL thetaAboveCell1010)))

/-- Subcell `10102321` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10102321 : AngleCell :=
  childLH (childHL (childHH (childHL thetaAboveCell1010)))

/-- Subcell `10102322` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10102322 : AngleCell :=
  childHL (childHL (childHH (childHL thetaAboveCell1010)))

/-- Subcell `10102323` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10102323 : AngleCell :=
  childHH (childHL (childHH (childHL thetaAboveCell1010)))

/-- Subcell `10102330` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10102330 : AngleCell :=
  childLL (childHH (childHH (childHL thetaAboveCell1010)))

/-- Subcell `10102331` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10102331 : AngleCell :=
  childLH (childHH (childHH (childHL thetaAboveCell1010)))

/-- Subcell `10102332` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10102332 : AngleCell :=
  childHL (childHH (childHH (childHL thetaAboveCell1010)))

/-- Subcell `10102333` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10102333 : AngleCell :=
  childHH (childHH (childHH (childHL thetaAboveCell1010)))

/-- Subcell `10103200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10103200 : AngleCell :=
  childLL (childLL (childHL (childHH thetaAboveCell1010)))

/-- Subcell `10103201` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10103201 : AngleCell :=
  childLH (childLL (childHL (childHH thetaAboveCell1010)))

/-- Subcell `10103202` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10103202 : AngleCell :=
  childHL (childLL (childHL (childHH thetaAboveCell1010)))

/-- Subcell `10103203` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10103203 : AngleCell :=
  childHH (childLL (childHL (childHH thetaAboveCell1010)))

/-- Subcell `10103210` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10103210 : AngleCell :=
  childLL (childLH (childHL (childHH thetaAboveCell1010)))

/-- Subcell `10103211` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10103211 : AngleCell :=
  childLH (childLH (childHL (childHH thetaAboveCell1010)))

/-- Subcell `10103212` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10103212 : AngleCell :=
  childHL (childLH (childHL (childHH thetaAboveCell1010)))

/-- Subcell `10103213` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10103213 : AngleCell :=
  childHH (childLH (childHL (childHH thetaAboveCell1010)))

/-- Subcell `10103220` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10103220 : AngleCell :=
  childLL (childHL (childHL (childHH thetaAboveCell1010)))

/-- Subcell `10103221` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10103221 : AngleCell :=
  childLH (childHL (childHL (childHH thetaAboveCell1010)))

/-- Subcell `10103222` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10103222 : AngleCell :=
  childHL (childHL (childHL (childHH thetaAboveCell1010)))

/-- Subcell `10103223` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10103223 : AngleCell :=
  childHH (childHL (childHL (childHH thetaAboveCell1010)))

/-- Subcell `10103230` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10103230 : AngleCell :=
  childLL (childHH (childHL (childHH thetaAboveCell1010)))

/-- Subcell `10103231` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10103231 : AngleCell :=
  childLH (childHH (childHL (childHH thetaAboveCell1010)))

/-- Subcell `10103232` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10103232 : AngleCell :=
  childHL (childHH (childHL (childHH thetaAboveCell1010)))

/-- Subcell `10103233` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10103233 : AngleCell :=
  childHH (childHH (childHL (childHH thetaAboveCell1010)))

/-- Subcell `10103300` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10103300 : AngleCell :=
  childLL (childLL (childHH (childHH thetaAboveCell1010)))

end GerverSofa.PartE.CertificateCells660a83a47d

namespace GerverSofa.PartE.CertificateCellse876d675ca

/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `0001` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0001 : AngleCell :=
  childLH (childLL (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `00003121` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00003121 : AngleCell :=
  childLH (childHL (childLH (childHH thetaAboveCell0000)))

/-- Subcell `00003122` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00003122 : AngleCell :=
  childHL (childHL (childLH (childHH thetaAboveCell0000)))

/-- Subcell `00003123` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00003123 : AngleCell :=
  childHH (childHL (childLH (childHH thetaAboveCell0000)))

/-- Subcell `00003130` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00003130 : AngleCell :=
  childLL (childHH (childLH (childHH thetaAboveCell0000)))

/-- Subcell `00003131` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00003131 : AngleCell :=
  childLH (childHH (childLH (childHH thetaAboveCell0000)))

/-- Subcell `00003132` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00003132 : AngleCell :=
  childHL (childHH (childLH (childHH thetaAboveCell0000)))

/-- Subcell `00003133` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00003133 : AngleCell :=
  childHH (childHH (childLH (childHH thetaAboveCell0000)))

/-- Subcell `00003200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00003200 : AngleCell :=
  childLL (childLL (childHL (childHH thetaAboveCell0000)))

/-- Subcell `00003201` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00003201 : AngleCell :=
  childLH (childLL (childHL (childHH thetaAboveCell0000)))

/-- Subcell `00003202` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00003202 : AngleCell :=
  childHL (childLL (childHL (childHH thetaAboveCell0000)))

/-- Subcell `00003203` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00003203 : AngleCell :=
  childHH (childLL (childHL (childHH thetaAboveCell0000)))

/-- Subcell `00003210` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00003210 : AngleCell :=
  childLL (childLH (childHL (childHH thetaAboveCell0000)))

/-- Subcell `00003211` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00003211 : AngleCell :=
  childLH (childLH (childHL (childHH thetaAboveCell0000)))

/-- Subcell `00003212` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00003212 : AngleCell :=
  childHL (childLH (childHL (childHH thetaAboveCell0000)))

/-- Subcell `00003213` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00003213 : AngleCell :=
  childHH (childLH (childHL (childHH thetaAboveCell0000)))

/-- Subcell `00003220` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00003220 : AngleCell :=
  childLL (childHL (childHL (childHH thetaAboveCell0000)))

/-- Subcell `00003221` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00003221 : AngleCell :=
  childLH (childHL (childHL (childHH thetaAboveCell0000)))

/-- Subcell `00003222` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00003222 : AngleCell :=
  childHL (childHL (childHL (childHH thetaAboveCell0000)))

/-- Subcell `00003223` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00003223 : AngleCell :=
  childHH (childHL (childHL (childHH thetaAboveCell0000)))

/-- Subcell `00003230` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00003230 : AngleCell :=
  childLL (childHH (childHL (childHH thetaAboveCell0000)))

/-- Subcell `00003231` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00003231 : AngleCell :=
  childLH (childHH (childHL (childHH thetaAboveCell0000)))

/-- Subcell `00003232` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00003232 : AngleCell :=
  childHL (childHH (childHL (childHH thetaAboveCell0000)))

/-- Subcell `00003233` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00003233 : AngleCell :=
  childHH (childHH (childHL (childHH thetaAboveCell0000)))

/-- Subcell `00003300` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00003300 : AngleCell :=
  childLL (childLL (childHH (childHH thetaAboveCell0000)))

/-- Subcell `00003301` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00003301 : AngleCell :=
  childLH (childLL (childHH (childHH thetaAboveCell0000)))

/-- Subcell `00003302` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00003302 : AngleCell :=
  childHL (childLL (childHH (childHH thetaAboveCell0000)))

/-- Subcell `00003303` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00003303 : AngleCell :=
  childHH (childLL (childHH (childHH thetaAboveCell0000)))

/-- Subcell `00003310` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00003310 : AngleCell :=
  childLL (childLH (childHH (childHH thetaAboveCell0000)))

/-- Subcell `00003311` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00003311 : AngleCell :=
  childLH (childLH (childHH (childHH thetaAboveCell0000)))

/-- Subcell `00003312` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00003312 : AngleCell :=
  childHL (childLH (childHH (childHH thetaAboveCell0000)))

/-- Subcell `00003313` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00003313 : AngleCell :=
  childHH (childLH (childHH (childHH thetaAboveCell0000)))

/-- Subcell `00003320` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00003320 : AngleCell :=
  childLL (childHL (childHH (childHH thetaAboveCell0000)))

/-- Subcell `00003321` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00003321 : AngleCell :=
  childLH (childHL (childHH (childHH thetaAboveCell0000)))

/-- Subcell `00003322` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00003322 : AngleCell :=
  childHL (childHL (childHH (childHH thetaAboveCell0000)))

/-- Subcell `00003323` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00003323 : AngleCell :=
  childHH (childHL (childHH (childHH thetaAboveCell0000)))

/-- Subcell `00003330` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00003330 : AngleCell :=
  childLL (childHH (childHH (childHH thetaAboveCell0000)))

/-- Subcell `00003331` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00003331 : AngleCell :=
  childLH (childHH (childHH (childHH thetaAboveCell0000)))

/-- Subcell `00003332` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00003332 : AngleCell :=
  childHL (childHH (childHH (childHH thetaAboveCell0000)))

/-- Subcell `00003333` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00003333 : AngleCell :=
  childHH (childHH (childHH (childHH thetaAboveCell0000)))

/-- Subcell `00012020` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00012020 : AngleCell :=
  childLL (childHL (childLL (childHL thetaAboveCell0001)))

/-- Subcell `00012021` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00012021 : AngleCell :=
  childLH (childHL (childLL (childHL thetaAboveCell0001)))

/-- Subcell `00012022` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00012022 : AngleCell :=
  childHL (childHL (childLL (childHL thetaAboveCell0001)))

/-- Subcell `00012023` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00012023 : AngleCell :=
  childHH (childHL (childLL (childHL thetaAboveCell0001)))

/-- Subcell `00012030` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00012030 : AngleCell :=
  childLL (childHH (childLL (childHL thetaAboveCell0001)))

/-- Subcell `00012031` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00012031 : AngleCell :=
  childLH (childHH (childLL (childHL thetaAboveCell0001)))

/-- Subcell `00012032` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00012032 : AngleCell :=
  childHL (childHH (childLL (childHL thetaAboveCell0001)))

/-- Subcell `00012033` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00012033 : AngleCell :=
  childHH (childHH (childLL (childHL thetaAboveCell0001)))

/-- Subcell `00012120` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00012120 : AngleCell :=
  childLL (childHL (childLH (childHL thetaAboveCell0001)))

/-- Subcell `00012121` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00012121 : AngleCell :=
  childLH (childHL (childLH (childHL thetaAboveCell0001)))

/-- Subcell `00012122` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00012122 : AngleCell :=
  childHL (childHL (childLH (childHL thetaAboveCell0001)))

/-- Subcell `00012123` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00012123 : AngleCell :=
  childHH (childHL (childLH (childHL thetaAboveCell0001)))

/-- Subcell `00012130` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00012130 : AngleCell :=
  childLL (childHH (childLH (childHL thetaAboveCell0001)))

/-- Subcell `00012131` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00012131 : AngleCell :=
  childLH (childHH (childLH (childHL thetaAboveCell0001)))

/-- Subcell `00012132` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00012132 : AngleCell :=
  childHL (childHH (childLH (childHL thetaAboveCell0001)))

/-- Subcell `00012133` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00012133 : AngleCell :=
  childHH (childHH (childLH (childHL thetaAboveCell0001)))

/-- Subcell `00012200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00012200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0001)))

/-- Subcell `00012201` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00012201 : AngleCell :=
  childLH (childLL (childHL (childHL thetaAboveCell0001)))

/-- Subcell `00012202` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00012202 : AngleCell :=
  childHL (childLL (childHL (childHL thetaAboveCell0001)))

/-- Subcell `00012203` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00012203 : AngleCell :=
  childHH (childLL (childHL (childHL thetaAboveCell0001)))

/-- Subcell `00012210` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00012210 : AngleCell :=
  childLL (childLH (childHL (childHL thetaAboveCell0001)))

/-- Subcell `00012211` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00012211 : AngleCell :=
  childLH (childLH (childHL (childHL thetaAboveCell0001)))

/-- Subcell `00012212` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00012212 : AngleCell :=
  childHL (childLH (childHL (childHL thetaAboveCell0001)))

/-- Subcell `00012213` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00012213 : AngleCell :=
  childHH (childLH (childHL (childHL thetaAboveCell0001)))

/-- Subcell `00012220` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00012220 : AngleCell :=
  childLL (childHL (childHL (childHL thetaAboveCell0001)))

/-- Subcell `00012221` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00012221 : AngleCell :=
  childLH (childHL (childHL (childHL thetaAboveCell0001)))

/-- Subcell `00012222` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00012222 : AngleCell :=
  childHL (childHL (childHL (childHL thetaAboveCell0001)))

/-- Subcell `00012223` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00012223 : AngleCell :=
  childHH (childHL (childHL (childHL thetaAboveCell0001)))

/-- Subcell `00012230` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00012230 : AngleCell :=
  childLL (childHH (childHL (childHL thetaAboveCell0001)))

/-- Subcell `00012231` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00012231 : AngleCell :=
  childLH (childHH (childHL (childHL thetaAboveCell0001)))

/-- Subcell `00012232` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00012232 : AngleCell :=
  childHL (childHH (childHL (childHL thetaAboveCell0001)))

/-- Subcell `00012233` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00012233 : AngleCell :=
  childHH (childHH (childHL (childHL thetaAboveCell0001)))

/-- Subcell `00012300` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00012300 : AngleCell :=
  childLL (childLL (childHH (childHL thetaAboveCell0001)))

/-- Subcell `00012301` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00012301 : AngleCell :=
  childLH (childLL (childHH (childHL thetaAboveCell0001)))

/-- Subcell `00012302` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00012302 : AngleCell :=
  childHL (childLL (childHH (childHL thetaAboveCell0001)))

/-- Subcell `00012303` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00012303 : AngleCell :=
  childHH (childLL (childHH (childHL thetaAboveCell0001)))

/-- Subcell `00012310` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00012310 : AngleCell :=
  childLL (childLH (childHH (childHL thetaAboveCell0001)))

/-- Subcell `00012311` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00012311 : AngleCell :=
  childLH (childLH (childHH (childHL thetaAboveCell0001)))

/-- Subcell `00012312` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00012312 : AngleCell :=
  childHL (childLH (childHH (childHL thetaAboveCell0001)))

/-- Subcell `00012313` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00012313 : AngleCell :=
  childHH (childLH (childHH (childHL thetaAboveCell0001)))

/-- Subcell `00012320` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00012320 : AngleCell :=
  childLL (childHL (childHH (childHL thetaAboveCell0001)))

/-- Subcell `00012321` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00012321 : AngleCell :=
  childLH (childHL (childHH (childHL thetaAboveCell0001)))

/-- Subcell `00012322` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00012322 : AngleCell :=
  childHL (childHL (childHH (childHL thetaAboveCell0001)))

/-- Subcell `00012323` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00012323 : AngleCell :=
  childHH (childHL (childHH (childHL thetaAboveCell0001)))

/-- Subcell `00012330` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00012330 : AngleCell :=
  childLL (childHH (childHH (childHL thetaAboveCell0001)))

/-- Subcell `00012331` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00012331 : AngleCell :=
  childLH (childHH (childHH (childHL thetaAboveCell0001)))

/-- Subcell `00012332` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00012332 : AngleCell :=
  childHL (childHH (childHH (childHL thetaAboveCell0001)))

/-- Subcell `00012333` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00012333 : AngleCell :=
  childHH (childHH (childHH (childHL thetaAboveCell0001)))

/-- Subcell `00013020` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00013020 : AngleCell :=
  childLL (childHL (childLL (childHH thetaAboveCell0001)))

/-- Subcell `00013021` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00013021 : AngleCell :=
  childLH (childHL (childLL (childHH thetaAboveCell0001)))

/-- Subcell `00013022` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00013022 : AngleCell :=
  childHL (childHL (childLL (childHH thetaAboveCell0001)))

/-- Subcell `00013023` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00013023 : AngleCell :=
  childHH (childHL (childLL (childHH thetaAboveCell0001)))

/-- Subcell `00013030` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00013030 : AngleCell :=
  childLL (childHH (childLL (childHH thetaAboveCell0001)))

/-- Subcell `00013031` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00013031 : AngleCell :=
  childLH (childHH (childLL (childHH thetaAboveCell0001)))

/-- Subcell `00013032` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00013032 : AngleCell :=
  childHL (childHH (childLL (childHH thetaAboveCell0001)))

/-- Subcell `00013033` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00013033 : AngleCell :=
  childHH (childHH (childLL (childHH thetaAboveCell0001)))

/-- Subcell `00013120` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00013120 : AngleCell :=
  childLL (childHL (childLH (childHH thetaAboveCell0001)))

/-- Subcell `00013121` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00013121 : AngleCell :=
  childLH (childHL (childLH (childHH thetaAboveCell0001)))

/-- Subcell `00013122` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00013122 : AngleCell :=
  childHL (childHL (childLH (childHH thetaAboveCell0001)))

/-- Subcell `00013123` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00013123 : AngleCell :=
  childHH (childHL (childLH (childHH thetaAboveCell0001)))

/-- Subcell `00013130` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00013130 : AngleCell :=
  childLL (childHH (childLH (childHH thetaAboveCell0001)))

/-- Subcell `00013131` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00013131 : AngleCell :=
  childLH (childHH (childLH (childHH thetaAboveCell0001)))

/-- Subcell `00013132` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00013132 : AngleCell :=
  childHL (childHH (childLH (childHH thetaAboveCell0001)))

/-- Subcell `00013133` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00013133 : AngleCell :=
  childHH (childHH (childLH (childHH thetaAboveCell0001)))

/-- Subcell `00013200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00013200 : AngleCell :=
  childLL (childLL (childHL (childHH thetaAboveCell0001)))

/-- Subcell `00013201` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00013201 : AngleCell :=
  childLH (childLL (childHL (childHH thetaAboveCell0001)))

/-- Subcell `00013202` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00013202 : AngleCell :=
  childHL (childLL (childHL (childHH thetaAboveCell0001)))

/-- Subcell `00013203` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00013203 : AngleCell :=
  childHH (childLL (childHL (childHH thetaAboveCell0001)))

/-- Subcell `00013210` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00013210 : AngleCell :=
  childLL (childLH (childHL (childHH thetaAboveCell0001)))

/-- Subcell `00013211` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00013211 : AngleCell :=
  childLH (childLH (childHL (childHH thetaAboveCell0001)))

/-- Subcell `00013212` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00013212 : AngleCell :=
  childHL (childLH (childHL (childHH thetaAboveCell0001)))

/-- Subcell `00013213` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00013213 : AngleCell :=
  childHH (childLH (childHL (childHH thetaAboveCell0001)))

/-- Subcell `00013220` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00013220 : AngleCell :=
  childLL (childHL (childHL (childHH thetaAboveCell0001)))

/-- Subcell `00013221` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00013221 : AngleCell :=
  childLH (childHL (childHL (childHH thetaAboveCell0001)))

/-- Subcell `00013222` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00013222 : AngleCell :=
  childHL (childHL (childHL (childHH thetaAboveCell0001)))

/-- Subcell `00013223` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00013223 : AngleCell :=
  childHH (childHL (childHL (childHH thetaAboveCell0001)))

/-- Subcell `00013230` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00013230 : AngleCell :=
  childLL (childHH (childHL (childHH thetaAboveCell0001)))

/-- Subcell `00013231` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00013231 : AngleCell :=
  childLH (childHH (childHL (childHH thetaAboveCell0001)))

/-- Subcell `00013232` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00013232 : AngleCell :=
  childHL (childHH (childHL (childHH thetaAboveCell0001)))

/-- Subcell `00013233` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00013233 : AngleCell :=
  childHH (childHH (childHL (childHH thetaAboveCell0001)))

/-- Subcell `00013300` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00013300 : AngleCell :=
  childLL (childLL (childHH (childHH thetaAboveCell0001)))

/-- Subcell `00013301` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00013301 : AngleCell :=
  childLH (childLL (childHH (childHH thetaAboveCell0001)))

/-- Subcell `00013302` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00013302 : AngleCell :=
  childHL (childLL (childHH (childHH thetaAboveCell0001)))

/-- Subcell `00013303` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00013303 : AngleCell :=
  childHH (childLL (childHH (childHH thetaAboveCell0001)))

/-- Subcell `00013310` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00013310 : AngleCell :=
  childLL (childLH (childHH (childHH thetaAboveCell0001)))

/-- Subcell `00013311` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00013311 : AngleCell :=
  childLH (childLH (childHH (childHH thetaAboveCell0001)))

/-- Subcell `00013312` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00013312 : AngleCell :=
  childHL (childLH (childHH (childHH thetaAboveCell0001)))

end GerverSofa.PartE.CertificateCellse876d675ca

section

/-
Copyright (c) 2026 Dawid Trela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dawid Trela
-/
/-!
# Gerver sofa dependency batch

* `KernelOnly.PartE.E24KC5TerminalBatchT409600011`.
* `KernelOnly.PartE.E24KC5TerminalBatchT460800012`.
-/

public section

noncomputable section

section

/-! E24KC5 checkpoint-aware kernel batch. -/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells0c0d0adfef

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells0c0d0adfef

open CertificateCells0c0d0adfef
theorem e24KC2ThetaAboveLeaf1000320222 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell10003202)) = true := by
  have h : ((childHL (childHL thetaAboveCell10003202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL thetaAboveCell10003202)) h
theorem e24KC2ThetaAboveLeaf1000320223 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell10003202)) = true := by
  have h : ((childHH (childHL thetaAboveCell10003202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL thetaAboveCell10003202)) h
theorem e24KC2ThetaAboveLeaf1000320230 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell10003202)) = true := by
  have h : ((childLL (childHH thetaAboveCell10003202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell10003202)) h
theorem e24KC2ThetaAboveLeaf1000320231 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell10003202)) = true := by
  have h : ((childLH (childHH thetaAboveCell10003202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell10003202)) h
theorem e24KC2ThetaAboveLeaf1000320232 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell10003202)) = true := by
  have h : ((childHL (childHH thetaAboveCell10003202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH thetaAboveCell10003202)) h
theorem e24KC2ThetaAboveLeaf1000320233 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell10003202)) = true := by
  have h : ((childHH (childHH thetaAboveCell10003202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH thetaAboveCell10003202)) h
theorem e24KC2ThetaAboveLeaf1000320300 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell10003203)) = true := by
  have h : ((childLL (childLL thetaAboveCell10003203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell10003203)) h
theorem e24KC2ThetaAboveLeaf1000320301 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell10003203)) = true := by
  have h : ((childLH (childLL thetaAboveCell10003203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell10003203)) h
theorem e24KC2ThetaAboveLeaf1000320302 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell10003203)) = true := by
  have h : ((childHL (childLL thetaAboveCell10003203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell10003203)) h
theorem e24KC2ThetaAboveLeaf1000320303 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell10003203)) = true := by
  have h : ((childHH (childLL thetaAboveCell10003203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell10003203)) h
theorem e24KC2ThetaAboveLeaf1000320310 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell10003203)) = true := by
  have h : ((childLL (childLH thetaAboveCell10003203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell10003203)) h
theorem e24KC2ThetaAboveLeaf1000320311 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell10003203)) = true := by
  have h : ((childLH (childLH thetaAboveCell10003203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell10003203)) h
theorem e24KC2ThetaAboveLeaf1000320312 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell10003203)) = true := by
  have h : ((childHL (childLH thetaAboveCell10003203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell10003203)) h
theorem e24KC2ThetaAboveLeaf1000320313 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell10003203)) = true := by
  have h : ((childHH (childLH thetaAboveCell10003203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell10003203)) h
theorem e24KC2ThetaAboveLeaf1000320320 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell10003203)) = true := by
  have h : ((childLL (childHL thetaAboveCell10003203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell10003203)) h
theorem e24KC2ThetaAboveLeaf1000320321 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell10003203)) = true := by
  have h : ((childLH (childHL thetaAboveCell10003203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell10003203)) h
theorem e24KC2ThetaAboveLeaf1000320322 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell10003203)) = true := by
  have h : ((childHL (childHL thetaAboveCell10003203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL thetaAboveCell10003203)) h
theorem e24KC2ThetaAboveLeaf1000320323 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell10003203)) = true := by
  have h : ((childHH (childHL thetaAboveCell10003203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL thetaAboveCell10003203)) h
theorem e24KC2ThetaAboveLeaf1000320330 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell10003203)) = true := by
  have h : ((childLL (childHH thetaAboveCell10003203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell10003203)) h
theorem e24KC2ThetaAboveLeaf1000320331 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell10003203)) = true := by
  have h : ((childLH (childHH thetaAboveCell10003203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell10003203)) h
theorem e24KC2ThetaAboveLeaf1000320332 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell10003203)) = true := by
  have h : ((childHL (childHH thetaAboveCell10003203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH thetaAboveCell10003203)) h
theorem e24KC2ThetaAboveLeaf1000320333 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell10003203)) = true := by
  have h : ((childHH (childHH thetaAboveCell10003203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH thetaAboveCell10003203)) h
theorem e24KC2ThetaAboveLeaf100032100 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10003210) = true := by
  have h : ((childLL thetaAboveCell10003210)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell10003210) h
theorem e24KC2ThetaAboveLeaf100032101 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10003210) = true := by
  have h : ((childLH thetaAboveCell10003210)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell10003210) h
theorem e24KC2ThetaAboveLeaf100032102 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10003210) = true := by
  have h : ((childHL thetaAboveCell10003210)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell10003210) h
theorem e24KC2ThetaAboveLeaf100032103 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10003210) = true := by
  have h : ((childHH thetaAboveCell10003210)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell10003210) h
theorem e24KC2ThetaAboveLeaf100032110 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10003211) = true := by
  have h : ((childLL thetaAboveCell10003211)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell10003211) h
theorem e24KC2ThetaAboveLeaf100032111 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10003211) = true := by
  have h : ((childLH thetaAboveCell10003211)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell10003211) h
theorem e24KC2ThetaAboveLeaf100032112 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10003211) = true := by
  have h : ((childHL thetaAboveCell10003211)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell10003211) h
theorem e24KC2ThetaAboveLeaf100032113 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10003211) = true := by
  have h : ((childHH thetaAboveCell10003211)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell10003211) h
theorem e24KC2ThetaAboveLeaf1000321200 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell10003212)) = true := by
  have h : ((childLL (childLL thetaAboveCell10003212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell10003212)) h
theorem e24KC2ThetaAboveLeaf1000321201 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell10003212)) = true := by
  have h : ((childLH (childLL thetaAboveCell10003212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell10003212)) h
theorem e24KC2ThetaAboveLeaf1000321202 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell10003212)) = true := by
  have h : ((childHL (childLL thetaAboveCell10003212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell10003212)) h
theorem e24KC2ThetaAboveLeaf1000321203 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell10003212)) = true := by
  have h : ((childHH (childLL thetaAboveCell10003212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell10003212)) h
theorem e24KC2ThetaAboveLeaf1000321210 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell10003212)) = true := by
  have h : ((childLL (childLH thetaAboveCell10003212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell10003212)) h
theorem e24KC2ThetaAboveLeaf1000321211 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell10003212)) = true := by
  have h : ((childLH (childLH thetaAboveCell10003212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell10003212)) h
theorem e24KC2ThetaAboveLeaf1000321212 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell10003212)) = true := by
  have h : ((childHL (childLH thetaAboveCell10003212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell10003212)) h
theorem e24KC2ThetaAboveLeaf1000321213 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell10003212)) = true := by
  have h : ((childHH (childLH thetaAboveCell10003212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell10003212)) h
theorem e24KC2ThetaAboveLeaf1000321220 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell10003212)) = true := by
  have h : ((childLL (childHL thetaAboveCell10003212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell10003212)) h
theorem e24KC2ThetaAboveLeaf1000321221 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell10003212)) = true := by
  have h : ((childLH (childHL thetaAboveCell10003212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell10003212)) h
theorem e24KC2ThetaAboveLeaf1000321222 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell10003212)) = true := by
  have h : ((childHL (childHL thetaAboveCell10003212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL thetaAboveCell10003212)) h
theorem e24KC2ThetaAboveLeaf1000321223 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell10003212)) = true := by
  have h : ((childHH (childHL thetaAboveCell10003212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL thetaAboveCell10003212)) h
theorem e24KC2ThetaAboveLeaf1000321230 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell10003212)) = true := by
  have h : ((childLL (childHH thetaAboveCell10003212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell10003212)) h
theorem e24KC2ThetaAboveLeaf1000321231 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell10003212)) = true := by
  have h : ((childLH (childHH thetaAboveCell10003212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell10003212)) h
theorem e24KC2ThetaAboveLeaf1000321232 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell10003212)) = true := by
  have h : ((childHL (childHH thetaAboveCell10003212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH thetaAboveCell10003212)) h
theorem e24KC2ThetaAboveLeaf1000321233 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell10003212)) = true := by
  have h : ((childHH (childHH thetaAboveCell10003212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH thetaAboveCell10003212)) h
theorem e24KC2ThetaAboveLeaf1000321300 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell10003213)) = true := by
  have h : ((childLL (childLL thetaAboveCell10003213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell10003213)) h
theorem e24KC2ThetaAboveLeaf1000321301 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell10003213)) = true := by
  have h : ((childLH (childLL thetaAboveCell10003213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell10003213)) h
theorem e24KC2ThetaAboveLeaf1000321302 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell10003213)) = true := by
  have h : ((childHL (childLL thetaAboveCell10003213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell10003213)) h
theorem e24KC2ThetaAboveLeaf1000321303 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell10003213)) = true := by
  have h : ((childHH (childLL thetaAboveCell10003213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell10003213)) h
theorem e24KC2ThetaAboveLeaf1000321310 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell10003213)) = true := by
  have h : ((childLL (childLH thetaAboveCell10003213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell10003213)) h
theorem e24KC2ThetaAboveLeaf1000321311 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell10003213)) = true := by
  have h : ((childLH (childLH thetaAboveCell10003213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell10003213)) h
theorem e24KC2ThetaAboveLeaf1000321312 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell10003213)) = true := by
  have h : ((childHL (childLH thetaAboveCell10003213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell10003213)) h
theorem e24KC2ThetaAboveLeaf1000321313 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell10003213)) = true := by
  have h : ((childHH (childLH thetaAboveCell10003213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell10003213)) h
theorem e24KC2ThetaAboveLeaf1000321320 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell10003213)) = true := by
  have h : ((childLL (childHL thetaAboveCell10003213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell10003213)) h
theorem e24KC2ThetaAboveLeaf1000321321 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell10003213)) = true := by
  have h : ((childLH (childHL thetaAboveCell10003213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell10003213)) h
theorem e24KC2ThetaAboveLeaf1000321322 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell10003213)) = true := by
  have h : ((childHL (childHL thetaAboveCell10003213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL thetaAboveCell10003213)) h
theorem e24KC2ThetaAboveLeaf1000321323 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell10003213)) = true := by
  have h : ((childHH (childHL thetaAboveCell10003213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL thetaAboveCell10003213)) h
theorem e24KC2ThetaAboveLeaf1000321330 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell10003213)) = true := by
  have h : ((childLL (childHH thetaAboveCell10003213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell10003213)) h
theorem e24KC2ThetaAboveLeaf1000321331 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell10003213)) = true := by
  have h : ((childLH (childHH thetaAboveCell10003213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell10003213)) h
theorem e24KC2ThetaAboveLeaf1000321332 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell10003213)) = true := by
  have h : ((childHL (childHH thetaAboveCell10003213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH thetaAboveCell10003213)) h
theorem e24KC2ThetaAboveLeaf1000321333 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell10003213)) = true := by
  have h : ((childHH (childHH thetaAboveCell10003213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH thetaAboveCell10003213)) h
theorem e24KC2ThetaAboveLeaf100032200 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10003220) = true := by
  have h : ((childLL thetaAboveCell10003220)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell10003220) h
theorem e24KC2ThetaAboveLeaf100032201 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10003220) = true := by
  have h : ((childLH thetaAboveCell10003220)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell10003220) h
theorem e24KC2ThetaAboveLeaf100032202 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10003220) = true := by
  have h : ((childHL thetaAboveCell10003220)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell10003220) h
theorem e24KC2ThetaAboveLeaf100032203 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10003220) = true := by
  have h : ((childHH thetaAboveCell10003220)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell10003220) h
theorem e24KC2ThetaAboveLeaf100032210 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10003221) = true := by
  have h : ((childLL thetaAboveCell10003221)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell10003221) h
theorem e24KC2ThetaAboveLeaf100032211 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10003221) = true := by
  have h : ((childLH thetaAboveCell10003221)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell10003221) h
theorem e24KC2ThetaAboveLeaf100032212 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10003221) = true := by
  have h : ((childHL thetaAboveCell10003221)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell10003221) h
theorem e24KC2ThetaAboveLeaf100032213 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10003221) = true := by
  have h : ((childHH thetaAboveCell10003221)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell10003221) h
theorem e24KC2ThetaAboveLeaf10003222 :
    adaptiveCoverCheck 11 thetaAboveCell10003222 = true := by
  have h : (thetaAboveCell10003222).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell10003222 h
theorem e24KC2ThetaAboveLeaf10003223 :
    adaptiveCoverCheck 11 thetaAboveCell10003223 = true := by
  have h : (thetaAboveCell10003223).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell10003223 h
theorem e24KC2ThetaAboveLeaf100032300 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10003230) = true := by
  have h : ((childLL thetaAboveCell10003230)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell10003230) h
theorem e24KC2ThetaAboveLeaf100032301 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10003230) = true := by
  have h : ((childLH thetaAboveCell10003230)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell10003230) h
theorem e24KC2ThetaAboveLeaf100032302 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10003230) = true := by
  have h : ((childHL thetaAboveCell10003230)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell10003230) h
theorem e24KC2ThetaAboveLeaf100032303 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10003230) = true := by
  have h : ((childHH thetaAboveCell10003230)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell10003230) h
theorem e24KC2ThetaAboveLeaf100032310 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10003231) = true := by
  have h : ((childLL thetaAboveCell10003231)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell10003231) h
theorem e24KC2ThetaAboveLeaf100032311 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10003231) = true := by
  have h : ((childLH thetaAboveCell10003231)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell10003231) h
theorem e24KC2ThetaAboveLeaf100032312 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10003231) = true := by
  have h : ((childHL thetaAboveCell10003231)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell10003231) h
theorem e24KC2ThetaAboveLeaf100032313 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10003231) = true := by
  have h : ((childHH thetaAboveCell10003231)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell10003231) h
theorem e24KC2ThetaAboveLeaf10003232 :
    adaptiveCoverCheck 11 thetaAboveCell10003232 = true := by
  have h : (thetaAboveCell10003232).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell10003232 h
theorem e24KC2ThetaAboveLeaf10003233 :
    adaptiveCoverCheck 11 thetaAboveCell10003233 = true := by
  have h : (thetaAboveCell10003233).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell10003233 h
theorem e24KC2ThetaAboveLeaf100033000 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10003300) = true := by
  have h : ((childLL thetaAboveCell10003300)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell10003300) h
theorem e24KC2ThetaAboveLeaf100033001 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10003300) = true := by
  have h : ((childLH thetaAboveCell10003300)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell10003300) h
theorem e24KC2ThetaAboveLeaf100033002 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10003300) = true := by
  have h : ((childHL thetaAboveCell10003300)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell10003300) h
theorem e24KC2ThetaAboveLeaf100033003 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10003300) = true := by
  have h : ((childHH thetaAboveCell10003300)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell10003300) h
theorem e24KC2ThetaAboveLeaf100033010 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10003301) = true := by
  have h : ((childLL thetaAboveCell10003301)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell10003301) h
theorem e24KC2ThetaAboveLeaf100033011 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10003301) = true := by
  have h : ((childLH thetaAboveCell10003301)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell10003301) h
theorem e24KC2ThetaAboveLeaf100033012 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10003301) = true := by
  have h : ((childHL thetaAboveCell10003301)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell10003301) h
theorem e24KC2ThetaAboveLeaf100033013 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10003301) = true := by
  have h : ((childHH thetaAboveCell10003301)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell10003301) h
theorem e24KC2ThetaAboveLeaf1000330200 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell10003302)) = true := by
  have h : ((childLL (childLL thetaAboveCell10003302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell10003302)) h
theorem e24KC2ThetaAboveLeaf1000330201 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell10003302)) = true := by
  have h : ((childLH (childLL thetaAboveCell10003302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell10003302)) h
theorem e24KC2ThetaAboveLeaf1000330202 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell10003302)) = true := by
  have h : ((childHL (childLL thetaAboveCell10003302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell10003302)) h
theorem e24KC2ThetaAboveLeaf1000330203 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell10003302)) = true := by
  have h : ((childHH (childLL thetaAboveCell10003302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell10003302)) h
theorem e24KC2ThetaAboveLeaf1000330210 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell10003302)) = true := by
  have h : ((childLL (childLH thetaAboveCell10003302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell10003302)) h
theorem e24KC2ThetaAboveLeaf1000330211 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell10003302)) = true := by
  have h : ((childLH (childLH thetaAboveCell10003302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell10003302)) h
theorem e24KC2ThetaAboveLeaf1000330212 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell10003302)) = true := by
  have h : ((childHL (childLH thetaAboveCell10003302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell10003302)) h
theorem e24KC2ThetaAboveLeaf1000330213 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell10003302)) = true := by
  have h : ((childHH (childLH thetaAboveCell10003302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell10003302)) h
theorem e24KC2ThetaAboveLeaf1000330220 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell10003302)) = true := by
  have h : ((childLL (childHL thetaAboveCell10003302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell10003302)) h
theorem e24KC2ThetaAboveLeaf1000330221 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell10003302)) = true := by
  have h : ((childLH (childHL thetaAboveCell10003302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell10003302)) h
theorem e24KC2ThetaAboveLeaf1000330222 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell10003302)) = true := by
  have h : ((childHL (childHL thetaAboveCell10003302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL thetaAboveCell10003302)) h
theorem e24KC2ThetaAboveLeaf1000330223 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell10003302)) = true := by
  have h : ((childHH (childHL thetaAboveCell10003302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL thetaAboveCell10003302)) h
theorem e24KC2ThetaAboveLeaf1000330230 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell10003302)) = true := by
  have h : ((childLL (childHH thetaAboveCell10003302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell10003302)) h
theorem e24KC2ThetaAboveLeaf1000330231 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell10003302)) = true := by
  have h : ((childLH (childHH thetaAboveCell10003302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell10003302)) h
theorem e24KC2ThetaAboveLeaf1000330232 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell10003302)) = true := by
  have h : ((childHL (childHH thetaAboveCell10003302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH thetaAboveCell10003302)) h
theorem e24KC2ThetaAboveLeaf1000330233 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell10003302)) = true := by
  have h : ((childHH (childHH thetaAboveCell10003302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH thetaAboveCell10003302)) h
theorem e24KC2ThetaAboveLeaf1000330300 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell10003303)) = true := by
  have h : ((childLL (childLL thetaAboveCell10003303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell10003303)) h
theorem e24KC2ThetaAboveLeaf1000330301 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell10003303)) = true := by
  have h : ((childLH (childLL thetaAboveCell10003303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell10003303)) h
theorem e24KC2ThetaAboveLeaf1000330302 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell10003303)) = true := by
  have h : ((childHL (childLL thetaAboveCell10003303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell10003303)) h
theorem e24KC2ThetaAboveLeaf1000330303 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell10003303)) = true := by
  have h : ((childHH (childLL thetaAboveCell10003303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell10003303)) h
theorem e24KC2ThetaAboveLeaf1000330310 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell10003303)) = true := by
  have h : ((childLL (childLH thetaAboveCell10003303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell10003303)) h
theorem e24KC2ThetaAboveLeaf1000330311 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell10003303)) = true := by
  have h : ((childLH (childLH thetaAboveCell10003303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell10003303)) h
theorem e24KC2ThetaAboveLeaf1000330312 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell10003303)) = true := by
  have h : ((childHL (childLH thetaAboveCell10003303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell10003303)) h
theorem e24KC2ThetaAboveLeaf1000330313 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell10003303)) = true := by
  have h : ((childHH (childLH thetaAboveCell10003303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell10003303)) h
theorem e24KC2ThetaAboveLeaf1000330320 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell10003303)) = true := by
  have h : ((childLL (childHL thetaAboveCell10003303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell10003303)) h
theorem e24KC2ThetaAboveLeaf1000330321 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell10003303)) = true := by
  have h : ((childLH (childHL thetaAboveCell10003303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell10003303)) h
theorem e24KC2ThetaAboveLeaf1000330322 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell10003303)) = true := by
  have h : ((childHL (childHL thetaAboveCell10003303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL thetaAboveCell10003303)) h
theorem e24KC2ThetaAboveLeaf1000330323 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell10003303)) = true := by
  have h : ((childHH (childHL thetaAboveCell10003303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL thetaAboveCell10003303)) h
theorem e24KC2ThetaAboveLeaf1000330330 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell10003303)) = true := by
  have h : ((childLL (childHH thetaAboveCell10003303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell10003303)) h
theorem e24KC2ThetaAboveLeaf1000330331 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell10003303)) = true := by
  have h : ((childLH (childHH thetaAboveCell10003303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell10003303)) h
theorem e24KC2ThetaAboveLeaf1000330332 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell10003303)) = true := by
  have h : ((childHL (childHH thetaAboveCell10003303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH thetaAboveCell10003303)) h
theorem e24KC2ThetaAboveLeaf1000330333 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell10003303)) = true := by
  have h : ((childHH (childHH thetaAboveCell10003303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH thetaAboveCell10003303)) h
theorem e24KC2ThetaAboveLeaf100033100 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10003310) = true := by
  have h : ((childLL thetaAboveCell10003310)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell10003310) h
theorem e24KC2ThetaAboveLeaf100033101 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10003310) = true := by
  have h : ((childLH thetaAboveCell10003310)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell10003310) h
theorem e24KC2ThetaAboveLeaf100033102 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10003310) = true := by
  have h : ((childHL thetaAboveCell10003310)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell10003310) h
theorem e24KC2ThetaAboveLeaf100033103 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10003310) = true := by
  have h : ((childHH thetaAboveCell10003310)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell10003310) h
theorem e24KC2ThetaAboveLeaf100033110 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10003311) = true := by
  have h : ((childLL thetaAboveCell10003311)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell10003311) h
theorem e24KC2ThetaAboveLeaf100033111 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10003311) = true := by
  have h : ((childLH thetaAboveCell10003311)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell10003311) h
theorem e24KC2ThetaAboveLeaf100033112 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10003311) = true := by
  have h : ((childHL thetaAboveCell10003311)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell10003311) h
theorem e24KC2ThetaAboveLeaf100033113 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10003311) = true := by
  have h : ((childHH thetaAboveCell10003311)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell10003311) h
theorem e24KC2ThetaAboveLeaf1000331200 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell10003312)) = true := by
  have h : ((childLL (childLL thetaAboveCell10003312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell10003312)) h
theorem e24KC2ThetaAboveLeaf1000331201 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell10003312)) = true := by
  have h : ((childLH (childLL thetaAboveCell10003312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell10003312)) h
theorem e24KC2ThetaAboveLeaf1000331202 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell10003312)) = true := by
  have h : ((childHL (childLL thetaAboveCell10003312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell10003312)) h
theorem e24KC2ThetaAboveLeaf1000331203 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell10003312)) = true := by
  have h : ((childHH (childLL thetaAboveCell10003312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell10003312)) h
theorem e24KC2ThetaAboveLeaf1000331210 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell10003312)) = true := by
  have h : ((childLL (childLH thetaAboveCell10003312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell10003312)) h
theorem e24KC2ThetaAboveLeaf1000331211 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell10003312)) = true := by
  have h : ((childLH (childLH thetaAboveCell10003312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell10003312)) h
theorem e24KC2ThetaAboveLeaf1000331212 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell10003312)) = true := by
  have h : ((childHL (childLH thetaAboveCell10003312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell10003312)) h
theorem e24KC2ThetaAboveLeaf1000331213 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell10003312)) = true := by
  have h : ((childHH (childLH thetaAboveCell10003312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell10003312)) h
theorem e24KC2ThetaAboveLeaf1000331220 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell10003312)) = true := by
  have h : ((childLL (childHL thetaAboveCell10003312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell10003312)) h
theorem e24KC2ThetaAboveLeaf1000331221 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell10003312)) = true := by
  have h : ((childLH (childHL thetaAboveCell10003312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell10003312)) h
theorem e24KC2ThetaAboveLeaf1000331222 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell10003312)) = true := by
  have h : ((childHL (childHL thetaAboveCell10003312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL thetaAboveCell10003312)) h
theorem e24KC2ThetaAboveLeaf1000331223 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell10003312)) = true := by
  have h : ((childHH (childHL thetaAboveCell10003312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL thetaAboveCell10003312)) h
theorem e24KC2ThetaAboveLeaf1000331230 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell10003312)) = true := by
  have h : ((childLL (childHH thetaAboveCell10003312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell10003312)) h
theorem e24KC2ThetaAboveLeaf1000331231 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell10003312)) = true := by
  have h : ((childLH (childHH thetaAboveCell10003312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell10003312)) h
theorem e24KC2ThetaAboveLeaf1000331232 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell10003312)) = true := by
  have h : ((childHL (childHH thetaAboveCell10003312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH thetaAboveCell10003312)) h
theorem e24KC2ThetaAboveLeaf1000331233 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell10003312)) = true := by
  have h : ((childHH (childHH thetaAboveCell10003312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH thetaAboveCell10003312)) h
theorem e24KC2ThetaAboveLeaf1000331300 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell10003313)) = true := by
  have h : ((childLL (childLL thetaAboveCell10003313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell10003313)) h
theorem e24KC2ThetaAboveLeaf1000331301 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell10003313)) = true := by
  have h : ((childLH (childLL thetaAboveCell10003313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell10003313)) h
theorem e24KC2ThetaAboveLeaf1000331302 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell10003313)) = true := by
  have h : ((childHL (childLL thetaAboveCell10003313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell10003313)) h
theorem e24KC2ThetaAboveLeaf1000331303 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell10003313)) = true := by
  have h : ((childHH (childLL thetaAboveCell10003313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell10003313)) h
theorem e24KC2ThetaAboveLeaf1000331310 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell10003313)) = true := by
  have h : ((childLL (childLH thetaAboveCell10003313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell10003313)) h
theorem e24KC2ThetaAboveLeaf1000331311 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell10003313)) = true := by
  have h : ((childLH (childLH thetaAboveCell10003313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell10003313)) h
theorem e24KC2ThetaAboveLeaf1000331312 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell10003313)) = true := by
  have h : ((childHL (childLH thetaAboveCell10003313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell10003313)) h
theorem e24KC2ThetaAboveLeaf1000331313 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell10003313)) = true := by
  have h : ((childHH (childLH thetaAboveCell10003313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell10003313)) h
theorem e24KC2ThetaAboveLeaf1000331320 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell10003313)) = true := by
  have h : ((childLL (childHL thetaAboveCell10003313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell10003313)) h
theorem e24KC2ThetaAboveLeaf1000331321 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell10003313)) = true := by
  have h : ((childLH (childHL thetaAboveCell10003313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell10003313)) h
theorem e24KC2ThetaAboveLeaf1000331322 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell10003313)) = true := by
  have h : ((childHL (childHL thetaAboveCell10003313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL thetaAboveCell10003313)) h
theorem e24KC2ThetaAboveLeaf1000331323 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell10003313)) = true := by
  have h : ((childHH (childHL thetaAboveCell10003313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL thetaAboveCell10003313)) h
theorem e24KC2ThetaAboveLeaf1000331330 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell10003313)) = true := by
  have h : ((childLL (childHH thetaAboveCell10003313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell10003313)) h
theorem e24KC2ThetaAboveLeaf1000331331 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell10003313)) = true := by
  have h : ((childLH (childHH thetaAboveCell10003313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell10003313)) h
theorem e24KC2ThetaAboveLeaf1000331332 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell10003313)) = true := by
  have h : ((childHL (childHH thetaAboveCell10003313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH thetaAboveCell10003313)) h
theorem e24KC2ThetaAboveLeaf1000331333 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell10003313)) = true := by
  have h : ((childHH (childHH thetaAboveCell10003313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH thetaAboveCell10003313)) h
theorem e24KC2ThetaAboveLeaf100033200 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10003320) = true := by
  have h : ((childLL thetaAboveCell10003320)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell10003320) h
theorem e24KC2ThetaAboveLeaf100033201 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10003320) = true := by
  have h : ((childLH thetaAboveCell10003320)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell10003320) h
theorem e24KC2ThetaAboveLeaf100033202 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10003320) = true := by
  have h : ((childHL thetaAboveCell10003320)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell10003320) h
theorem e24KC2ThetaAboveLeaf100033203 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10003320) = true := by
  have h : ((childHH thetaAboveCell10003320)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell10003320) h
theorem e24KC2ThetaAboveLeaf100033210 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10003321) = true := by
  have h : ((childLL thetaAboveCell10003321)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell10003321) h
theorem e24KC2ThetaAboveLeaf100033211 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10003321) = true := by
  have h : ((childLH thetaAboveCell10003321)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell10003321) h
theorem e24KC2ThetaAboveLeaf100033212 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10003321) = true := by
  have h : ((childHL thetaAboveCell10003321)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell10003321) h
theorem e24KC2ThetaAboveLeaf100033213 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10003321) = true := by
  have h : ((childHH thetaAboveCell10003321)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell10003321) h
theorem e24KC2ThetaAboveLeaf10003322 :
    adaptiveCoverCheck 11 thetaAboveCell10003322 = true := by
  have h : (thetaAboveCell10003322).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell10003322 h
theorem e24KC2ThetaAboveLeaf10003323 :
    adaptiveCoverCheck 11 thetaAboveCell10003323 = true := by
  have h : (thetaAboveCell10003323).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell10003323 h
theorem e24KC2ThetaAboveLeaf100033300 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10003330) = true := by
  have h : ((childLL thetaAboveCell10003330)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell10003330) h
theorem e24KC2ThetaAboveLeaf100033301 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10003330) = true := by
  have h : ((childLH thetaAboveCell10003330)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell10003330) h
theorem e24KC2ThetaAboveLeaf100033302 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10003330) = true := by
  have h : ((childHL thetaAboveCell10003330)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell10003330) h
theorem e24KC2ThetaAboveLeaf100033303 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10003330) = true := by
  have h : ((childHH thetaAboveCell10003330)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell10003330) h
theorem e24KC2ThetaAboveLeaf100033310 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10003331) = true := by
  have h : ((childLL thetaAboveCell10003331)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell10003331) h
theorem e24KC2ThetaAboveLeaf1000333110 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell10003331)) = true := by
  have h : ((childLL (childLH thetaAboveCell10003331))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell10003331)) h
theorem e24KC2ThetaAboveLeaf1000333111 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell10003331)) = true := by
  have h : ((childLH (childLH thetaAboveCell10003331))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell10003331)) h
theorem e24KC2ThetaAboveLeaf1000333112 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell10003331)) = true := by
  have h : ((childHL (childLH thetaAboveCell10003331))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell10003331)) h
theorem e24KC2ThetaAboveLeaf1000333113 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell10003331)) = true := by
  have h : ((childHH (childLH thetaAboveCell10003331))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell10003331)) h
theorem e24KC2ThetaAboveLeaf100033312 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10003331) = true := by
  have h : ((childHL thetaAboveCell10003331)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell10003331) h
theorem e24KC2ThetaAboveLeaf100033313 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10003331) = true := by
  have h : ((childHH thetaAboveCell10003331)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell10003331) h
theorem e24KC2ThetaAboveLeaf10003332 :
    adaptiveCoverCheck 11 thetaAboveCell10003332 = true := by
  have h : (thetaAboveCell10003332).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell10003332 h
theorem e24KC2ThetaAboveLeaf10003333 :
    adaptiveCoverCheck 11 thetaAboveCell10003333 = true := by
  have h : (thetaAboveCell10003333).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell10003333 h
theorem e24KC2ThetaAboveLeaf100100 :
    adaptiveCoverCheck 13 (childLL (childLL thetaAboveCell1001)) = true := by
  have h : ((childLL (childLL thetaAboveCell1001))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLL (childLL thetaAboveCell1001)) h
theorem e24KC2ThetaAboveLeaf100101 :
    adaptiveCoverCheck 13 (childLH (childLL thetaAboveCell1001)) = true := by
  have h : ((childLH (childLL thetaAboveCell1001))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLH (childLL thetaAboveCell1001)) h
theorem e24KC2ThetaAboveLeaf100102 :
    adaptiveCoverCheck 13 (childHL (childLL thetaAboveCell1001)) = true := by
  have h : ((childHL (childLL thetaAboveCell1001))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHL (childLL thetaAboveCell1001)) h
theorem e24KC2ThetaAboveLeaf100103 :
    adaptiveCoverCheck 13 (childHH (childLL thetaAboveCell1001)) = true := by
  have h : ((childHH (childLL thetaAboveCell1001))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHH (childLL thetaAboveCell1001)) h
theorem e24KC2ThetaAboveLeaf100110 :
    adaptiveCoverCheck 13 (childLL (childLH thetaAboveCell1001)) = true := by
  have h : ((childLL (childLH thetaAboveCell1001))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLL (childLH thetaAboveCell1001)) h
theorem e24KC2ThetaAboveLeaf100111 :
    adaptiveCoverCheck 13 (childLH (childLH thetaAboveCell1001)) = true := by
  have h : ((childLH (childLH thetaAboveCell1001))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLH (childLH thetaAboveCell1001)) h
theorem e24KC2ThetaAboveLeaf100112 :
    adaptiveCoverCheck 13 (childHL (childLH thetaAboveCell1001)) = true := by
  have h : ((childHL (childLH thetaAboveCell1001))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHL (childLH thetaAboveCell1001)) h
theorem e24KC2ThetaAboveLeaf100113 :
    adaptiveCoverCheck 13 (childHH (childLH thetaAboveCell1001)) = true := by
  have h : ((childHH (childLH thetaAboveCell1001))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHH (childLH thetaAboveCell1001)) h
theorem e24KC2ThetaAboveLeaf1001200 :
    adaptiveCoverCheck 12 (childLL (childLL (childHL thetaAboveCell1001))) = true := by
  have h : ((childLL (childLL (childHL thetaAboveCell1001)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLL (childHL thetaAboveCell1001))) h
theorem e24KC2ThetaAboveLeaf1001201 :
    adaptiveCoverCheck 12 (childLH (childLL (childHL thetaAboveCell1001))) = true := by
  have h : ((childLH (childLL (childHL thetaAboveCell1001)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLL (childHL thetaAboveCell1001))) h
theorem e24KC2ThetaAboveLeaf10012020 :
    adaptiveCoverCheck 11 thetaAboveCell10012020 = true := by
  have h : (thetaAboveCell10012020).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell10012020 h
theorem e24KC2ThetaAboveLeaf10012021 :
    adaptiveCoverCheck 11 thetaAboveCell10012021 = true := by
  have h : (thetaAboveCell10012021).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell10012021 h
theorem e24KC2ThetaAboveLeaf10012022 :
    adaptiveCoverCheck 11 thetaAboveCell10012022 = true := by
  have h : (thetaAboveCell10012022).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell10012022 h
theorem e24KC2ThetaAboveLeaf10012023 :
    adaptiveCoverCheck 11 thetaAboveCell10012023 = true := by
  have h : (thetaAboveCell10012023).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell10012023 h
theorem e24KC2ThetaAboveLeaf10012030 :
    adaptiveCoverCheck 11 thetaAboveCell10012030 = true := by
  have h : (thetaAboveCell10012030).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell10012030 h
theorem e24KC2ThetaAboveLeaf10012031 :
    adaptiveCoverCheck 11 thetaAboveCell10012031 = true := by
  have h : (thetaAboveCell10012031).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell10012031 h
theorem e24KC2ThetaAboveLeaf10012032 :
    adaptiveCoverCheck 11 thetaAboveCell10012032 = true := by
  have h : (thetaAboveCell10012032).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell10012032 h
theorem e24KC2ThetaAboveLeaf10012033 :
    adaptiveCoverCheck 11 thetaAboveCell10012033 = true := by
  have h : (thetaAboveCell10012033).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell10012033 h
theorem e24KC2ThetaAboveLeaf1001210 :
    adaptiveCoverCheck 12 (childLL (childLH (childHL thetaAboveCell1001))) = true := by
  have h : ((childLL (childLH (childHL thetaAboveCell1001)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLH (childHL thetaAboveCell1001))) h
theorem e24KC2ThetaAboveLeaf1001211 :
    adaptiveCoverCheck 12 (childLH (childLH (childHL thetaAboveCell1001))) = true := by
  have h : ((childLH (childLH (childHL thetaAboveCell1001)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLH (childHL thetaAboveCell1001))) h
theorem e24KC2ThetaAboveLeaf10012120 :
    adaptiveCoverCheck 11 thetaAboveCell10012120 = true := by
  have h : (thetaAboveCell10012120).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell10012120 h
theorem e24KC2ThetaAboveLeaf10012121 :
    adaptiveCoverCheck 11 thetaAboveCell10012121 = true := by
  have h : (thetaAboveCell10012121).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell10012121 h
theorem e24KC2ThetaAboveLeaf10012122 :
    adaptiveCoverCheck 11 thetaAboveCell10012122 = true := by
  have h : (thetaAboveCell10012122).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell10012122 h
theorem e24KC2ThetaAboveLeaf10012123 :
    adaptiveCoverCheck 11 thetaAboveCell10012123 = true := by
  have h : (thetaAboveCell10012123).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell10012123 h
theorem e24KC2ThetaAboveLeaf10012130 :
    adaptiveCoverCheck 11 thetaAboveCell10012130 = true := by
  have h : (thetaAboveCell10012130).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell10012130 h
theorem e24KC2ThetaAboveLeaf10012131 :
    adaptiveCoverCheck 11 thetaAboveCell10012131 = true := by
  have h : (thetaAboveCell10012131).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell10012131 h
theorem e24KC2ThetaAboveLeaf10012132 :
    adaptiveCoverCheck 11 thetaAboveCell10012132 = true := by
  have h : (thetaAboveCell10012132).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell10012132 h
theorem e24KC2ThetaAboveLeaf10012133 :
    adaptiveCoverCheck 11 thetaAboveCell10012133 = true := by
  have h : (thetaAboveCell10012133).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell10012133 h
theorem e24KC2ThetaAboveLeaf100122000 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10012200) = true := by
  have h : ((childLL thetaAboveCell10012200)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell10012200) h
theorem e24KC2ThetaAboveLeaf100122001 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10012200) = true := by
  have h : ((childLH thetaAboveCell10012200)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell10012200) h
theorem e24KC2ThetaAboveLeaf100122002 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10012200) = true := by
  have h : ((childHL thetaAboveCell10012200)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell10012200) h
theorem e24KC2ThetaAboveLeaf100122003 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10012200) = true := by
  have h : ((childHH thetaAboveCell10012200)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell10012200) h
theorem e24KC2ThetaAboveLeaf100122010 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10012201) = true := by
  have h : ((childLL thetaAboveCell10012201)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell10012201) h
theorem e24KC2ThetaAboveLeaf100122011 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10012201) = true := by
  have h : ((childLH thetaAboveCell10012201)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell10012201) h
theorem e24KC2ThetaAboveLeaf100122012 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10012201) = true := by
  have h : ((childHL thetaAboveCell10012201)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell10012201) h
theorem e24KC2ThetaAboveLeaf100122013 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10012201) = true := by
  have h : ((childHH thetaAboveCell10012201)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell10012201) h
theorem e24KC2ThetaAboveLeaf1001220200 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell10012202)) = true := by
  have h : ((childLL (childLL thetaAboveCell10012202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell10012202)) h
theorem e24KC2ThetaAboveLeaf1001220201 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell10012202)) = true := by
  have h : ((childLH (childLL thetaAboveCell10012202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell10012202)) h
theorem e24KC2ThetaAboveLeaf1001220202 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell10012202)) = true := by
  have h : ((childHL (childLL thetaAboveCell10012202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell10012202)) h
theorem e24KC2ThetaAboveLeaf1001220203 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell10012202)) = true := by
  have h : ((childHH (childLL thetaAboveCell10012202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell10012202)) h
theorem e24KC2ThetaAboveLeaf1001220210 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell10012202)) = true := by
  have h : ((childLL (childLH thetaAboveCell10012202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell10012202)) h
theorem e24KC2ThetaAboveLeaf1001220211 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell10012202)) = true := by
  have h : ((childLH (childLH thetaAboveCell10012202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell10012202)) h
theorem e24KC2ThetaAboveLeaf1001220212 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell10012202)) = true := by
  have h : ((childHL (childLH thetaAboveCell10012202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell10012202)) h
theorem e24KC2ThetaAboveLeaf1001220213 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell10012202)) = true := by
  have h : ((childHH (childLH thetaAboveCell10012202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell10012202)) h
theorem e24KC2ThetaAboveLeaf1001220220 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell10012202)) = true := by
  have h : ((childLL (childHL thetaAboveCell10012202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell10012202)) h
theorem e24KC2ThetaAboveLeaf1001220221 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell10012202)) = true := by
  have h : ((childLH (childHL thetaAboveCell10012202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell10012202)) h
theorem e24KC2ThetaAboveLeaf1001220222 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell10012202)) = true := by
  have h : ((childHL (childHL thetaAboveCell10012202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL thetaAboveCell10012202)) h
theorem e24KC2ThetaAboveLeaf1001220223 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell10012202)) = true := by
  have h : ((childHH (childHL thetaAboveCell10012202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL thetaAboveCell10012202)) h
theorem e24KC2ThetaAboveLeaf1001220230 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell10012202)) = true := by
  have h : ((childLL (childHH thetaAboveCell10012202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell10012202)) h
theorem e24KC2ThetaAboveLeaf1001220231 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell10012202)) = true := by
  have h : ((childLH (childHH thetaAboveCell10012202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell10012202)) h
theorem e24KC2ThetaAboveLeaf1001220232 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell10012202)) = true := by
  have h : ((childHL (childHH thetaAboveCell10012202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH thetaAboveCell10012202)) h
theorem e24KC2ThetaAboveLeaf1001220233 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell10012202)) = true := by
  have h : ((childHH (childHH thetaAboveCell10012202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH thetaAboveCell10012202)) h
theorem e24KC2ThetaAboveLeaf1001220300 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell10012203)) = true := by
  have h : ((childLL (childLL thetaAboveCell10012203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell10012203)) h
theorem e24KC2ThetaAboveLeaf1001220301 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell10012203)) = true := by
  have h : ((childLH (childLL thetaAboveCell10012203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell10012203)) h
theorem e24KC2ThetaAboveLeaf1001220302 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell10012203)) = true := by
  have h : ((childHL (childLL thetaAboveCell10012203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell10012203)) h
theorem e24KC2ThetaAboveLeaf1001220303 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell10012203)) = true := by
  have h : ((childHH (childLL thetaAboveCell10012203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell10012203)) h
theorem e24KC2ThetaAboveLeaf1001220310 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell10012203)) = true := by
  have h : ((childLL (childLH thetaAboveCell10012203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell10012203)) h
theorem e24KC2ThetaAboveLeaf1001220311 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell10012203)) = true := by
  have h : ((childLH (childLH thetaAboveCell10012203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell10012203)) h
theorem e24KC2ThetaAboveLeaf1001220312 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell10012203)) = true := by
  have h : ((childHL (childLH thetaAboveCell10012203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell10012203)) h
theorem e24KC2ThetaAboveLeaf1001220313 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell10012203)) = true := by
  have h : ((childHH (childLH thetaAboveCell10012203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell10012203)) h
theorem e24KC2ThetaAboveLeaf1001220320 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell10012203)) = true := by
  have h : ((childLL (childHL thetaAboveCell10012203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell10012203)) h
theorem e24KC2ThetaAboveLeaf1001220321 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell10012203)) = true := by
  have h : ((childLH (childHL thetaAboveCell10012203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell10012203)) h
theorem e24KC2ThetaAboveLeaf1001220322 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell10012203)) = true := by
  have h : ((childHL (childHL thetaAboveCell10012203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL thetaAboveCell10012203)) h
theorem e24KC2ThetaAboveLeaf1001220323 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell10012203)) = true := by
  have h : ((childHH (childHL thetaAboveCell10012203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL thetaAboveCell10012203)) h
theorem e24KC2ThetaAboveLeaf1001220330 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell10012203)) = true := by
  have h : ((childLL (childHH thetaAboveCell10012203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell10012203)) h
theorem e24KC2ThetaAboveLeaf1001220331 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell10012203)) = true := by
  have h : ((childLH (childHH thetaAboveCell10012203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell10012203)) h
theorem e24KC2ThetaAboveLeaf1001220332 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell10012203)) = true := by
  have h : ((childHL (childHH thetaAboveCell10012203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH thetaAboveCell10012203)) h
theorem e24KC2ThetaAboveLeaf1001220333 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell10012203)) = true := by
  have h : ((childHH (childHH thetaAboveCell10012203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH thetaAboveCell10012203)) h
theorem e24KC2ThetaAboveLeaf100122100 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10012210) = true := by
  have h : ((childLL thetaAboveCell10012210)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell10012210) h
theorem e24KC2ThetaAboveLeaf100122101 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10012210) = true := by
  have h : ((childLH thetaAboveCell10012210)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell10012210) h
theorem e24KC2ThetaAboveLeaf100122102 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10012210) = true := by
  have h : ((childHL thetaAboveCell10012210)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell10012210) h
theorem e24KC2ThetaAboveLeaf100122103 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10012210) = true := by
  have h : ((childHH thetaAboveCell10012210)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell10012210) h
theorem e24KC2ThetaAboveLeaf100122110 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10012211) = true := by
  have h : ((childLL thetaAboveCell10012211)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell10012211) h
theorem e24KC2ThetaAboveLeaf100122111 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10012211) = true := by
  have h : ((childLH thetaAboveCell10012211)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell10012211) h
theorem e24KC2ThetaAboveLeaf100122112 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10012211) = true := by
  have h : ((childHL thetaAboveCell10012211)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell10012211) h
theorem e24KC2ThetaAboveLeaf100122113 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10012211) = true := by
  have h : ((childHH thetaAboveCell10012211)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell10012211) h
theorem e24KC2ThetaAboveLeaf1001221200 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell10012212)) = true := by
  have h : ((childLL (childLL thetaAboveCell10012212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell10012212)) h
theorem e24KC2ThetaAboveLeaf1001221201 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell10012212)) = true := by
  have h : ((childLH (childLL thetaAboveCell10012212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell10012212)) h
theorem e24KC2ThetaAboveLeaf1001221202 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell10012212)) = true := by
  have h : ((childHL (childLL thetaAboveCell10012212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell10012212)) h
theorem e24KC2ThetaAboveLeaf1001221203 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell10012212)) = true := by
  have h : ((childHH (childLL thetaAboveCell10012212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell10012212)) h
theorem e24KC2ThetaAboveLeaf1001221210 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell10012212)) = true := by
  have h : ((childLL (childLH thetaAboveCell10012212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell10012212)) h
theorem e24KC2ThetaAboveLeaf1001221211 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell10012212)) = true := by
  have h : ((childLH (childLH thetaAboveCell10012212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell10012212)) h
theorem e24KC2ThetaAboveLeaf1001221212 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell10012212)) = true := by
  have h : ((childHL (childLH thetaAboveCell10012212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell10012212)) h
theorem e24KC2ThetaAboveLeaf1001221213 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell10012212)) = true := by
  have h : ((childHH (childLH thetaAboveCell10012212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell10012212)) h
theorem e24KC2ThetaAboveLeaf1001221220 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell10012212)) = true := by
  have h : ((childLL (childHL thetaAboveCell10012212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell10012212)) h
theorem e24KC2ThetaAboveLeaf1001221221 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell10012212)) = true := by
  have h : ((childLH (childHL thetaAboveCell10012212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell10012212)) h
theorem e24KC2ThetaAboveLeaf1001221222 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell10012212)) = true := by
  have h : ((childHL (childHL thetaAboveCell10012212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL thetaAboveCell10012212)) h
theorem e24KC2ThetaAboveLeaf1001221223 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell10012212)) = true := by
  have h : ((childHH (childHL thetaAboveCell10012212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL thetaAboveCell10012212)) h
theorem e24KC2ThetaAboveLeaf1001221230 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell10012212)) = true := by
  have h : ((childLL (childHH thetaAboveCell10012212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell10012212)) h
theorem e24KC2ThetaAboveLeaf1001221231 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell10012212)) = true := by
  have h : ((childLH (childHH thetaAboveCell10012212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell10012212)) h
theorem e24KC2ThetaAboveLeaf1001221232 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell10012212)) = true := by
  have h : ((childHL (childHH thetaAboveCell10012212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH thetaAboveCell10012212)) h
theorem e24KC2ThetaAboveLeaf1001221233 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell10012212)) = true := by
  have h : ((childHH (childHH thetaAboveCell10012212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH thetaAboveCell10012212)) h
theorem e24KC2ThetaAboveLeaf1001221300 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell10012213)) = true := by
  have h : ((childLL (childLL thetaAboveCell10012213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell10012213)) h
theorem e24KC2ThetaAboveLeaf1001221301 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell10012213)) = true := by
  have h : ((childLH (childLL thetaAboveCell10012213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell10012213)) h
theorem e24KC2ThetaAboveLeaf1001221302 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell10012213)) = true := by
  have h : ((childHL (childLL thetaAboveCell10012213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell10012213)) h
theorem e24KC2ThetaAboveLeaf1001221303 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell10012213)) = true := by
  have h : ((childHH (childLL thetaAboveCell10012213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell10012213)) h
theorem e24KC2ThetaAboveLeaf1001221310 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell10012213)) = true := by
  have h : ((childLL (childLH thetaAboveCell10012213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell10012213)) h
theorem e24KC2ThetaAboveLeaf1001221311 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell10012213)) = true := by
  have h : ((childLH (childLH thetaAboveCell10012213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell10012213)) h
theorem e24KC2ThetaAboveLeaf1001221312 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell10012213)) = true := by
  have h : ((childHL (childLH thetaAboveCell10012213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell10012213)) h
theorem e24KC2ThetaAboveLeaf1001221313 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell10012213)) = true := by
  have h : ((childHH (childLH thetaAboveCell10012213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell10012213)) h
theorem e24KC2ThetaAboveLeaf1001221320 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell10012213)) = true := by
  have h : ((childLL (childHL thetaAboveCell10012213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell10012213)) h
theorem e24KC2ThetaAboveLeaf1001221321 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell10012213)) = true := by
  have h : ((childLH (childHL thetaAboveCell10012213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell10012213)) h
theorem e24KC2ThetaAboveLeaf1001221322 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell10012213)) = true := by
  have h : ((childHL (childHL thetaAboveCell10012213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL thetaAboveCell10012213)) h
theorem e24KC2ThetaAboveLeaf1001221323 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell10012213)) = true := by
  have h : ((childHH (childHL thetaAboveCell10012213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL thetaAboveCell10012213)) h
theorem e24KC2ThetaAboveLeaf1001221330 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell10012213)) = true := by
  have h : ((childLL (childHH thetaAboveCell10012213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell10012213)) h
theorem e24KC2ThetaAboveLeaf1001221331 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell10012213)) = true := by
  have h : ((childLH (childHH thetaAboveCell10012213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell10012213)) h
theorem e24KC2ThetaAboveLeaf1001221332 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell10012213)) = true := by
  have h : ((childHL (childHH thetaAboveCell10012213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH thetaAboveCell10012213)) h
theorem e24KC2ThetaAboveLeaf1001221333 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell10012213)) = true := by
  have h : ((childHH (childHH thetaAboveCell10012213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH thetaAboveCell10012213)) h
theorem e24KC2ThetaAboveLeaf1001222000 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell10012220)) = true := by
  have h : ((childLL (childLL thetaAboveCell10012220))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell10012220)) h
theorem e24KC2ThetaAboveLeaf1001222001 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell10012220)) = true := by
  have h : ((childLH (childLL thetaAboveCell10012220))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell10012220)) h
theorem e24KC2ThetaAboveLeaf1001222002 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell10012220)) = true := by
  have h : ((childHL (childLL thetaAboveCell10012220))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell10012220)) h
theorem e24KC2ThetaAboveLeaf1001222003 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell10012220)) = true := by
  have h : ((childHH (childLL thetaAboveCell10012220))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell10012220)) h
theorem e24KC2ThetaAboveLeaf1001222010 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell10012220)) = true := by
  have h : ((childLL (childLH thetaAboveCell10012220))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell10012220)) h
theorem e24KC2ThetaAboveLeaf1001222011 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell10012220)) = true := by
  have h : ((childLH (childLH thetaAboveCell10012220))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell10012220)) h
theorem e24KC2ThetaAboveLeaf1001222012 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell10012220)) = true := by
  have h : ((childHL (childLH thetaAboveCell10012220))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell10012220)) h
theorem e24KC2ThetaAboveLeaf1001222013 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell10012220)) = true := by
  have h : ((childHH (childLH thetaAboveCell10012220))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell10012220)) h
theorem e24KC2ThetaAboveLeaf100122202 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10012220) = true := by
  have h : ((childHL thetaAboveCell10012220)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell10012220) h
theorem e24KC2ThetaAboveLeaf100122203 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10012220) = true := by
  have h : ((childHH thetaAboveCell10012220)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell10012220) h
theorem e24KC2ThetaAboveLeaf1001222100 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell10012221)) = true := by
  have h : ((childLL (childLL thetaAboveCell10012221))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell10012221)) h
theorem e24KC2ThetaAboveLeaf1001222101 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell10012221)) = true := by
  have h : ((childLH (childLL thetaAboveCell10012221))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell10012221)) h
theorem e24KC2ThetaAboveLeaf1001222102 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell10012221)) = true := by
  have h : ((childHL (childLL thetaAboveCell10012221))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell10012221)) h
theorem e24KC2ThetaAboveLeaf1001222103 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell10012221)) = true := by
  have h : ((childHH (childLL thetaAboveCell10012221))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell10012221)) h
theorem e24KC2ThetaAboveLeaf1001222110 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell10012221)) = true := by
  have h : ((childLL (childLH thetaAboveCell10012221))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell10012221)) h
theorem e24KC2ThetaAboveLeaf1001222111 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell10012221)) = true := by
  have h : ((childLH (childLH thetaAboveCell10012221))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell10012221)) h
theorem e24KC2ThetaAboveLeaf1001222112 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell10012221)) = true := by
  have h : ((childHL (childLH thetaAboveCell10012221))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell10012221)) h
theorem e24KC2ThetaAboveLeaf1001222113 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell10012221)) = true := by
  have h : ((childHH (childLH thetaAboveCell10012221))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell10012221)) h
theorem e24KC2ThetaAboveLeaf100122212 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10012221) = true := by
  have h : ((childHL thetaAboveCell10012221)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell10012221) h
theorem e24KC2ThetaAboveLeaf100122213 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10012221) = true := by
  have h : ((childHH thetaAboveCell10012221)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell10012221) h
theorem e24KC2ThetaAboveLeaf10012222 :
    adaptiveCoverCheck 11 thetaAboveCell10012222 = true := by
  have h : (thetaAboveCell10012222).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell10012222 h
theorem e24KC2ThetaAboveLeaf10012223 :
    adaptiveCoverCheck 11 thetaAboveCell10012223 = true := by
  have h : (thetaAboveCell10012223).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell10012223 h
theorem e24KC2ThetaAboveLeaf1001223000 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell10012230)) = true := by
  have h : ((childLL (childLL thetaAboveCell10012230))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell10012230)) h
theorem e24KC2ThetaAboveLeaf1001223001 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell10012230)) = true := by
  have h : ((childLH (childLL thetaAboveCell10012230))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell10012230)) h
theorem e24KC2ThetaAboveLeaf1001223002 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell10012230)) = true := by
  have h : ((childHL (childLL thetaAboveCell10012230))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell10012230)) h
theorem e24KC2ThetaAboveLeaf1001223003 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell10012230)) = true := by
  have h : ((childHH (childLL thetaAboveCell10012230))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell10012230)) h
theorem e24KC2ThetaAboveLeaf1001223010 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell10012230)) = true := by
  have h : ((childLL (childLH thetaAboveCell10012230))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell10012230)) h
theorem e24KC2ThetaAboveLeaf1001223011 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell10012230)) = true := by
  have h : ((childLH (childLH thetaAboveCell10012230))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell10012230)) h
theorem e24KC2ThetaAboveLeaf1001223012 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell10012230)) = true := by
  have h : ((childHL (childLH thetaAboveCell10012230))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell10012230)) h
theorem e24KC2ThetaAboveLeaf1001223013 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell10012230)) = true := by
  have h : ((childHH (childLH thetaAboveCell10012230))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell10012230)) h
theorem e24KC2ThetaAboveLeaf100122302 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10012230) = true := by
  have h : ((childHL thetaAboveCell10012230)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell10012230) h
theorem e24KC2ThetaAboveLeaf100122303 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10012230) = true := by
  have h : ((childHH thetaAboveCell10012230)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell10012230) h
theorem e24KC2ThetaAboveLeaf1001223100 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell10012231)) = true := by
  have h : ((childLL (childLL thetaAboveCell10012231))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell10012231)) h
theorem e24KC2ThetaAboveLeaf1001223101 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell10012231)) = true := by
  have h : ((childLH (childLL thetaAboveCell10012231))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell10012231)) h
theorem e24KC2ThetaAboveLeaf1001223102 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell10012231)) = true := by
  have h : ((childHL (childLL thetaAboveCell10012231))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell10012231)) h
theorem e24KC2ThetaAboveLeaf1001223103 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell10012231)) = true := by
  have h : ((childHH (childLL thetaAboveCell10012231))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell10012231)) h
theorem e24KC2ThetaAboveLeaf1001223110 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell10012231)) = true := by
  have h : ((childLL (childLH thetaAboveCell10012231))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell10012231)) h
theorem e24KC2ThetaAboveLeaf1001223111 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell10012231)) = true := by
  have h : ((childLH (childLH thetaAboveCell10012231))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell10012231)) h
theorem e24KC2ThetaAboveLeaf1001223112 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell10012231)) = true := by
  have h : ((childHL (childLH thetaAboveCell10012231))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell10012231)) h
theorem e24KC2ThetaAboveLeaf1001223113 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell10012231)) = true := by
  have h : ((childHH (childLH thetaAboveCell10012231))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell10012231)) h
theorem e24KC2ThetaAboveLeaf100122312 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10012231) = true := by
  have h : ((childHL thetaAboveCell10012231)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell10012231) h
theorem e24KC2ThetaAboveLeaf100122313 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10012231) = true := by
  have h : ((childHH thetaAboveCell10012231)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell10012231) h
theorem e24KC2ThetaAboveLeaf10012232 :
    adaptiveCoverCheck 11 thetaAboveCell10012232 = true := by
  have h : (thetaAboveCell10012232).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell10012232 h
theorem e24KC2ThetaAboveLeaf10012233 :
    adaptiveCoverCheck 11 thetaAboveCell10012233 = true := by
  have h : (thetaAboveCell10012233).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell10012233 h
theorem e24KC2ThetaAboveLeaf100123000 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10012300) = true := by
  have h : ((childLL thetaAboveCell10012300)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell10012300) h
theorem e24KC2ThetaAboveLeaf100123001 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10012300) = true := by
  have h : ((childLH thetaAboveCell10012300)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell10012300) h
theorem e24KC2ThetaAboveLeaf100123002 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10012300) = true := by
  have h : ((childHL thetaAboveCell10012300)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell10012300) h
theorem e24KC2ThetaAboveLeaf100123003 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10012300) = true := by
  have h : ((childHH thetaAboveCell10012300)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell10012300) h
theorem e24KC2ThetaAboveLeaf100123010 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10012301) = true := by
  have h : ((childLL thetaAboveCell10012301)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell10012301) h
theorem e24KC2ThetaAboveLeaf100123011 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10012301) = true := by
  have h : ((childLH thetaAboveCell10012301)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell10012301) h
theorem e24KC2ThetaAboveLeaf100123012 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10012301) = true := by
  have h : ((childHL thetaAboveCell10012301)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell10012301) h
theorem e24KC2ThetaAboveLeaf100123013 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10012301) = true := by
  have h : ((childHH thetaAboveCell10012301)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell10012301) h
theorem e24KC2ThetaAboveLeaf1001230200 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell10012302)) = true := by
  have h : ((childLL (childLL thetaAboveCell10012302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell10012302)) h
theorem e24KC2ThetaAboveLeaf1001230201 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell10012302)) = true := by
  have h : ((childLH (childLL thetaAboveCell10012302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell10012302)) h
theorem e24KC2ThetaAboveLeaf1001230202 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell10012302)) = true := by
  have h : ((childHL (childLL thetaAboveCell10012302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell10012302)) h
theorem e24KC2ThetaAboveLeaf1001230203 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell10012302)) = true := by
  have h : ((childHH (childLL thetaAboveCell10012302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell10012302)) h
theorem e24KC2ThetaAboveLeaf1001230210 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell10012302)) = true := by
  have h : ((childLL (childLH thetaAboveCell10012302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell10012302)) h
theorem e24KC2ThetaAboveLeaf1001230211 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell10012302)) = true := by
  have h : ((childLH (childLH thetaAboveCell10012302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell10012302)) h
theorem e24KC2ThetaAboveLeaf1001230212 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell10012302)) = true := by
  have h : ((childHL (childLH thetaAboveCell10012302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell10012302)) h
theorem e24KC2ThetaAboveLeaf1001230213 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell10012302)) = true := by
  have h : ((childHH (childLH thetaAboveCell10012302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell10012302)) h
theorem e24KC2ThetaAboveLeaf1001230220 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell10012302)) = true := by
  have h : ((childLL (childHL thetaAboveCell10012302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell10012302)) h
theorem e24KC2ThetaAboveLeaf1001230221 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell10012302)) = true := by
  have h : ((childLH (childHL thetaAboveCell10012302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell10012302)) h
theorem e24KC2ThetaAboveLeaf1001230222 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell10012302)) = true := by
  have h : ((childHL (childHL thetaAboveCell10012302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL thetaAboveCell10012302)) h
theorem e24KC2ThetaAboveLeaf1001230223 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell10012302)) = true := by
  have h : ((childHH (childHL thetaAboveCell10012302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL thetaAboveCell10012302)) h
theorem e24KC2ThetaAboveLeaf1001230230 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell10012302)) = true := by
  have h : ((childLL (childHH thetaAboveCell10012302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell10012302)) h
theorem e24KC2ThetaAboveLeaf1001230231 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell10012302)) = true := by
  have h : ((childLH (childHH thetaAboveCell10012302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell10012302)) h
theorem e24KC2ThetaAboveLeaf1001230232 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell10012302)) = true := by
  have h : ((childHL (childHH thetaAboveCell10012302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH thetaAboveCell10012302)) h
theorem e24KC2ThetaAboveLeaf1001230233 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell10012302)) = true := by
  have h : ((childHH (childHH thetaAboveCell10012302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH thetaAboveCell10012302)) h
theorem e24KC2ThetaAboveLeaf1001230300 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell10012303)) = true := by
  have h : ((childLL (childLL thetaAboveCell10012303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell10012303)) h
theorem e24KC2ThetaAboveLeaf1001230301 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell10012303)) = true := by
  have h : ((childLH (childLL thetaAboveCell10012303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell10012303)) h
theorem e24KC2ThetaAboveLeaf1001230302 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell10012303)) = true := by
  have h : ((childHL (childLL thetaAboveCell10012303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell10012303)) h
theorem e24KC2ThetaAboveLeaf1001230303 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell10012303)) = true := by
  have h : ((childHH (childLL thetaAboveCell10012303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell10012303)) h
theorem e24KC2ThetaAboveLeaf1001230310 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell10012303)) = true := by
  have h : ((childLL (childLH thetaAboveCell10012303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell10012303)) h
theorem e24KC2ThetaAboveLeaf1001230311 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell10012303)) = true := by
  have h : ((childLH (childLH thetaAboveCell10012303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell10012303)) h
theorem e24KC2ThetaAboveLeaf1001230312 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell10012303)) = true := by
  have h : ((childHL (childLH thetaAboveCell10012303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell10012303)) h
theorem e24KC2ThetaAboveLeaf1001230313 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell10012303)) = true := by
  have h : ((childHH (childLH thetaAboveCell10012303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell10012303)) h
theorem e24KC2ThetaAboveLeaf1001230320 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell10012303)) = true := by
  have h : ((childLL (childHL thetaAboveCell10012303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell10012303)) h
theorem e24KC2ThetaAboveLeaf1001230321 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell10012303)) = true := by
  have h : ((childLH (childHL thetaAboveCell10012303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell10012303)) h
theorem e24KC2ThetaAboveLeaf1001230322 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell10012303)) = true := by
  have h : ((childHL (childHL thetaAboveCell10012303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL thetaAboveCell10012303)) h
theorem e24KC2ThetaAboveLeaf1001230323 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell10012303)) = true := by
  have h : ((childHH (childHL thetaAboveCell10012303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL thetaAboveCell10012303)) h
theorem e24KC2ThetaAboveLeaf1001230330 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell10012303)) = true := by
  have h : ((childLL (childHH thetaAboveCell10012303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell10012303)) h
theorem e24KC2ThetaAboveLeaf1001230331 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell10012303)) = true := by
  have h : ((childLH (childHH thetaAboveCell10012303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell10012303)) h
theorem e24KC2ThetaAboveLeaf1001230332 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell10012303)) = true := by
  have h : ((childHL (childHH thetaAboveCell10012303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH thetaAboveCell10012303)) h
theorem e24KC2ThetaAboveLeaf1001230333 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell10012303)) = true := by
  have h : ((childHH (childHH thetaAboveCell10012303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH thetaAboveCell10012303)) h
theorem e24KC2ThetaAboveLeaf100123100 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10012310) = true := by
  have h : ((childLL thetaAboveCell10012310)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell10012310) h
theorem e24KC2ThetaAboveLeaf100123101 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10012310) = true := by
  have h : ((childLH thetaAboveCell10012310)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell10012310) h
theorem e24KC2ThetaAboveLeaf100123102 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10012310) = true := by
  have h : ((childHL thetaAboveCell10012310)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell10012310) h
theorem e24KC2ThetaAboveLeaf100123103 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10012310) = true := by
  have h : ((childHH thetaAboveCell10012310)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell10012310) h
theorem e24KC2ThetaAboveLeaf100123110 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10012311) = true := by
  have h : ((childLL thetaAboveCell10012311)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell10012311) h
theorem e24KC2ThetaAboveLeaf100123111 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10012311) = true := by
  have h : ((childLH thetaAboveCell10012311)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell10012311) h
theorem e24KC2ThetaAboveLeaf100123112 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10012311) = true := by
  have h : ((childHL thetaAboveCell10012311)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell10012311) h
theorem e24KC2ThetaAboveLeaf100123113 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10012311) = true := by
  have h : ((childHH thetaAboveCell10012311)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell10012311) h
theorem e24KC2ThetaAboveLeaf1001231200 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell10012312)) = true := by
  have h : ((childLL (childLL thetaAboveCell10012312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell10012312)) h
theorem e24KC2ThetaAboveLeaf1001231201 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell10012312)) = true := by
  have h : ((childLH (childLL thetaAboveCell10012312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell10012312)) h
theorem e24KC2ThetaAboveLeaf1001231202 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell10012312)) = true := by
  have h : ((childHL (childLL thetaAboveCell10012312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell10012312)) h
theorem e24KC2ThetaAboveLeaf1001231203 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell10012312)) = true := by
  have h : ((childHH (childLL thetaAboveCell10012312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell10012312)) h
theorem e24KC2ThetaAboveLeaf1001231210 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell10012312)) = true := by
  have h : ((childLL (childLH thetaAboveCell10012312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell10012312)) h
theorem e24KC2ThetaAboveLeaf1001231211 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell10012312)) = true := by
  have h : ((childLH (childLH thetaAboveCell10012312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell10012312)) h
theorem e24KC2ThetaAboveLeaf1001231212 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell10012312)) = true := by
  have h : ((childHL (childLH thetaAboveCell10012312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell10012312)) h
theorem e24KC2ThetaAboveLeaf1001231213 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell10012312)) = true := by
  have h : ((childHH (childLH thetaAboveCell10012312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell10012312)) h
theorem e24KC2ThetaAboveLeaf1001231220 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell10012312)) = true := by
  have h : ((childLL (childHL thetaAboveCell10012312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell10012312)) h
theorem e24KC2ThetaAboveLeaf1001231221 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell10012312)) = true := by
  have h : ((childLH (childHL thetaAboveCell10012312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell10012312)) h
theorem e24KC2ThetaAboveLeaf1001231222 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell10012312)) = true := by
  have h : ((childHL (childHL thetaAboveCell10012312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL thetaAboveCell10012312)) h
theorem e24KC2ThetaAboveLeaf1001231223 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell10012312)) = true := by
  have h : ((childHH (childHL thetaAboveCell10012312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL thetaAboveCell10012312)) h
theorem e24KC2ThetaAboveLeaf1001231230 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell10012312)) = true := by
  have h : ((childLL (childHH thetaAboveCell10012312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell10012312)) h
theorem e24KC2ThetaAboveLeaf1001231231 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell10012312)) = true := by
  have h : ((childLH (childHH thetaAboveCell10012312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell10012312)) h
theorem e24KC2ThetaAboveLeaf1001231232 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell10012312)) = true := by
  have h : ((childHL (childHH thetaAboveCell10012312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH thetaAboveCell10012312)) h
theorem e24KC2ThetaAboveLeaf1001231233 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell10012312)) = true := by
  have h : ((childHH (childHH thetaAboveCell10012312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH thetaAboveCell10012312)) h
theorem e24KC2ThetaAboveLeaf1001231300 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell10012313)) = true := by
  have h : ((childLL (childLL thetaAboveCell10012313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell10012313)) h
theorem e24KC2ThetaAboveLeaf1001231301 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell10012313)) = true := by
  have h : ((childLH (childLL thetaAboveCell10012313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell10012313)) h
theorem e24KC2ThetaAboveLeaf1001231302 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell10012313)) = true := by
  have h : ((childHL (childLL thetaAboveCell10012313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell10012313)) h
theorem e24KC2ThetaAboveLeaf1001231303 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell10012313)) = true := by
  have h : ((childHH (childLL thetaAboveCell10012313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell10012313)) h
theorem e24KC2ThetaAboveLeaf1001231310 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell10012313)) = true := by
  have h : ((childLL (childLH thetaAboveCell10012313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell10012313)) h
theorem e24KC2ThetaAboveLeaf1001231311 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell10012313)) = true := by
  have h : ((childLH (childLH thetaAboveCell10012313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell10012313)) h
theorem e24KC2ThetaAboveLeaf1001231312 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell10012313)) = true := by
  have h : ((childHL (childLH thetaAboveCell10012313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell10012313)) h
theorem e24KC2ThetaAboveLeaf1001231313 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell10012313)) = true := by
  have h : ((childHH (childLH thetaAboveCell10012313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell10012313)) h
theorem e24KC2ThetaAboveLeaf1001231320 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell10012313)) = true := by
  have h : ((childLL (childHL thetaAboveCell10012313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell10012313)) h
theorem e24KC2ThetaAboveLeaf1001231321 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell10012313)) = true := by
  have h : ((childLH (childHL thetaAboveCell10012313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell10012313)) h
theorem e24KC2ThetaAboveLeaf1001231322 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell10012313)) = true := by
  have h : ((childHL (childHL thetaAboveCell10012313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL thetaAboveCell10012313)) h
theorem e24KC2ThetaAboveLeaf1001231323 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell10012313)) = true := by
  have h : ((childHH (childHL thetaAboveCell10012313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL thetaAboveCell10012313)) h
theorem e24KC2ThetaAboveLeaf1001231330 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell10012313)) = true := by
  have h : ((childLL (childHH thetaAboveCell10012313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell10012313)) h
theorem e24KC2ThetaAboveLeaf1001231331 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell10012313)) = true := by
  have h : ((childLH (childHH thetaAboveCell10012313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell10012313)) h
theorem e24KC2ThetaAboveLeaf1001231332 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell10012313)) = true := by
  have h : ((childHL (childHH thetaAboveCell10012313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH thetaAboveCell10012313)) h
theorem e24KC2ThetaAboveLeaf1001231333 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell10012313)) = true := by
  have h : ((childHH (childHH thetaAboveCell10012313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH thetaAboveCell10012313)) h
theorem e24KC2ThetaAboveLeaf1001232000 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell10012320)) = true := by
  have h : ((childLL (childLL thetaAboveCell10012320))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell10012320)) h
theorem e24KC2ThetaAboveLeaf1001232001 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell10012320)) = true := by
  have h : ((childLH (childLL thetaAboveCell10012320))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell10012320)) h
theorem e24KC2ThetaAboveLeaf1001232002 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell10012320)) = true := by
  have h : ((childHL (childLL thetaAboveCell10012320))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell10012320)) h
theorem e24KC2ThetaAboveLeaf1001232003 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell10012320)) = true := by
  have h : ((childHH (childLL thetaAboveCell10012320))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell10012320)) h
theorem e24KC2ThetaAboveLeaf1001232010 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell10012320)) = true := by
  have h : ((childLL (childLH thetaAboveCell10012320))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell10012320)) h
theorem e24KC2ThetaAboveLeaf1001232011 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell10012320)) = true := by
  have h : ((childLH (childLH thetaAboveCell10012320))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell10012320)) h
theorem e24KC2ThetaAboveLeaf1001232012 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell10012320)) = true := by
  have h : ((childHL (childLH thetaAboveCell10012320))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell10012320)) h
theorem e24KC2ThetaAboveLeaf1001232013 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell10012320)) = true := by
  have h : ((childHH (childLH thetaAboveCell10012320))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell10012320)) h
theorem e24KC2ThetaAboveLeaf100123202 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10012320) = true := by
  have h : ((childHL thetaAboveCell10012320)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell10012320) h
theorem e24KC2ThetaAboveLeaf100123203 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10012320) = true := by
  have h : ((childHH thetaAboveCell10012320)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell10012320) h
theorem e24KC2ThetaAboveLeaf1001232100 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell10012321)) = true := by
  have h : ((childLL (childLL thetaAboveCell10012321))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell10012321)) h
theorem e24KC2ThetaAboveLeaf1001232101 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell10012321)) = true := by
  have h : ((childLH (childLL thetaAboveCell10012321))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell10012321)) h
theorem e24KC2ThetaAboveLeaf1001232102 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell10012321)) = true := by
  have h : ((childHL (childLL thetaAboveCell10012321))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell10012321)) h
theorem e24KC2ThetaAboveLeaf1001232103 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell10012321)) = true := by
  have h : ((childHH (childLL thetaAboveCell10012321))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell10012321)) h
theorem e24KC2ThetaAboveLeaf1001232110 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell10012321)) = true := by
  have h : ((childLL (childLH thetaAboveCell10012321))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell10012321)) h
theorem e24KC2ThetaAboveLeaf1001232111 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell10012321)) = true := by
  have h : ((childLH (childLH thetaAboveCell10012321))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell10012321)) h
theorem e24KC2ThetaAboveLeaf1001232112 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell10012321)) = true := by
  have h : ((childHL (childLH thetaAboveCell10012321))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell10012321)) h
theorem e24KC2ThetaAboveLeaf1001232113 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell10012321)) = true := by
  have h : ((childHH (childLH thetaAboveCell10012321))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell10012321)) h
theorem e24KC2ThetaAboveLeaf100123212 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10012321) = true := by
  have h : ((childHL thetaAboveCell10012321)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell10012321) h
theorem e24KC2ThetaAboveLeaf100123213 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10012321) = true := by
  have h : ((childHH thetaAboveCell10012321)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell10012321) h
theorem e24KC2ThetaAboveLeaf10012322 :
    adaptiveCoverCheck 11 thetaAboveCell10012322 = true := by
  have h : (thetaAboveCell10012322).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell10012322 h
theorem e24KC2ThetaAboveLeaf10012323 :
    adaptiveCoverCheck 11 thetaAboveCell10012323 = true := by
  have h : (thetaAboveCell10012323).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell10012323 h
theorem e24KC2ThetaAboveLeaf1001233000 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell10012330)) = true := by
  have h : ((childLL (childLL thetaAboveCell10012330))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell10012330)) h
theorem e24KC2ThetaAboveLeaf1001233001 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell10012330)) = true := by
  have h : ((childLH (childLL thetaAboveCell10012330))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell10012330)) h
theorem e24KC2ThetaAboveLeaf1001233002 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell10012330)) = true := by
  have h : ((childHL (childLL thetaAboveCell10012330))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell10012330)) h
theorem e24KC2ThetaAboveLeaf1001233003 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell10012330)) = true := by
  have h : ((childHH (childLL thetaAboveCell10012330))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell10012330)) h
theorem e24KC2ThetaAboveLeaf1001233010 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell10012330)) = true := by
  have h : ((childLL (childLH thetaAboveCell10012330))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell10012330)) h
theorem e24KC2ThetaAboveLeaf1001233011 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell10012330)) = true := by
  have h : ((childLH (childLH thetaAboveCell10012330))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell10012330)) h
theorem e24KC2ThetaAboveLeaf1001233012 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell10012330)) = true := by
  have h : ((childHL (childLH thetaAboveCell10012330))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell10012330)) h
theorem e24KC2ThetaAboveLeaf1001233013 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell10012330)) = true := by
  have h : ((childHH (childLH thetaAboveCell10012330))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell10012330)) h
theorem e24KC2ThetaAboveLeaf100123302 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10012330) = true := by
  have h : ((childHL thetaAboveCell10012330)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell10012330) h
theorem e24KC2ThetaAboveLeaf100123303 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10012330) = true := by
  have h : ((childHH thetaAboveCell10012330)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell10012330) h
theorem e24KC2ThetaAboveLeaf1001233100 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell10012331)) = true := by
  have h : ((childLL (childLL thetaAboveCell10012331))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell10012331)) h
theorem e24KC2ThetaAboveLeaf1001233101 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell10012331)) = true := by
  have h : ((childLH (childLL thetaAboveCell10012331))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell10012331)) h
theorem e24KC2ThetaAboveLeaf1001233102 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell10012331)) = true := by
  have h : ((childHL (childLL thetaAboveCell10012331))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell10012331)) h
theorem e24KC2ThetaAboveLeaf1001233103 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell10012331)) = true := by
  have h : ((childHH (childLL thetaAboveCell10012331))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell10012331)) h
theorem e24KC2ThetaAboveLeaf1001233110 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell10012331)) = true := by
  have h : ((childLL (childLH thetaAboveCell10012331))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell10012331)) h
theorem e24KC2ThetaAboveLeaf1001233111 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell10012331)) = true := by
  have h : ((childLH (childLH thetaAboveCell10012331))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell10012331)) h
theorem e24KC2ThetaAboveLeaf1001233112 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell10012331)) = true := by
  have h : ((childHL (childLH thetaAboveCell10012331))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell10012331)) h
theorem e24KC2ThetaAboveLeaf1001233113 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell10012331)) = true := by
  have h : ((childHH (childLH thetaAboveCell10012331))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell10012331)) h
theorem e24KC2ThetaAboveLeaf100123312 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10012331) = true := by
  have h : ((childHL thetaAboveCell10012331)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell10012331) h
theorem e24KC2ThetaAboveLeaf100123313 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10012331) = true := by
  have h : ((childHH thetaAboveCell10012331)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell10012331) h
theorem e24KC2ThetaAboveLeaf10012332 :
    adaptiveCoverCheck 11 thetaAboveCell10012332 = true := by
  have h : (thetaAboveCell10012332).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell10012332 h
theorem e24KC2ThetaAboveLeaf10012333 :
    adaptiveCoverCheck 11 thetaAboveCell10012333 = true := by
  have h : (thetaAboveCell10012333).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell10012333 h
theorem e24KC2ThetaAboveLeaf1001300 :
    adaptiveCoverCheck 12 (childLL (childLL (childHH thetaAboveCell1001))) = true := by
  have h : ((childLL (childLL (childHH thetaAboveCell1001)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLL (childHH thetaAboveCell1001))) h
theorem e24KC2ThetaAboveLeaf1001301 :
    adaptiveCoverCheck 12 (childLH (childLL (childHH thetaAboveCell1001))) = true := by
  have h : ((childLH (childLL (childHH thetaAboveCell1001)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLL (childHH thetaAboveCell1001))) h
theorem e24KC2ThetaAboveLeaf10013020 :
    adaptiveCoverCheck 11 thetaAboveCell10013020 = true := by
  have h : (thetaAboveCell10013020).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell10013020 h
theorem e24KC2ThetaAboveLeaf10013021 :
    adaptiveCoverCheck 11 thetaAboveCell10013021 = true := by
  have h : (thetaAboveCell10013021).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell10013021 h
theorem e24KC2ThetaAboveLeaf10013022 :
    adaptiveCoverCheck 11 thetaAboveCell10013022 = true := by
  have h : (thetaAboveCell10013022).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell10013022 h
theorem e24KC2ThetaAboveLeaf10013023 :
    adaptiveCoverCheck 11 thetaAboveCell10013023 = true := by
  have h : (thetaAboveCell10013023).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell10013023 h
theorem e24KC2ThetaAboveLeaf10013030 :
    adaptiveCoverCheck 11 thetaAboveCell10013030 = true := by
  have h : (thetaAboveCell10013030).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell10013030 h
theorem e24KC2ThetaAboveLeaf10013031 :
    adaptiveCoverCheck 11 thetaAboveCell10013031 = true := by
  have h : (thetaAboveCell10013031).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell10013031 h
theorem e24KC2ThetaAboveLeaf10013032 :
    adaptiveCoverCheck 11 thetaAboveCell10013032 = true := by
  have h : (thetaAboveCell10013032).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell10013032 h
theorem e24KC2ThetaAboveLeaf10013033 :
    adaptiveCoverCheck 11 thetaAboveCell10013033 = true := by
  have h : (thetaAboveCell10013033).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell10013033 h
theorem e24KC2ThetaAboveLeaf1001310 :
    adaptiveCoverCheck 12 (childLL (childLH (childHH thetaAboveCell1001))) = true := by
  have h : ((childLL (childLH (childHH thetaAboveCell1001)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLH (childHH thetaAboveCell1001))) h
theorem e24KC2ThetaAboveLeaf1001311 :
    adaptiveCoverCheck 12 (childLH (childLH (childHH thetaAboveCell1001))) = true := by
  have h : ((childLH (childLH (childHH thetaAboveCell1001)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLH (childHH thetaAboveCell1001))) h
theorem e24KC2ThetaAboveLeaf10013120 :
    adaptiveCoverCheck 11 thetaAboveCell10013120 = true := by
  have h : (thetaAboveCell10013120).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell10013120 h
theorem e24KC2ThetaAboveLeaf10013121 :
    adaptiveCoverCheck 11 thetaAboveCell10013121 = true := by
  have h : (thetaAboveCell10013121).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell10013121 h
theorem e24KC2ThetaAboveLeaf10013122 :
    adaptiveCoverCheck 11 thetaAboveCell10013122 = true := by
  have h : (thetaAboveCell10013122).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell10013122 h
theorem e24KC2ThetaAboveLeaf10013123 :
    adaptiveCoverCheck 11 thetaAboveCell10013123 = true := by
  have h : (thetaAboveCell10013123).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell10013123 h
theorem e24KC2ThetaAboveLeaf10013130 :
    adaptiveCoverCheck 11 thetaAboveCell10013130 = true := by
  have h : (thetaAboveCell10013130).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell10013130 h
theorem e24KC2ThetaAboveLeaf10013131 :
    adaptiveCoverCheck 11 thetaAboveCell10013131 = true := by
  have h : (thetaAboveCell10013131).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell10013131 h
theorem e24KC2ThetaAboveLeaf10013132 :
    adaptiveCoverCheck 11 thetaAboveCell10013132 = true := by
  have h : (thetaAboveCell10013132).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell10013132 h
theorem e24KC2ThetaAboveLeaf10013133 :
    adaptiveCoverCheck 11 thetaAboveCell10013133 = true := by
  have h : (thetaAboveCell10013133).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell10013133 h
theorem e24KC2ThetaAboveLeaf100132000 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10013200) = true := by
  have h : ((childLL thetaAboveCell10013200)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell10013200) h
theorem e24KC2ThetaAboveLeaf100132001 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10013200) = true := by
  have h : ((childLH thetaAboveCell10013200)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell10013200) h
theorem e24KC2ThetaAboveLeaf100132002 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10013200) = true := by
  have h : ((childHL thetaAboveCell10013200)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell10013200) h
theorem e24KC2ThetaAboveLeaf100132003 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10013200) = true := by
  have h : ((childHH thetaAboveCell10013200)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell10013200) h
theorem e24KC2ThetaAboveLeaf100132010 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10013201) = true := by
  have h : ((childLL thetaAboveCell10013201)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell10013201) h
theorem e24KC2ThetaAboveLeaf100132011 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10013201) = true := by
  have h : ((childLH thetaAboveCell10013201)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell10013201) h
theorem e24KC2ThetaAboveLeaf100132012 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10013201) = true := by
  have h : ((childHL thetaAboveCell10013201)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell10013201) h
theorem e24KC2ThetaAboveLeaf100132013 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10013201) = true := by
  have h : ((childHH thetaAboveCell10013201)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell10013201) h
theorem e24KC2ThetaAboveLeaf1001320200 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell10013202)) = true := by
  have h : ((childLL (childLL thetaAboveCell10013202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell10013202)) h
theorem e24KC2ThetaAboveLeaf1001320201 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell10013202)) = true := by
  have h : ((childLH (childLL thetaAboveCell10013202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell10013202)) h
theorem e24KC2ThetaAboveLeaf1001320202 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell10013202)) = true := by
  have h : ((childHL (childLL thetaAboveCell10013202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell10013202)) h
theorem e24KC2ThetaAboveLeaf1001320203 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell10013202)) = true := by
  have h : ((childHH (childLL thetaAboveCell10013202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell10013202)) h
theorem e24KC2ThetaAboveLeaf1001320210 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell10013202)) = true := by
  have h : ((childLL (childLH thetaAboveCell10013202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell10013202)) h
theorem e24KC2ThetaAboveLeaf1001320211 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell10013202)) = true := by
  have h : ((childLH (childLH thetaAboveCell10013202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell10013202)) h
theorem e24KC2ThetaAboveLeaf1001320212 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell10013202)) = true := by
  have h : ((childHL (childLH thetaAboveCell10013202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell10013202)) h
theorem e24KC2ThetaAboveLeaf1001320213 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell10013202)) = true := by
  have h : ((childHH (childLH thetaAboveCell10013202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell10013202)) h
theorem e24KC2ThetaAboveLeaf1001320220 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell10013202)) = true := by
  have h : ((childLL (childHL thetaAboveCell10013202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell10013202)) h
theorem e24KC2ThetaAboveLeaf1001320221 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell10013202)) = true := by
  have h : ((childLH (childHL thetaAboveCell10013202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell10013202)) h
theorem e24KC2ThetaAboveLeaf1001320222 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell10013202)) = true := by
  have h : ((childHL (childHL thetaAboveCell10013202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL thetaAboveCell10013202)) h
theorem e24KC2ThetaAboveLeaf1001320223 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell10013202)) = true := by
  have h : ((childHH (childHL thetaAboveCell10013202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL thetaAboveCell10013202)) h
theorem e24KC2ThetaAboveLeaf1001320230 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell10013202)) = true := by
  have h : ((childLL (childHH thetaAboveCell10013202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell10013202)) h
theorem e24KC2ThetaAboveLeaf1001320231 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell10013202)) = true := by
  have h : ((childLH (childHH thetaAboveCell10013202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell10013202)) h
theorem e24KC2ThetaAboveLeaf1001320232 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell10013202)) = true := by
  have h : ((childHL (childHH thetaAboveCell10013202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH thetaAboveCell10013202)) h
theorem e24KC2ThetaAboveLeaf1001320233 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell10013202)) = true := by
  have h : ((childHH (childHH thetaAboveCell10013202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH thetaAboveCell10013202)) h
theorem e24KC2ThetaAboveLeaf1001320300 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell10013203)) = true := by
  have h : ((childLL (childLL thetaAboveCell10013203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell10013203)) h
theorem e24KC2ThetaAboveLeaf1001320301 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell10013203)) = true := by
  have h : ((childLH (childLL thetaAboveCell10013203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell10013203)) h
theorem e24KC2ThetaAboveLeaf1001320302 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell10013203)) = true := by
  have h : ((childHL (childLL thetaAboveCell10013203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell10013203)) h
theorem e24KC2ThetaAboveLeaf1001320303 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell10013203)) = true := by
  have h : ((childHH (childLL thetaAboveCell10013203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell10013203)) h
theorem e24KC2ThetaAboveLeaf1001320310 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell10013203)) = true := by
  have h : ((childLL (childLH thetaAboveCell10013203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell10013203)) h
theorem e24KC2ThetaAboveLeaf1001320311 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell10013203)) = true := by
  have h : ((childLH (childLH thetaAboveCell10013203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell10013203)) h
theorem e24KC2ThetaAboveLeaf1001320312 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell10013203)) = true := by
  have h : ((childHL (childLH thetaAboveCell10013203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell10013203)) h

end PartE
end GerverSofa

end

end

end

section

/-! E24KC5 checkpoint-aware kernel batch. -/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells660a83a47d

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells660a83a47d

open CertificateCells660a83a47d
theorem e24KC2ThetaAboveLeaf1001320313 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell10013203)) = true := by
  have h : ((childHH (childLH thetaAboveCell10013203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell10013203)) h
theorem e24KC2ThetaAboveLeaf1001320320 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell10013203)) = true := by
  have h : ((childLL (childHL thetaAboveCell10013203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell10013203)) h
theorem e24KC2ThetaAboveLeaf1001320321 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell10013203)) = true := by
  have h : ((childLH (childHL thetaAboveCell10013203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell10013203)) h
theorem e24KC2ThetaAboveLeaf1001320322 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell10013203)) = true := by
  have h : ((childHL (childHL thetaAboveCell10013203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL thetaAboveCell10013203)) h
theorem e24KC2ThetaAboveLeaf1001320323 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell10013203)) = true := by
  have h : ((childHH (childHL thetaAboveCell10013203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL thetaAboveCell10013203)) h
theorem e24KC2ThetaAboveLeaf1001320330 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell10013203)) = true := by
  have h : ((childLL (childHH thetaAboveCell10013203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell10013203)) h
theorem e24KC2ThetaAboveLeaf1001320331 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell10013203)) = true := by
  have h : ((childLH (childHH thetaAboveCell10013203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell10013203)) h
theorem e24KC2ThetaAboveLeaf1001320332 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell10013203)) = true := by
  have h : ((childHL (childHH thetaAboveCell10013203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH thetaAboveCell10013203)) h
theorem e24KC2ThetaAboveLeaf1001320333 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell10013203)) = true := by
  have h : ((childHH (childHH thetaAboveCell10013203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH thetaAboveCell10013203)) h
theorem e24KC2ThetaAboveLeaf100132100 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10013210) = true := by
  have h : ((childLL thetaAboveCell10013210)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell10013210) h
theorem e24KC2ThetaAboveLeaf100132101 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10013210) = true := by
  have h : ((childLH thetaAboveCell10013210)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell10013210) h
theorem e24KC2ThetaAboveLeaf100132102 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10013210) = true := by
  have h : ((childHL thetaAboveCell10013210)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell10013210) h
theorem e24KC2ThetaAboveLeaf100132103 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10013210) = true := by
  have h : ((childHH thetaAboveCell10013210)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell10013210) h
theorem e24KC2ThetaAboveLeaf100132110 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10013211) = true := by
  have h : ((childLL thetaAboveCell10013211)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell10013211) h
theorem e24KC2ThetaAboveLeaf100132111 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10013211) = true := by
  have h : ((childLH thetaAboveCell10013211)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell10013211) h
theorem e24KC2ThetaAboveLeaf100132112 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10013211) = true := by
  have h : ((childHL thetaAboveCell10013211)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell10013211) h
theorem e24KC2ThetaAboveLeaf100132113 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10013211) = true := by
  have h : ((childHH thetaAboveCell10013211)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell10013211) h
theorem e24KC2ThetaAboveLeaf1001321200 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell10013212)) = true := by
  have h : ((childLL (childLL thetaAboveCell10013212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell10013212)) h
theorem e24KC2ThetaAboveLeaf1001321201 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell10013212)) = true := by
  have h : ((childLH (childLL thetaAboveCell10013212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell10013212)) h
theorem e24KC2ThetaAboveLeaf1001321202 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell10013212)) = true := by
  have h : ((childHL (childLL thetaAboveCell10013212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell10013212)) h
theorem e24KC2ThetaAboveLeaf1001321203 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell10013212)) = true := by
  have h : ((childHH (childLL thetaAboveCell10013212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell10013212)) h
theorem e24KC2ThetaAboveLeaf1001321210 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell10013212)) = true := by
  have h : ((childLL (childLH thetaAboveCell10013212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell10013212)) h
theorem e24KC2ThetaAboveLeaf1001321211 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell10013212)) = true := by
  have h : ((childLH (childLH thetaAboveCell10013212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell10013212)) h
theorem e24KC2ThetaAboveLeaf1001321212 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell10013212)) = true := by
  have h : ((childHL (childLH thetaAboveCell10013212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell10013212)) h
theorem e24KC2ThetaAboveLeaf1001321213 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell10013212)) = true := by
  have h : ((childHH (childLH thetaAboveCell10013212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell10013212)) h
theorem e24KC2ThetaAboveLeaf1001321220 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell10013212)) = true := by
  have h : ((childLL (childHL thetaAboveCell10013212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell10013212)) h
theorem e24KC2ThetaAboveLeaf1001321221 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell10013212)) = true := by
  have h : ((childLH (childHL thetaAboveCell10013212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell10013212)) h
theorem e24KC2ThetaAboveLeaf1001321222 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell10013212)) = true := by
  have h : ((childHL (childHL thetaAboveCell10013212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL thetaAboveCell10013212)) h
theorem e24KC2ThetaAboveLeaf1001321223 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell10013212)) = true := by
  have h : ((childHH (childHL thetaAboveCell10013212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL thetaAboveCell10013212)) h
theorem e24KC2ThetaAboveLeaf1001321230 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell10013212)) = true := by
  have h : ((childLL (childHH thetaAboveCell10013212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell10013212)) h
theorem e24KC2ThetaAboveLeaf1001321231 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell10013212)) = true := by
  have h : ((childLH (childHH thetaAboveCell10013212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell10013212)) h
theorem e24KC2ThetaAboveLeaf1001321232 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell10013212)) = true := by
  have h : ((childHL (childHH thetaAboveCell10013212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH thetaAboveCell10013212)) h
theorem e24KC2ThetaAboveLeaf1001321233 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell10013212)) = true := by
  have h : ((childHH (childHH thetaAboveCell10013212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH thetaAboveCell10013212)) h
theorem e24KC2ThetaAboveLeaf1001321300 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell10013213)) = true := by
  have h : ((childLL (childLL thetaAboveCell10013213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell10013213)) h
theorem e24KC2ThetaAboveLeaf1001321301 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell10013213)) = true := by
  have h : ((childLH (childLL thetaAboveCell10013213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell10013213)) h
theorem e24KC2ThetaAboveLeaf1001321302 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell10013213)) = true := by
  have h : ((childHL (childLL thetaAboveCell10013213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell10013213)) h
theorem e24KC2ThetaAboveLeaf1001321303 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell10013213)) = true := by
  have h : ((childHH (childLL thetaAboveCell10013213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell10013213)) h
theorem e24KC2ThetaAboveLeaf1001321310 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell10013213)) = true := by
  have h : ((childLL (childLH thetaAboveCell10013213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell10013213)) h
theorem e24KC2ThetaAboveLeaf1001321311 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell10013213)) = true := by
  have h : ((childLH (childLH thetaAboveCell10013213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell10013213)) h
theorem e24KC2ThetaAboveLeaf1001321312 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell10013213)) = true := by
  have h : ((childHL (childLH thetaAboveCell10013213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell10013213)) h
theorem e24KC2ThetaAboveLeaf1001321313 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell10013213)) = true := by
  have h : ((childHH (childLH thetaAboveCell10013213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell10013213)) h
theorem e24KC2ThetaAboveLeaf1001321320 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell10013213)) = true := by
  have h : ((childLL (childHL thetaAboveCell10013213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell10013213)) h
theorem e24KC2ThetaAboveLeaf1001321321 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell10013213)) = true := by
  have h : ((childLH (childHL thetaAboveCell10013213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell10013213)) h
theorem e24KC2ThetaAboveLeaf1001321322 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell10013213)) = true := by
  have h : ((childHL (childHL thetaAboveCell10013213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL thetaAboveCell10013213)) h
theorem e24KC2ThetaAboveLeaf1001321323 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell10013213)) = true := by
  have h : ((childHH (childHL thetaAboveCell10013213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL thetaAboveCell10013213)) h
theorem e24KC2ThetaAboveLeaf1001321330 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell10013213)) = true := by
  have h : ((childLL (childHH thetaAboveCell10013213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell10013213)) h
theorem e24KC2ThetaAboveLeaf1001321331 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell10013213)) = true := by
  have h : ((childLH (childHH thetaAboveCell10013213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell10013213)) h
theorem e24KC2ThetaAboveLeaf1001321332 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell10013213)) = true := by
  have h : ((childHL (childHH thetaAboveCell10013213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH thetaAboveCell10013213)) h
theorem e24KC2ThetaAboveLeaf1001321333 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell10013213)) = true := by
  have h : ((childHH (childHH thetaAboveCell10013213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH thetaAboveCell10013213)) h
theorem e24KC2ThetaAboveLeaf1001322000 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell10013220)) = true := by
  have h : ((childLL (childLL thetaAboveCell10013220))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell10013220)) h
theorem e24KC2ThetaAboveLeaf1001322001 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell10013220)) = true := by
  have h : ((childLH (childLL thetaAboveCell10013220))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell10013220)) h
theorem e24KC2ThetaAboveLeaf1001322002 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell10013220)) = true := by
  have h : ((childHL (childLL thetaAboveCell10013220))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell10013220)) h
theorem e24KC2ThetaAboveLeaf1001322003 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell10013220)) = true := by
  have h : ((childHH (childLL thetaAboveCell10013220))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell10013220)) h
theorem e24KC2ThetaAboveLeaf1001322010 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell10013220)) = true := by
  have h : ((childLL (childLH thetaAboveCell10013220))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell10013220)) h
theorem e24KC2ThetaAboveLeaf1001322011 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell10013220)) = true := by
  have h : ((childLH (childLH thetaAboveCell10013220))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell10013220)) h
theorem e24KC2ThetaAboveLeaf1001322012 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell10013220)) = true := by
  have h : ((childHL (childLH thetaAboveCell10013220))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell10013220)) h
theorem e24KC2ThetaAboveLeaf1001322013 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell10013220)) = true := by
  have h : ((childHH (childLH thetaAboveCell10013220))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell10013220)) h
theorem e24KC2ThetaAboveLeaf100132202 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10013220) = true := by
  have h : ((childHL thetaAboveCell10013220)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell10013220) h
theorem e24KC2ThetaAboveLeaf100132203 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10013220) = true := by
  have h : ((childHH thetaAboveCell10013220)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell10013220) h
theorem e24KC2ThetaAboveLeaf1001322100 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell10013221)) = true := by
  have h : ((childLL (childLL thetaAboveCell10013221))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell10013221)) h
theorem e24KC2ThetaAboveLeaf1001322101 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell10013221)) = true := by
  have h : ((childLH (childLL thetaAboveCell10013221))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell10013221)) h
theorem e24KC2ThetaAboveLeaf1001322102 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell10013221)) = true := by
  have h : ((childHL (childLL thetaAboveCell10013221))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell10013221)) h
theorem e24KC2ThetaAboveLeaf1001322103 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell10013221)) = true := by
  have h : ((childHH (childLL thetaAboveCell10013221))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell10013221)) h
theorem e24KC2ThetaAboveLeaf1001322110 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell10013221)) = true := by
  have h : ((childLL (childLH thetaAboveCell10013221))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell10013221)) h
theorem e24KC2ThetaAboveLeaf1001322111 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell10013221)) = true := by
  have h : ((childLH (childLH thetaAboveCell10013221))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell10013221)) h
theorem e24KC2ThetaAboveLeaf1001322112 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell10013221)) = true := by
  have h : ((childHL (childLH thetaAboveCell10013221))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell10013221)) h
theorem e24KC2ThetaAboveLeaf1001322113 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell10013221)) = true := by
  have h : ((childHH (childLH thetaAboveCell10013221))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell10013221)) h
theorem e24KC2ThetaAboveLeaf100132212 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10013221) = true := by
  have h : ((childHL thetaAboveCell10013221)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell10013221) h
theorem e24KC2ThetaAboveLeaf100132213 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10013221) = true := by
  have h : ((childHH thetaAboveCell10013221)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell10013221) h
theorem e24KC2ThetaAboveLeaf10013222 :
    adaptiveCoverCheck 11 thetaAboveCell10013222 = true := by
  have h : (thetaAboveCell10013222).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell10013222 h
theorem e24KC2ThetaAboveLeaf10013223 :
    adaptiveCoverCheck 11 thetaAboveCell10013223 = true := by
  have h : (thetaAboveCell10013223).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell10013223 h
theorem e24KC2ThetaAboveLeaf1001323000 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell10013230)) = true := by
  have h : ((childLL (childLL thetaAboveCell10013230))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell10013230)) h
theorem e24KC2ThetaAboveLeaf1001323001 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell10013230)) = true := by
  have h : ((childLH (childLL thetaAboveCell10013230))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell10013230)) h
theorem e24KC2ThetaAboveLeaf1001323002 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell10013230)) = true := by
  have h : ((childHL (childLL thetaAboveCell10013230))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell10013230)) h
theorem e24KC2ThetaAboveLeaf1001323003 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell10013230)) = true := by
  have h : ((childHH (childLL thetaAboveCell10013230))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell10013230)) h
theorem e24KC2ThetaAboveLeaf1001323010 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell10013230)) = true := by
  have h : ((childLL (childLH thetaAboveCell10013230))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell10013230)) h
theorem e24KC2ThetaAboveLeaf1001323011 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell10013230)) = true := by
  have h : ((childLH (childLH thetaAboveCell10013230))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell10013230)) h
theorem e24KC2ThetaAboveLeaf1001323012 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell10013230)) = true := by
  have h : ((childHL (childLH thetaAboveCell10013230))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell10013230)) h
theorem e24KC2ThetaAboveLeaf1001323013 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell10013230)) = true := by
  have h : ((childHH (childLH thetaAboveCell10013230))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell10013230)) h
theorem e24KC2ThetaAboveLeaf100132302 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10013230) = true := by
  have h : ((childHL thetaAboveCell10013230)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell10013230) h
theorem e24KC2ThetaAboveLeaf100132303 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10013230) = true := by
  have h : ((childHH thetaAboveCell10013230)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell10013230) h
theorem e24KC2ThetaAboveLeaf100132310 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10013231) = true := by
  have h : ((childLL thetaAboveCell10013231)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell10013231) h
theorem e24KC2ThetaAboveLeaf100132311 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10013231) = true := by
  have h : ((childLH thetaAboveCell10013231)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell10013231) h
theorem e24KC2ThetaAboveLeaf100132312 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10013231) = true := by
  have h : ((childHL thetaAboveCell10013231)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell10013231) h
theorem e24KC2ThetaAboveLeaf100132313 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10013231) = true := by
  have h : ((childHH thetaAboveCell10013231)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell10013231) h
theorem e24KC2ThetaAboveLeaf10013232 :
    adaptiveCoverCheck 11 thetaAboveCell10013232 = true := by
  have h : (thetaAboveCell10013232).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell10013232 h
theorem e24KC2ThetaAboveLeaf10013233 :
    adaptiveCoverCheck 11 thetaAboveCell10013233 = true := by
  have h : (thetaAboveCell10013233).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell10013233 h
theorem e24KC2ThetaAboveLeaf100133000 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10013300) = true := by
  have h : ((childLL thetaAboveCell10013300)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell10013300) h
theorem e24KC2ThetaAboveLeaf100133001 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10013300) = true := by
  have h : ((childLH thetaAboveCell10013300)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell10013300) h
theorem e24KC2ThetaAboveLeaf100133002 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10013300) = true := by
  have h : ((childHL thetaAboveCell10013300)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell10013300) h
theorem e24KC2ThetaAboveLeaf100133003 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10013300) = true := by
  have h : ((childHH thetaAboveCell10013300)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell10013300) h
theorem e24KC2ThetaAboveLeaf100133010 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10013301) = true := by
  have h : ((childLL thetaAboveCell10013301)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell10013301) h
theorem e24KC2ThetaAboveLeaf100133011 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10013301) = true := by
  have h : ((childLH thetaAboveCell10013301)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell10013301) h
theorem e24KC2ThetaAboveLeaf100133012 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10013301) = true := by
  have h : ((childHL thetaAboveCell10013301)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell10013301) h
theorem e24KC2ThetaAboveLeaf100133013 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10013301) = true := by
  have h : ((childHH thetaAboveCell10013301)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell10013301) h
theorem e24KC2ThetaAboveLeaf1001330200 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell10013302)) = true := by
  have h : ((childLL (childLL thetaAboveCell10013302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell10013302)) h
theorem e24KC2ThetaAboveLeaf1001330201 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell10013302)) = true := by
  have h : ((childLH (childLL thetaAboveCell10013302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell10013302)) h
theorem e24KC2ThetaAboveLeaf1001330202 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell10013302)) = true := by
  have h : ((childHL (childLL thetaAboveCell10013302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell10013302)) h
theorem e24KC2ThetaAboveLeaf1001330203 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell10013302)) = true := by
  have h : ((childHH (childLL thetaAboveCell10013302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell10013302)) h
theorem e24KC2ThetaAboveLeaf1001330210 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell10013302)) = true := by
  have h : ((childLL (childLH thetaAboveCell10013302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell10013302)) h
theorem e24KC2ThetaAboveLeaf1001330211 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell10013302)) = true := by
  have h : ((childLH (childLH thetaAboveCell10013302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell10013302)) h
theorem e24KC2ThetaAboveLeaf1001330212 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell10013302)) = true := by
  have h : ((childHL (childLH thetaAboveCell10013302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell10013302)) h
theorem e24KC2ThetaAboveLeaf1001330213 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell10013302)) = true := by
  have h : ((childHH (childLH thetaAboveCell10013302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell10013302)) h
theorem e24KC2ThetaAboveLeaf1001330220 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell10013302)) = true := by
  have h : ((childLL (childHL thetaAboveCell10013302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell10013302)) h
theorem e24KC2ThetaAboveLeaf1001330221 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell10013302)) = true := by
  have h : ((childLH (childHL thetaAboveCell10013302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell10013302)) h
theorem e24KC2ThetaAboveLeaf1001330222 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell10013302)) = true := by
  have h : ((childHL (childHL thetaAboveCell10013302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL thetaAboveCell10013302)) h
theorem e24KC2ThetaAboveLeaf1001330223 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell10013302)) = true := by
  have h : ((childHH (childHL thetaAboveCell10013302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL thetaAboveCell10013302)) h
theorem e24KC2ThetaAboveLeaf1001330230 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell10013302)) = true := by
  have h : ((childLL (childHH thetaAboveCell10013302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell10013302)) h
theorem e24KC2ThetaAboveLeaf1001330231 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell10013302)) = true := by
  have h : ((childLH (childHH thetaAboveCell10013302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell10013302)) h
theorem e24KC2ThetaAboveLeaf1001330232 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell10013302)) = true := by
  have h : ((childHL (childHH thetaAboveCell10013302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH thetaAboveCell10013302)) h
theorem e24KC2ThetaAboveLeaf1001330233 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell10013302)) = true := by
  have h : ((childHH (childHH thetaAboveCell10013302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH thetaAboveCell10013302)) h
theorem e24KC2ThetaAboveLeaf1001330300 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell10013303)) = true := by
  have h : ((childLL (childLL thetaAboveCell10013303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell10013303)) h
theorem e24KC2ThetaAboveLeaf1001330301 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell10013303)) = true := by
  have h : ((childLH (childLL thetaAboveCell10013303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell10013303)) h
theorem e24KC2ThetaAboveLeaf1001330302 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell10013303)) = true := by
  have h : ((childHL (childLL thetaAboveCell10013303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell10013303)) h
theorem e24KC2ThetaAboveLeaf1001330303 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell10013303)) = true := by
  have h : ((childHH (childLL thetaAboveCell10013303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell10013303)) h
theorem e24KC2ThetaAboveLeaf1001330310 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell10013303)) = true := by
  have h : ((childLL (childLH thetaAboveCell10013303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell10013303)) h
theorem e24KC2ThetaAboveLeaf1001330311 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell10013303)) = true := by
  have h : ((childLH (childLH thetaAboveCell10013303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell10013303)) h
theorem e24KC2ThetaAboveLeaf1001330312 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell10013303)) = true := by
  have h : ((childHL (childLH thetaAboveCell10013303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell10013303)) h
theorem e24KC2ThetaAboveLeaf1001330313 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell10013303)) = true := by
  have h : ((childHH (childLH thetaAboveCell10013303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell10013303)) h
theorem e24KC2ThetaAboveLeaf1001330320 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell10013303)) = true := by
  have h : ((childLL (childHL thetaAboveCell10013303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell10013303)) h
theorem e24KC2ThetaAboveLeaf1001330321 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell10013303)) = true := by
  have h : ((childLH (childHL thetaAboveCell10013303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell10013303)) h
theorem e24KC2ThetaAboveLeaf1001330322 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell10013303)) = true := by
  have h : ((childHL (childHL thetaAboveCell10013303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL thetaAboveCell10013303)) h
theorem e24KC2ThetaAboveLeaf1001330323 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell10013303)) = true := by
  have h : ((childHH (childHL thetaAboveCell10013303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL thetaAboveCell10013303)) h
theorem e24KC2ThetaAboveLeaf1001330330 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell10013303)) = true := by
  have h : ((childLL (childHH thetaAboveCell10013303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell10013303)) h
theorem e24KC2ThetaAboveLeaf1001330331 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell10013303)) = true := by
  have h : ((childLH (childHH thetaAboveCell10013303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell10013303)) h
theorem e24KC2ThetaAboveLeaf1001330332 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell10013303)) = true := by
  have h : ((childHL (childHH thetaAboveCell10013303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH thetaAboveCell10013303)) h
theorem e24KC2ThetaAboveLeaf1001330333 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell10013303)) = true := by
  have h : ((childHH (childHH thetaAboveCell10013303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH thetaAboveCell10013303)) h
theorem e24KC2ThetaAboveLeaf100133100 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10013310) = true := by
  have h : ((childLL thetaAboveCell10013310)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell10013310) h
theorem e24KC2ThetaAboveLeaf100133101 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10013310) = true := by
  have h : ((childLH thetaAboveCell10013310)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell10013310) h
theorem e24KC2ThetaAboveLeaf100133102 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10013310) = true := by
  have h : ((childHL thetaAboveCell10013310)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell10013310) h
theorem e24KC2ThetaAboveLeaf100133103 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10013310) = true := by
  have h : ((childHH thetaAboveCell10013310)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell10013310) h
theorem e24KC2ThetaAboveLeaf100133110 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10013311) = true := by
  have h : ((childLL thetaAboveCell10013311)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell10013311) h
theorem e24KC2ThetaAboveLeaf100133111 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10013311) = true := by
  have h : ((childLH thetaAboveCell10013311)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell10013311) h
theorem e24KC2ThetaAboveLeaf100133112 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10013311) = true := by
  have h : ((childHL thetaAboveCell10013311)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell10013311) h
theorem e24KC2ThetaAboveLeaf100133113 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10013311) = true := by
  have h : ((childHH thetaAboveCell10013311)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell10013311) h
theorem e24KC2ThetaAboveLeaf1001331200 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell10013312)) = true := by
  have h : ((childLL (childLL thetaAboveCell10013312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell10013312)) h
theorem e24KC2ThetaAboveLeaf1001331201 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell10013312)) = true := by
  have h : ((childLH (childLL thetaAboveCell10013312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell10013312)) h
theorem e24KC2ThetaAboveLeaf1001331202 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell10013312)) = true := by
  have h : ((childHL (childLL thetaAboveCell10013312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell10013312)) h
theorem e24KC2ThetaAboveLeaf1001331203 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell10013312)) = true := by
  have h : ((childHH (childLL thetaAboveCell10013312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell10013312)) h
theorem e24KC2ThetaAboveLeaf1001331210 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell10013312)) = true := by
  have h : ((childLL (childLH thetaAboveCell10013312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell10013312)) h
theorem e24KC2ThetaAboveLeaf1001331211 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell10013312)) = true := by
  have h : ((childLH (childLH thetaAboveCell10013312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell10013312)) h
theorem e24KC2ThetaAboveLeaf1001331212 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell10013312)) = true := by
  have h : ((childHL (childLH thetaAboveCell10013312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell10013312)) h
theorem e24KC2ThetaAboveLeaf1001331213 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell10013312)) = true := by
  have h : ((childHH (childLH thetaAboveCell10013312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell10013312)) h
theorem e24KC2ThetaAboveLeaf1001331220 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell10013312)) = true := by
  have h : ((childLL (childHL thetaAboveCell10013312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell10013312)) h
theorem e24KC2ThetaAboveLeaf1001331221 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell10013312)) = true := by
  have h : ((childLH (childHL thetaAboveCell10013312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell10013312)) h
theorem e24KC2ThetaAboveLeaf1001331222 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell10013312)) = true := by
  have h : ((childHL (childHL thetaAboveCell10013312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL thetaAboveCell10013312)) h
theorem e24KC2ThetaAboveLeaf1001331223 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell10013312)) = true := by
  have h : ((childHH (childHL thetaAboveCell10013312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL thetaAboveCell10013312)) h
theorem e24KC2ThetaAboveLeaf1001331230 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell10013312)) = true := by
  have h : ((childLL (childHH thetaAboveCell10013312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell10013312)) h
theorem e24KC2ThetaAboveLeaf1001331231 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell10013312)) = true := by
  have h : ((childLH (childHH thetaAboveCell10013312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell10013312)) h
theorem e24KC2ThetaAboveLeaf1001331232 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell10013312)) = true := by
  have h : ((childHL (childHH thetaAboveCell10013312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH thetaAboveCell10013312)) h
theorem e24KC2ThetaAboveLeaf1001331233 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell10013312)) = true := by
  have h : ((childHH (childHH thetaAboveCell10013312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH thetaAboveCell10013312)) h
theorem e24KC2ThetaAboveLeaf1001331300 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell10013313)) = true := by
  have h : ((childLL (childLL thetaAboveCell10013313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell10013313)) h
theorem e24KC2ThetaAboveLeaf1001331301 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell10013313)) = true := by
  have h : ((childLH (childLL thetaAboveCell10013313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell10013313)) h
theorem e24KC2ThetaAboveLeaf1001331302 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell10013313)) = true := by
  have h : ((childHL (childLL thetaAboveCell10013313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell10013313)) h
theorem e24KC2ThetaAboveLeaf1001331303 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell10013313)) = true := by
  have h : ((childHH (childLL thetaAboveCell10013313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell10013313)) h
theorem e24KC2ThetaAboveLeaf1001331310 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell10013313)) = true := by
  have h : ((childLL (childLH thetaAboveCell10013313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell10013313)) h
theorem e24KC2ThetaAboveLeaf1001331311 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell10013313)) = true := by
  have h : ((childLH (childLH thetaAboveCell10013313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell10013313)) h
theorem e24KC2ThetaAboveLeaf1001331312 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell10013313)) = true := by
  have h : ((childHL (childLH thetaAboveCell10013313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell10013313)) h
theorem e24KC2ThetaAboveLeaf1001331313 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell10013313)) = true := by
  have h : ((childHH (childLH thetaAboveCell10013313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell10013313)) h
theorem e24KC2ThetaAboveLeaf1001331320 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell10013313)) = true := by
  have h : ((childLL (childHL thetaAboveCell10013313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell10013313)) h
theorem e24KC2ThetaAboveLeaf1001331321 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell10013313)) = true := by
  have h : ((childLH (childHL thetaAboveCell10013313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell10013313)) h
theorem e24KC2ThetaAboveLeaf1001331322 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell10013313)) = true := by
  have h : ((childHL (childHL thetaAboveCell10013313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL thetaAboveCell10013313)) h
theorem e24KC2ThetaAboveLeaf1001331323 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell10013313)) = true := by
  have h : ((childHH (childHL thetaAboveCell10013313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL thetaAboveCell10013313)) h
theorem e24KC2ThetaAboveLeaf1001331330 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell10013313)) = true := by
  have h : ((childLL (childHH thetaAboveCell10013313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell10013313)) h
theorem e24KC2ThetaAboveLeaf1001331331 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell10013313)) = true := by
  have h : ((childLH (childHH thetaAboveCell10013313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell10013313)) h
theorem e24KC2ThetaAboveLeaf1001331332 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell10013313)) = true := by
  have h : ((childHL (childHH thetaAboveCell10013313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH thetaAboveCell10013313)) h
theorem e24KC2ThetaAboveLeaf1001331333 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell10013313)) = true := by
  have h : ((childHH (childHH thetaAboveCell10013313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH thetaAboveCell10013313)) h
theorem e24KC2ThetaAboveLeaf100133200 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10013320) = true := by
  have h : ((childLL thetaAboveCell10013320)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell10013320) h
theorem e24KC2ThetaAboveLeaf100133201 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10013320) = true := by
  have h : ((childLH thetaAboveCell10013320)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell10013320) h
theorem e24KC2ThetaAboveLeaf100133202 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10013320) = true := by
  have h : ((childHL thetaAboveCell10013320)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell10013320) h
theorem e24KC2ThetaAboveLeaf100133203 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10013320) = true := by
  have h : ((childHH thetaAboveCell10013320)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell10013320) h
theorem e24KC2ThetaAboveLeaf100133210 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10013321) = true := by
  have h : ((childLL thetaAboveCell10013321)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell10013321) h
theorem e24KC2ThetaAboveLeaf100133211 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10013321) = true := by
  have h : ((childLH thetaAboveCell10013321)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell10013321) h
theorem e24KC2ThetaAboveLeaf100133212 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10013321) = true := by
  have h : ((childHL thetaAboveCell10013321)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell10013321) h
theorem e24KC2ThetaAboveLeaf100133213 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10013321) = true := by
  have h : ((childHH thetaAboveCell10013321)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell10013321) h
theorem e24KC2ThetaAboveLeaf10013322 :
    adaptiveCoverCheck 11 thetaAboveCell10013322 = true := by
  have h : (thetaAboveCell10013322).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell10013322 h
theorem e24KC2ThetaAboveLeaf10013323 :
    adaptiveCoverCheck 11 thetaAboveCell10013323 = true := by
  have h : (thetaAboveCell10013323).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell10013323 h
theorem e24KC2ThetaAboveLeaf100133300 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10013330) = true := by
  have h : ((childLL thetaAboveCell10013330)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell10013330) h
theorem e24KC2ThetaAboveLeaf100133301 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10013330) = true := by
  have h : ((childLH thetaAboveCell10013330)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell10013330) h
theorem e24KC2ThetaAboveLeaf100133302 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10013330) = true := by
  have h : ((childHL thetaAboveCell10013330)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell10013330) h
theorem e24KC2ThetaAboveLeaf100133303 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10013330) = true := by
  have h : ((childHH thetaAboveCell10013330)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell10013330) h
theorem e24KC2ThetaAboveLeaf100133310 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10013331) = true := by
  have h : ((childLL thetaAboveCell10013331)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell10013331) h
theorem e24KC2ThetaAboveLeaf100133311 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10013331) = true := by
  have h : ((childLH thetaAboveCell10013331)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell10013331) h
theorem e24KC2ThetaAboveLeaf100133312 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10013331) = true := by
  have h : ((childHL thetaAboveCell10013331)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell10013331) h
theorem e24KC2ThetaAboveLeaf100133313 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10013331) = true := by
  have h : ((childHH thetaAboveCell10013331)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell10013331) h
theorem e24KC2ThetaAboveLeaf10013332 :
    adaptiveCoverCheck 11 thetaAboveCell10013332 = true := by
  have h : (thetaAboveCell10013332).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell10013332 h
theorem e24KC2ThetaAboveLeaf10013333 :
    adaptiveCoverCheck 11 thetaAboveCell10013333 = true := by
  have h : (thetaAboveCell10013333).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell10013333 h
theorem e24KC2ThetaAboveLeaf1002000 :
    adaptiveCoverCheck 12 (childLL (childLL (childLL thetaAboveCell1002))) = true := by
  have h : ((childLL (childLL (childLL thetaAboveCell1002)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLL (childLL thetaAboveCell1002))) h
theorem e24KC2ThetaAboveLeaf1002001 :
    adaptiveCoverCheck 12 (childLH (childLL (childLL thetaAboveCell1002))) = true := by
  have h : ((childLH (childLL (childLL thetaAboveCell1002)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLL (childLL thetaAboveCell1002))) h
theorem e24KC2ThetaAboveLeaf1002002 :
    adaptiveCoverCheck 12 (childHL (childLL (childLL thetaAboveCell1002))) = true := by
  have h : ((childHL (childLL (childLL thetaAboveCell1002)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLL (childLL thetaAboveCell1002))) h
theorem e24KC2ThetaAboveLeaf1002003 :
    adaptiveCoverCheck 12 (childHH (childLL (childLL thetaAboveCell1002))) = true := by
  have h : ((childHH (childLL (childLL thetaAboveCell1002)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLL (childLL thetaAboveCell1002))) h
theorem e24KC2ThetaAboveLeaf1002010 :
    adaptiveCoverCheck 12 (childLL (childLH (childLL thetaAboveCell1002))) = true := by
  have h : ((childLL (childLH (childLL thetaAboveCell1002)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLH (childLL thetaAboveCell1002))) h
theorem e24KC2ThetaAboveLeaf1002011 :
    adaptiveCoverCheck 12 (childLH (childLH (childLL thetaAboveCell1002))) = true := by
  have h : ((childLH (childLH (childLL thetaAboveCell1002)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLH (childLL thetaAboveCell1002))) h
theorem e24KC2ThetaAboveLeaf1002012 :
    adaptiveCoverCheck 12 (childHL (childLH (childLL thetaAboveCell1002))) = true := by
  have h : ((childHL (childLH (childLL thetaAboveCell1002)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLH (childLL thetaAboveCell1002))) h
theorem e24KC2ThetaAboveLeaf1002013 :
    adaptiveCoverCheck 12 (childHH (childLH (childLL thetaAboveCell1002))) = true := by
  have h : ((childHH (childLH (childLL thetaAboveCell1002)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLH (childLL thetaAboveCell1002))) h
theorem e24KC2ThetaAboveLeaf100202 :
    adaptiveCoverCheck 13 (childHL (childLL thetaAboveCell1002)) = true := by
  have h : ((childHL (childLL thetaAboveCell1002))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHL (childLL thetaAboveCell1002)) h
theorem e24KC2ThetaAboveLeaf100203 :
    adaptiveCoverCheck 13 (childHH (childLL thetaAboveCell1002)) = true := by
  have h : ((childHH (childLL thetaAboveCell1002))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHH (childLL thetaAboveCell1002)) h
theorem e24KC2ThetaAboveLeaf1002100 :
    adaptiveCoverCheck 12 (childLL (childLL (childLH thetaAboveCell1002))) = true := by
  have h : ((childLL (childLL (childLH thetaAboveCell1002)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLL (childLH thetaAboveCell1002))) h
theorem e24KC2ThetaAboveLeaf1002101 :
    adaptiveCoverCheck 12 (childLH (childLL (childLH thetaAboveCell1002))) = true := by
  have h : ((childLH (childLL (childLH thetaAboveCell1002)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLL (childLH thetaAboveCell1002))) h
theorem e24KC2ThetaAboveLeaf1002102 :
    adaptiveCoverCheck 12 (childHL (childLL (childLH thetaAboveCell1002))) = true := by
  have h : ((childHL (childLL (childLH thetaAboveCell1002)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLL (childLH thetaAboveCell1002))) h
theorem e24KC2ThetaAboveLeaf1002103 :
    adaptiveCoverCheck 12 (childHH (childLL (childLH thetaAboveCell1002))) = true := by
  have h : ((childHH (childLL (childLH thetaAboveCell1002)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLL (childLH thetaAboveCell1002))) h
theorem e24KC2ThetaAboveLeaf1002110 :
    adaptiveCoverCheck 12 (childLL (childLH (childLH thetaAboveCell1002))) = true := by
  have h : ((childLL (childLH (childLH thetaAboveCell1002)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLH (childLH thetaAboveCell1002))) h
theorem e24KC2ThetaAboveLeaf1002111 :
    adaptiveCoverCheck 12 (childLH (childLH (childLH thetaAboveCell1002))) = true := by
  have h : ((childLH (childLH (childLH thetaAboveCell1002)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLH (childLH thetaAboveCell1002))) h
theorem e24KC2ThetaAboveLeaf1002112 :
    adaptiveCoverCheck 12 (childHL (childLH (childLH thetaAboveCell1002))) = true := by
  have h : ((childHL (childLH (childLH thetaAboveCell1002)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLH (childLH thetaAboveCell1002))) h
theorem e24KC2ThetaAboveLeaf1002113 :
    adaptiveCoverCheck 12 (childHH (childLH (childLH thetaAboveCell1002))) = true := by
  have h : ((childHH (childLH (childLH thetaAboveCell1002)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLH (childLH thetaAboveCell1002))) h
theorem e24KC2ThetaAboveLeaf100212 :
    adaptiveCoverCheck 13 (childHL (childLH thetaAboveCell1002)) = true := by
  have h : ((childHL (childLH thetaAboveCell1002))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHL (childLH thetaAboveCell1002)) h
theorem e24KC2ThetaAboveLeaf100213 :
    adaptiveCoverCheck 13 (childHH (childLH thetaAboveCell1002)) = true := by
  have h : ((childHH (childLH thetaAboveCell1002))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHH (childLH thetaAboveCell1002)) h
theorem e24KC2ThetaAboveLeaf10022 :
    adaptiveCoverCheck 14 (childHL thetaAboveCell1002) = true := by
  have h : ((childHL thetaAboveCell1002)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 14 (childHL thetaAboveCell1002) h
theorem e24KC2ThetaAboveLeaf10023 :
    adaptiveCoverCheck 14 (childHH thetaAboveCell1002) = true := by
  have h : ((childHH thetaAboveCell1002)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 14 (childHH thetaAboveCell1002) h
theorem e24KC2ThetaAboveLeaf1003000 :
    adaptiveCoverCheck 12 (childLL (childLL (childLL thetaAboveCell1003))) = true := by
  have h : ((childLL (childLL (childLL thetaAboveCell1003)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLL (childLL thetaAboveCell1003))) h
theorem e24KC2ThetaAboveLeaf1003001 :
    adaptiveCoverCheck 12 (childLH (childLL (childLL thetaAboveCell1003))) = true := by
  have h : ((childLH (childLL (childLL thetaAboveCell1003)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLL (childLL thetaAboveCell1003))) h
theorem e24KC2ThetaAboveLeaf1003002 :
    adaptiveCoverCheck 12 (childHL (childLL (childLL thetaAboveCell1003))) = true := by
  have h : ((childHL (childLL (childLL thetaAboveCell1003)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLL (childLL thetaAboveCell1003))) h
theorem e24KC2ThetaAboveLeaf1003003 :
    adaptiveCoverCheck 12 (childHH (childLL (childLL thetaAboveCell1003))) = true := by
  have h : ((childHH (childLL (childLL thetaAboveCell1003)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLL (childLL thetaAboveCell1003))) h
theorem e24KC2ThetaAboveLeaf1003010 :
    adaptiveCoverCheck 12 (childLL (childLH (childLL thetaAboveCell1003))) = true := by
  have h : ((childLL (childLH (childLL thetaAboveCell1003)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLH (childLL thetaAboveCell1003))) h
theorem e24KC2ThetaAboveLeaf1003011 :
    adaptiveCoverCheck 12 (childLH (childLH (childLL thetaAboveCell1003))) = true := by
  have h : ((childLH (childLH (childLL thetaAboveCell1003)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLH (childLL thetaAboveCell1003))) h
theorem e24KC2ThetaAboveLeaf1003012 :
    adaptiveCoverCheck 12 (childHL (childLH (childLL thetaAboveCell1003))) = true := by
  have h : ((childHL (childLH (childLL thetaAboveCell1003)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLH (childLL thetaAboveCell1003))) h
theorem e24KC2ThetaAboveLeaf1003013 :
    adaptiveCoverCheck 12 (childHH (childLH (childLL thetaAboveCell1003))) = true := by
  have h : ((childHH (childLH (childLL thetaAboveCell1003)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLH (childLL thetaAboveCell1003))) h
theorem e24KC2ThetaAboveLeaf100302 :
    adaptiveCoverCheck 13 (childHL (childLL thetaAboveCell1003)) = true := by
  have h : ((childHL (childLL thetaAboveCell1003))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHL (childLL thetaAboveCell1003)) h
theorem e24KC2ThetaAboveLeaf100303 :
    adaptiveCoverCheck 13 (childHH (childLL thetaAboveCell1003)) = true := by
  have h : ((childHH (childLL thetaAboveCell1003))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHH (childLL thetaAboveCell1003)) h
theorem e24KC2ThetaAboveLeaf1003100 :
    adaptiveCoverCheck 12 (childLL (childLL (childLH thetaAboveCell1003))) = true := by
  have h : ((childLL (childLL (childLH thetaAboveCell1003)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLL (childLH thetaAboveCell1003))) h
theorem e24KC2ThetaAboveLeaf1003101 :
    adaptiveCoverCheck 12 (childLH (childLL (childLH thetaAboveCell1003))) = true := by
  have h : ((childLH (childLL (childLH thetaAboveCell1003)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLL (childLH thetaAboveCell1003))) h
theorem e24KC2ThetaAboveLeaf1003102 :
    adaptiveCoverCheck 12 (childHL (childLL (childLH thetaAboveCell1003))) = true := by
  have h : ((childHL (childLL (childLH thetaAboveCell1003)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLL (childLH thetaAboveCell1003))) h
theorem e24KC2ThetaAboveLeaf1003103 :
    adaptiveCoverCheck 12 (childHH (childLL (childLH thetaAboveCell1003))) = true := by
  have h : ((childHH (childLL (childLH thetaAboveCell1003)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLL (childLH thetaAboveCell1003))) h
theorem e24KC2ThetaAboveLeaf1003110 :
    adaptiveCoverCheck 12 (childLL (childLH (childLH thetaAboveCell1003))) = true := by
  have h : ((childLL (childLH (childLH thetaAboveCell1003)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLH (childLH thetaAboveCell1003))) h
theorem e24KC2ThetaAboveLeaf1003111 :
    adaptiveCoverCheck 12 (childLH (childLH (childLH thetaAboveCell1003))) = true := by
  have h : ((childLH (childLH (childLH thetaAboveCell1003)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLH (childLH thetaAboveCell1003))) h
theorem e24KC2ThetaAboveLeaf1003112 :
    adaptiveCoverCheck 12 (childHL (childLH (childLH thetaAboveCell1003))) = true := by
  have h : ((childHL (childLH (childLH thetaAboveCell1003)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLH (childLH thetaAboveCell1003))) h
theorem e24KC2ThetaAboveLeaf1003113 :
    adaptiveCoverCheck 12 (childHH (childLH (childLH thetaAboveCell1003))) = true := by
  have h : ((childHH (childLH (childLH thetaAboveCell1003)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLH (childLH thetaAboveCell1003))) h
theorem e24KC2ThetaAboveLeaf100312 :
    adaptiveCoverCheck 13 (childHL (childLH thetaAboveCell1003)) = true := by
  have h : ((childHL (childLH thetaAboveCell1003))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHL (childLH thetaAboveCell1003)) h
theorem e24KC2ThetaAboveLeaf100313 :
    adaptiveCoverCheck 13 (childHH (childLH thetaAboveCell1003)) = true := by
  have h : ((childHH (childLH thetaAboveCell1003))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHH (childLH thetaAboveCell1003)) h
theorem e24KC2ThetaAboveLeaf10032 :
    adaptiveCoverCheck 14 (childHL thetaAboveCell1003) = true := by
  have h : ((childHL thetaAboveCell1003)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 14 (childHL thetaAboveCell1003) h
theorem e24KC2ThetaAboveLeaf10033 :
    adaptiveCoverCheck 14 (childHH thetaAboveCell1003) = true := by
  have h : ((childHH thetaAboveCell1003)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 14 (childHH thetaAboveCell1003) h
theorem e24KC2ThetaAboveLeaf101000 :
    adaptiveCoverCheck 13 (childLL (childLL thetaAboveCell1010)) = true := by
  have h : ((childLL (childLL thetaAboveCell1010))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLL (childLL thetaAboveCell1010)) h
theorem e24KC2ThetaAboveLeaf101001 :
    adaptiveCoverCheck 13 (childLH (childLL thetaAboveCell1010)) = true := by
  have h : ((childLH (childLL thetaAboveCell1010))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLH (childLL thetaAboveCell1010)) h
theorem e24KC2ThetaAboveLeaf101002 :
    adaptiveCoverCheck 13 (childHL (childLL thetaAboveCell1010)) = true := by
  have h : ((childHL (childLL thetaAboveCell1010))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHL (childLL thetaAboveCell1010)) h
theorem e24KC2ThetaAboveLeaf101003 :
    adaptiveCoverCheck 13 (childHH (childLL thetaAboveCell1010)) = true := by
  have h : ((childHH (childLL thetaAboveCell1010))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHH (childLL thetaAboveCell1010)) h
theorem e24KC2ThetaAboveLeaf101010 :
    adaptiveCoverCheck 13 (childLL (childLH thetaAboveCell1010)) = true := by
  have h : ((childLL (childLH thetaAboveCell1010))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLL (childLH thetaAboveCell1010)) h
theorem e24KC2ThetaAboveLeaf101011 :
    adaptiveCoverCheck 13 (childLH (childLH thetaAboveCell1010)) = true := by
  have h : ((childLH (childLH thetaAboveCell1010))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLH (childLH thetaAboveCell1010)) h
theorem e24KC2ThetaAboveLeaf101012 :
    adaptiveCoverCheck 13 (childHL (childLH thetaAboveCell1010)) = true := by
  have h : ((childHL (childLH thetaAboveCell1010))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHL (childLH thetaAboveCell1010)) h
theorem e24KC2ThetaAboveLeaf101013 :
    adaptiveCoverCheck 13 (childHH (childLH thetaAboveCell1010)) = true := by
  have h : ((childHH (childLH thetaAboveCell1010))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHH (childLH thetaAboveCell1010)) h
theorem e24KC2ThetaAboveLeaf1010200 :
    adaptiveCoverCheck 12 (childLL (childLL (childHL thetaAboveCell1010))) = true := by
  have h : ((childLL (childLL (childHL thetaAboveCell1010)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLL (childHL thetaAboveCell1010))) h
theorem e24KC2ThetaAboveLeaf1010201 :
    adaptiveCoverCheck 12 (childLH (childLL (childHL thetaAboveCell1010))) = true := by
  have h : ((childLH (childLL (childHL thetaAboveCell1010)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLL (childHL thetaAboveCell1010))) h
theorem e24KC2ThetaAboveLeaf10102020 :
    adaptiveCoverCheck 11 thetaAboveCell10102020 = true := by
  have h : (thetaAboveCell10102020).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell10102020 h
theorem e24KC2ThetaAboveLeaf10102021 :
    adaptiveCoverCheck 11 thetaAboveCell10102021 = true := by
  have h : (thetaAboveCell10102021).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell10102021 h
theorem e24KC2ThetaAboveLeaf10102022 :
    adaptiveCoverCheck 11 thetaAboveCell10102022 = true := by
  have h : (thetaAboveCell10102022).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell10102022 h
theorem e24KC2ThetaAboveLeaf10102023 :
    adaptiveCoverCheck 11 thetaAboveCell10102023 = true := by
  have h : (thetaAboveCell10102023).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell10102023 h
theorem e24KC2ThetaAboveLeaf10102030 :
    adaptiveCoverCheck 11 thetaAboveCell10102030 = true := by
  have h : (thetaAboveCell10102030).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell10102030 h
theorem e24KC2ThetaAboveLeaf10102031 :
    adaptiveCoverCheck 11 thetaAboveCell10102031 = true := by
  have h : (thetaAboveCell10102031).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell10102031 h
theorem e24KC2ThetaAboveLeaf10102032 :
    adaptiveCoverCheck 11 thetaAboveCell10102032 = true := by
  have h : (thetaAboveCell10102032).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell10102032 h
theorem e24KC2ThetaAboveLeaf10102033 :
    adaptiveCoverCheck 11 thetaAboveCell10102033 = true := by
  have h : (thetaAboveCell10102033).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell10102033 h
theorem e24KC2ThetaAboveLeaf1010210 :
    adaptiveCoverCheck 12 (childLL (childLH (childHL thetaAboveCell1010))) = true := by
  have h : ((childLL (childLH (childHL thetaAboveCell1010)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLH (childHL thetaAboveCell1010))) h
theorem e24KC2ThetaAboveLeaf1010211 :
    adaptiveCoverCheck 12 (childLH (childLH (childHL thetaAboveCell1010))) = true := by
  have h : ((childLH (childLH (childHL thetaAboveCell1010)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLH (childHL thetaAboveCell1010))) h
theorem e24KC2ThetaAboveLeaf1010212 :
    adaptiveCoverCheck 12 (childHL (childLH (childHL thetaAboveCell1010))) = true := by
  have h : ((childHL (childLH (childHL thetaAboveCell1010)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLH (childHL thetaAboveCell1010))) h
theorem e24KC2ThetaAboveLeaf1010213 :
    adaptiveCoverCheck 12 (childHH (childLH (childHL thetaAboveCell1010))) = true := by
  have h : ((childHH (childLH (childHL thetaAboveCell1010)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLH (childHL thetaAboveCell1010))) h
theorem e24KC2ThetaAboveLeaf101022000 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10102200) = true := by
  have h : ((childLL thetaAboveCell10102200)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell10102200) h
theorem e24KC2ThetaAboveLeaf101022001 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10102200) = true := by
  have h : ((childLH thetaAboveCell10102200)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell10102200) h
theorem e24KC2ThetaAboveLeaf101022002 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10102200) = true := by
  have h : ((childHL thetaAboveCell10102200)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell10102200) h
theorem e24KC2ThetaAboveLeaf101022003 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10102200) = true := by
  have h : ((childHH thetaAboveCell10102200)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell10102200) h
theorem e24KC2ThetaAboveLeaf101022010 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10102201) = true := by
  have h : ((childLL thetaAboveCell10102201)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell10102201) h
theorem e24KC2ThetaAboveLeaf101022011 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10102201) = true := by
  have h : ((childLH thetaAboveCell10102201)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell10102201) h
theorem e24KC2ThetaAboveLeaf101022012 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10102201) = true := by
  have h : ((childHL thetaAboveCell10102201)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell10102201) h
theorem e24KC2ThetaAboveLeaf101022013 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10102201) = true := by
  have h : ((childHH thetaAboveCell10102201)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell10102201) h
theorem e24KC2ThetaAboveLeaf1010220200 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell10102202)) = true := by
  have h : ((childLL (childLL thetaAboveCell10102202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell10102202)) h
theorem e24KC2ThetaAboveLeaf1010220201 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell10102202)) = true := by
  have h : ((childLH (childLL thetaAboveCell10102202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell10102202)) h
theorem e24KC2ThetaAboveLeaf1010220202 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell10102202)) = true := by
  have h : ((childHL (childLL thetaAboveCell10102202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell10102202)) h
theorem e24KC2ThetaAboveLeaf1010220203 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell10102202)) = true := by
  have h : ((childHH (childLL thetaAboveCell10102202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell10102202)) h
theorem e24KC2ThetaAboveLeaf1010220210 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell10102202)) = true := by
  have h : ((childLL (childLH thetaAboveCell10102202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell10102202)) h
theorem e24KC2ThetaAboveLeaf1010220211 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell10102202)) = true := by
  have h : ((childLH (childLH thetaAboveCell10102202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell10102202)) h
theorem e24KC2ThetaAboveLeaf1010220212 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell10102202)) = true := by
  have h : ((childHL (childLH thetaAboveCell10102202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell10102202)) h
theorem e24KC2ThetaAboveLeaf1010220213 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell10102202)) = true := by
  have h : ((childHH (childLH thetaAboveCell10102202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell10102202)) h
theorem e24KC2ThetaAboveLeaf1010220220 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell10102202)) = true := by
  have h : ((childLL (childHL thetaAboveCell10102202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell10102202)) h
theorem e24KC2ThetaAboveLeaf1010220221 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell10102202)) = true := by
  have h : ((childLH (childHL thetaAboveCell10102202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell10102202)) h
theorem e24KC2ThetaAboveLeaf1010220222 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell10102202)) = true := by
  have h : ((childHL (childHL thetaAboveCell10102202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL thetaAboveCell10102202)) h
theorem e24KC2ThetaAboveLeaf1010220223 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell10102202)) = true := by
  have h : ((childHH (childHL thetaAboveCell10102202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL thetaAboveCell10102202)) h
theorem e24KC2ThetaAboveLeaf1010220230 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell10102202)) = true := by
  have h : ((childLL (childHH thetaAboveCell10102202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell10102202)) h
theorem e24KC2ThetaAboveLeaf1010220231 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell10102202)) = true := by
  have h : ((childLH (childHH thetaAboveCell10102202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell10102202)) h
theorem e24KC2ThetaAboveLeaf1010220232 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell10102202)) = true := by
  have h : ((childHL (childHH thetaAboveCell10102202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH thetaAboveCell10102202)) h
theorem e24KC2ThetaAboveLeaf1010220233 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell10102202)) = true := by
  have h : ((childHH (childHH thetaAboveCell10102202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH thetaAboveCell10102202)) h
theorem e24KC2ThetaAboveLeaf1010220300 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell10102203)) = true := by
  have h : ((childLL (childLL thetaAboveCell10102203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell10102203)) h
theorem e24KC2ThetaAboveLeaf1010220301 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell10102203)) = true := by
  have h : ((childLH (childLL thetaAboveCell10102203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell10102203)) h
theorem e24KC2ThetaAboveLeaf1010220302 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell10102203)) = true := by
  have h : ((childHL (childLL thetaAboveCell10102203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell10102203)) h
theorem e24KC2ThetaAboveLeaf1010220303 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell10102203)) = true := by
  have h : ((childHH (childLL thetaAboveCell10102203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell10102203)) h
theorem e24KC2ThetaAboveLeaf1010220310 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell10102203)) = true := by
  have h : ((childLL (childLH thetaAboveCell10102203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell10102203)) h
theorem e24KC2ThetaAboveLeaf1010220311 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell10102203)) = true := by
  have h : ((childLH (childLH thetaAboveCell10102203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell10102203)) h
theorem e24KC2ThetaAboveLeaf1010220312 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell10102203)) = true := by
  have h : ((childHL (childLH thetaAboveCell10102203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell10102203)) h
theorem e24KC2ThetaAboveLeaf1010220313 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell10102203)) = true := by
  have h : ((childHH (childLH thetaAboveCell10102203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell10102203)) h
theorem e24KC2ThetaAboveLeaf1010220320 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell10102203)) = true := by
  have h : ((childLL (childHL thetaAboveCell10102203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell10102203)) h
theorem e24KC2ThetaAboveLeaf1010220321 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell10102203)) = true := by
  have h : ((childLH (childHL thetaAboveCell10102203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell10102203)) h
theorem e24KC2ThetaAboveLeaf1010220322 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell10102203)) = true := by
  have h : ((childHL (childHL thetaAboveCell10102203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL thetaAboveCell10102203)) h
theorem e24KC2ThetaAboveLeaf1010220323 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell10102203)) = true := by
  have h : ((childHH (childHL thetaAboveCell10102203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL thetaAboveCell10102203)) h
theorem e24KC2ThetaAboveLeaf1010220330 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell10102203)) = true := by
  have h : ((childLL (childHH thetaAboveCell10102203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell10102203)) h
theorem e24KC2ThetaAboveLeaf1010220331 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell10102203)) = true := by
  have h : ((childLH (childHH thetaAboveCell10102203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell10102203)) h
theorem e24KC2ThetaAboveLeaf1010220332 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell10102203)) = true := by
  have h : ((childHL (childHH thetaAboveCell10102203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH thetaAboveCell10102203)) h
theorem e24KC2ThetaAboveLeaf1010220333 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell10102203)) = true := by
  have h : ((childHH (childHH thetaAboveCell10102203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH thetaAboveCell10102203)) h
theorem e24KC2ThetaAboveLeaf101022100 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10102210) = true := by
  have h : ((childLL thetaAboveCell10102210)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell10102210) h
theorem e24KC2ThetaAboveLeaf101022101 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10102210) = true := by
  have h : ((childLH thetaAboveCell10102210)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell10102210) h
theorem e24KC2ThetaAboveLeaf101022102 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10102210) = true := by
  have h : ((childHL thetaAboveCell10102210)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell10102210) h
theorem e24KC2ThetaAboveLeaf101022103 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10102210) = true := by
  have h : ((childHH thetaAboveCell10102210)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell10102210) h
theorem e24KC2ThetaAboveLeaf101022110 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10102211) = true := by
  have h : ((childLL thetaAboveCell10102211)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell10102211) h
theorem e24KC2ThetaAboveLeaf101022111 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10102211) = true := by
  have h : ((childLH thetaAboveCell10102211)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell10102211) h
theorem e24KC2ThetaAboveLeaf101022112 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10102211) = true := by
  have h : ((childHL thetaAboveCell10102211)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell10102211) h
theorem e24KC2ThetaAboveLeaf101022113 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10102211) = true := by
  have h : ((childHH thetaAboveCell10102211)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell10102211) h
theorem e24KC2ThetaAboveLeaf1010221200 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell10102212)) = true := by
  have h : ((childLL (childLL thetaAboveCell10102212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell10102212)) h
theorem e24KC2ThetaAboveLeaf1010221201 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell10102212)) = true := by
  have h : ((childLH (childLL thetaAboveCell10102212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell10102212)) h
theorem e24KC2ThetaAboveLeaf1010221202 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell10102212)) = true := by
  have h : ((childHL (childLL thetaAboveCell10102212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell10102212)) h
theorem e24KC2ThetaAboveLeaf1010221203 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell10102212)) = true := by
  have h : ((childHH (childLL thetaAboveCell10102212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell10102212)) h
theorem e24KC2ThetaAboveLeaf1010221210 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell10102212)) = true := by
  have h : ((childLL (childLH thetaAboveCell10102212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell10102212)) h
theorem e24KC2ThetaAboveLeaf1010221211 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell10102212)) = true := by
  have h : ((childLH (childLH thetaAboveCell10102212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell10102212)) h
theorem e24KC2ThetaAboveLeaf1010221212 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell10102212)) = true := by
  have h : ((childHL (childLH thetaAboveCell10102212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell10102212)) h
theorem e24KC2ThetaAboveLeaf1010221213 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell10102212)) = true := by
  have h : ((childHH (childLH thetaAboveCell10102212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell10102212)) h
theorem e24KC2ThetaAboveLeaf1010221220 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell10102212)) = true := by
  have h : ((childLL (childHL thetaAboveCell10102212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell10102212)) h
theorem e24KC2ThetaAboveLeaf1010221221 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell10102212)) = true := by
  have h : ((childLH (childHL thetaAboveCell10102212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell10102212)) h
theorem e24KC2ThetaAboveLeaf1010221222 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell10102212)) = true := by
  have h : ((childHL (childHL thetaAboveCell10102212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL thetaAboveCell10102212)) h
theorem e24KC2ThetaAboveLeaf1010221223 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell10102212)) = true := by
  have h : ((childHH (childHL thetaAboveCell10102212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL thetaAboveCell10102212)) h
theorem e24KC2ThetaAboveLeaf1010221230 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell10102212)) = true := by
  have h : ((childLL (childHH thetaAboveCell10102212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell10102212)) h
theorem e24KC2ThetaAboveLeaf1010221231 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell10102212)) = true := by
  have h : ((childLH (childHH thetaAboveCell10102212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell10102212)) h
theorem e24KC2ThetaAboveLeaf1010221232 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell10102212)) = true := by
  have h : ((childHL (childHH thetaAboveCell10102212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH thetaAboveCell10102212)) h
theorem e24KC2ThetaAboveLeaf1010221233 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell10102212)) = true := by
  have h : ((childHH (childHH thetaAboveCell10102212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH thetaAboveCell10102212)) h
theorem e24KC2ThetaAboveLeaf1010221300 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell10102213)) = true := by
  have h : ((childLL (childLL thetaAboveCell10102213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell10102213)) h
theorem e24KC2ThetaAboveLeaf1010221301 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell10102213)) = true := by
  have h : ((childLH (childLL thetaAboveCell10102213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell10102213)) h
theorem e24KC2ThetaAboveLeaf1010221302 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell10102213)) = true := by
  have h : ((childHL (childLL thetaAboveCell10102213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell10102213)) h
theorem e24KC2ThetaAboveLeaf1010221303 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell10102213)) = true := by
  have h : ((childHH (childLL thetaAboveCell10102213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell10102213)) h
theorem e24KC2ThetaAboveLeaf1010221310 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell10102213)) = true := by
  have h : ((childLL (childLH thetaAboveCell10102213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell10102213)) h
theorem e24KC2ThetaAboveLeaf1010221311 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell10102213)) = true := by
  have h : ((childLH (childLH thetaAboveCell10102213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell10102213)) h
theorem e24KC2ThetaAboveLeaf1010221312 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell10102213)) = true := by
  have h : ((childHL (childLH thetaAboveCell10102213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell10102213)) h
theorem e24KC2ThetaAboveLeaf1010221313 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell10102213)) = true := by
  have h : ((childHH (childLH thetaAboveCell10102213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell10102213)) h
theorem e24KC2ThetaAboveLeaf1010221320 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell10102213)) = true := by
  have h : ((childLL (childHL thetaAboveCell10102213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell10102213)) h
theorem e24KC2ThetaAboveLeaf1010221321 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell10102213)) = true := by
  have h : ((childLH (childHL thetaAboveCell10102213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell10102213)) h
theorem e24KC2ThetaAboveLeaf1010221322 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell10102213)) = true := by
  have h : ((childHL (childHL thetaAboveCell10102213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL thetaAboveCell10102213)) h
theorem e24KC2ThetaAboveLeaf1010221323 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell10102213)) = true := by
  have h : ((childHH (childHL thetaAboveCell10102213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL thetaAboveCell10102213)) h
theorem e24KC2ThetaAboveLeaf101022133 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10102213) = true := by
  have h : ((childHH thetaAboveCell10102213)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell10102213) h
theorem e24KC2ThetaAboveLeaf101022200 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10102220) = true := by
  have h : ((childLL thetaAboveCell10102220)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell10102220) h
theorem e24KC2ThetaAboveLeaf101022201 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10102220) = true := by
  have h : ((childLH thetaAboveCell10102220)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell10102220) h
theorem e24KC2ThetaAboveLeaf101022202 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10102220) = true := by
  have h : ((childHL thetaAboveCell10102220)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell10102220) h
theorem e24KC2ThetaAboveLeaf101022203 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10102220) = true := by
  have h : ((childHH thetaAboveCell10102220)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell10102220) h
theorem e24KC2ThetaAboveLeaf101022210 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10102221) = true := by
  have h : ((childLL thetaAboveCell10102221)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell10102221) h
theorem e24KC2ThetaAboveLeaf101022211 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10102221) = true := by
  have h : ((childLH thetaAboveCell10102221)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell10102221) h
theorem e24KC2ThetaAboveLeaf101022212 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10102221) = true := by
  have h : ((childHL thetaAboveCell10102221)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell10102221) h
theorem e24KC2ThetaAboveLeaf101022213 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10102221) = true := by
  have h : ((childHH thetaAboveCell10102221)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell10102221) h
theorem e24KC2ThetaAboveLeaf10102222 :
    adaptiveCoverCheck 11 thetaAboveCell10102222 = true := by
  have h : (thetaAboveCell10102222).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell10102222 h
theorem e24KC2ThetaAboveLeaf10102223 :
    adaptiveCoverCheck 11 thetaAboveCell10102223 = true := by
  have h : (thetaAboveCell10102223).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell10102223 h
theorem e24KC2ThetaAboveLeaf101022300 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10102230) = true := by
  have h : ((childLL thetaAboveCell10102230)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell10102230) h
theorem e24KC2ThetaAboveLeaf101022301 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10102230) = true := by
  have h : ((childLH thetaAboveCell10102230)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell10102230) h
theorem e24KC2ThetaAboveLeaf101022302 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10102230) = true := by
  have h : ((childHL thetaAboveCell10102230)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell10102230) h
theorem e24KC2ThetaAboveLeaf101022303 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10102230) = true := by
  have h : ((childHH thetaAboveCell10102230)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell10102230) h
theorem e24KC2ThetaAboveLeaf101022310 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10102231) = true := by
  have h : ((childLL thetaAboveCell10102231)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell10102231) h
theorem e24KC2ThetaAboveLeaf101022311 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10102231) = true := by
  have h : ((childLH thetaAboveCell10102231)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell10102231) h
theorem e24KC2ThetaAboveLeaf101022312 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10102231) = true := by
  have h : ((childHL thetaAboveCell10102231)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell10102231) h
theorem e24KC2ThetaAboveLeaf101022313 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10102231) = true := by
  have h : ((childHH thetaAboveCell10102231)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell10102231) h
theorem e24KC2ThetaAboveLeaf10102232 :
    adaptiveCoverCheck 11 thetaAboveCell10102232 = true := by
  have h : (thetaAboveCell10102232).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell10102232 h
theorem e24KC2ThetaAboveLeaf10102233 :
    adaptiveCoverCheck 11 thetaAboveCell10102233 = true := by
  have h : (thetaAboveCell10102233).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell10102233 h
theorem e24KC2ThetaAboveLeaf101023000 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10102300) = true := by
  have h : ((childLL thetaAboveCell10102300)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell10102300) h
theorem e24KC2ThetaAboveLeaf101023001 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10102300) = true := by
  have h : ((childLH thetaAboveCell10102300)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell10102300) h
theorem e24KC2ThetaAboveLeaf101023002 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10102300) = true := by
  have h : ((childHL thetaAboveCell10102300)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell10102300) h
theorem e24KC2ThetaAboveLeaf101023003 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10102300) = true := by
  have h : ((childHH thetaAboveCell10102300)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell10102300) h
theorem e24KC2ThetaAboveLeaf101023010 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10102301) = true := by
  have h : ((childLL thetaAboveCell10102301)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell10102301) h
theorem e24KC2ThetaAboveLeaf101023011 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10102301) = true := by
  have h : ((childLH thetaAboveCell10102301)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell10102301) h
theorem e24KC2ThetaAboveLeaf101023012 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10102301) = true := by
  have h : ((childHL thetaAboveCell10102301)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell10102301) h
theorem e24KC2ThetaAboveLeaf101023013 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10102301) = true := by
  have h : ((childHH thetaAboveCell10102301)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell10102301) h
theorem e24KC2ThetaAboveLeaf1010230200 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell10102302)) = true := by
  have h : ((childLL (childLL thetaAboveCell10102302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell10102302)) h
theorem e24KC2ThetaAboveLeaf1010230201 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell10102302)) = true := by
  have h : ((childLH (childLL thetaAboveCell10102302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell10102302)) h
theorem e24KC2ThetaAboveLeaf1010230202 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell10102302)) = true := by
  have h : ((childHL (childLL thetaAboveCell10102302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell10102302)) h
theorem e24KC2ThetaAboveLeaf1010230203 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell10102302)) = true := by
  have h : ((childHH (childLL thetaAboveCell10102302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell10102302)) h
theorem e24KC2ThetaAboveLeaf1010230210 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell10102302)) = true := by
  have h : ((childLL (childLH thetaAboveCell10102302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell10102302)) h
theorem e24KC2ThetaAboveLeaf1010230211 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell10102302)) = true := by
  have h : ((childLH (childLH thetaAboveCell10102302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell10102302)) h
theorem e24KC2ThetaAboveLeaf1010230212 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell10102302)) = true := by
  have h : ((childHL (childLH thetaAboveCell10102302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell10102302)) h
theorem e24KC2ThetaAboveLeaf1010230213 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell10102302)) = true := by
  have h : ((childHH (childLH thetaAboveCell10102302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell10102302)) h
theorem e24KC2ThetaAboveLeaf101023022 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10102302) = true := by
  have h : ((childHL thetaAboveCell10102302)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell10102302) h
theorem e24KC2ThetaAboveLeaf101023023 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10102302) = true := by
  have h : ((childHH thetaAboveCell10102302)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell10102302) h
theorem e24KC2ThetaAboveLeaf1010230300 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell10102303)) = true := by
  have h : ((childLL (childLL thetaAboveCell10102303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell10102303)) h
theorem e24KC2ThetaAboveLeaf1010230301 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell10102303)) = true := by
  have h : ((childLH (childLL thetaAboveCell10102303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell10102303)) h
theorem e24KC2ThetaAboveLeaf1010230302 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell10102303)) = true := by
  have h : ((childHL (childLL thetaAboveCell10102303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell10102303)) h
theorem e24KC2ThetaAboveLeaf1010230303 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell10102303)) = true := by
  have h : ((childHH (childLL thetaAboveCell10102303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell10102303)) h
theorem e24KC2ThetaAboveLeaf1010230310 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell10102303)) = true := by
  have h : ((childLL (childLH thetaAboveCell10102303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell10102303)) h
theorem e24KC2ThetaAboveLeaf1010230311 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell10102303)) = true := by
  have h : ((childLH (childLH thetaAboveCell10102303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell10102303)) h
theorem e24KC2ThetaAboveLeaf1010230312 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell10102303)) = true := by
  have h : ((childHL (childLH thetaAboveCell10102303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell10102303)) h
theorem e24KC2ThetaAboveLeaf1010230313 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell10102303)) = true := by
  have h : ((childHH (childLH thetaAboveCell10102303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell10102303)) h
theorem e24KC2ThetaAboveLeaf101023032 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10102303) = true := by
  have h : ((childHL thetaAboveCell10102303)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell10102303) h
theorem e24KC2ThetaAboveLeaf101023033 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10102303) = true := by
  have h : ((childHH thetaAboveCell10102303)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell10102303) h
theorem e24KC2ThetaAboveLeaf101023100 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10102310) = true := by
  have h : ((childLL thetaAboveCell10102310)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell10102310) h
theorem e24KC2ThetaAboveLeaf101023101 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10102310) = true := by
  have h : ((childLH thetaAboveCell10102310)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell10102310) h
theorem e24KC2ThetaAboveLeaf101023102 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10102310) = true := by
  have h : ((childHL thetaAboveCell10102310)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell10102310) h
theorem e24KC2ThetaAboveLeaf101023103 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10102310) = true := by
  have h : ((childHH thetaAboveCell10102310)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell10102310) h
theorem e24KC2ThetaAboveLeaf101023110 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10102311) = true := by
  have h : ((childLL thetaAboveCell10102311)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell10102311) h
theorem e24KC2ThetaAboveLeaf101023111 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10102311) = true := by
  have h : ((childLH thetaAboveCell10102311)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell10102311) h
theorem e24KC2ThetaAboveLeaf101023112 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10102311) = true := by
  have h : ((childHL thetaAboveCell10102311)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell10102311) h
theorem e24KC2ThetaAboveLeaf101023113 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10102311) = true := by
  have h : ((childHH thetaAboveCell10102311)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell10102311) h
theorem e24KC2ThetaAboveLeaf1010231200 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell10102312)) = true := by
  have h : ((childLL (childLL thetaAboveCell10102312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell10102312)) h
theorem e24KC2ThetaAboveLeaf1010231201 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell10102312)) = true := by
  have h : ((childLH (childLL thetaAboveCell10102312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell10102312)) h
theorem e24KC2ThetaAboveLeaf1010231202 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell10102312)) = true := by
  have h : ((childHL (childLL thetaAboveCell10102312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell10102312)) h
theorem e24KC2ThetaAboveLeaf1010231203 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell10102312)) = true := by
  have h : ((childHH (childLL thetaAboveCell10102312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell10102312)) h
theorem e24KC2ThetaAboveLeaf1010231210 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell10102312)) = true := by
  have h : ((childLL (childLH thetaAboveCell10102312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell10102312)) h
theorem e24KC2ThetaAboveLeaf1010231211 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell10102312)) = true := by
  have h : ((childLH (childLH thetaAboveCell10102312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell10102312)) h
theorem e24KC2ThetaAboveLeaf1010231212 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell10102312)) = true := by
  have h : ((childHL (childLH thetaAboveCell10102312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell10102312)) h
theorem e24KC2ThetaAboveLeaf1010231213 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell10102312)) = true := by
  have h : ((childHH (childLH thetaAboveCell10102312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell10102312)) h
theorem e24KC2ThetaAboveLeaf101023122 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10102312) = true := by
  have h : ((childHL thetaAboveCell10102312)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell10102312) h
theorem e24KC2ThetaAboveLeaf101023123 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10102312) = true := by
  have h : ((childHH thetaAboveCell10102312)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell10102312) h
theorem e24KC2ThetaAboveLeaf1010231300 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell10102313)) = true := by
  have h : ((childLL (childLL thetaAboveCell10102313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell10102313)) h
theorem e24KC2ThetaAboveLeaf1010231301 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell10102313)) = true := by
  have h : ((childLH (childLL thetaAboveCell10102313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell10102313)) h
theorem e24KC2ThetaAboveLeaf1010231302 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell10102313)) = true := by
  have h : ((childHL (childLL thetaAboveCell10102313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell10102313)) h
theorem e24KC2ThetaAboveLeaf1010231303 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell10102313)) = true := by
  have h : ((childHH (childLL thetaAboveCell10102313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell10102313)) h
theorem e24KC2ThetaAboveLeaf1010231310 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell10102313)) = true := by
  have h : ((childLL (childLH thetaAboveCell10102313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell10102313)) h
theorem e24KC2ThetaAboveLeaf1010231311 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell10102313)) = true := by
  have h : ((childLH (childLH thetaAboveCell10102313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell10102313)) h
theorem e24KC2ThetaAboveLeaf1010231312 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell10102313)) = true := by
  have h : ((childHL (childLH thetaAboveCell10102313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell10102313)) h
theorem e24KC2ThetaAboveLeaf1010231313 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell10102313)) = true := by
  have h : ((childHH (childLH thetaAboveCell10102313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell10102313)) h
theorem e24KC2ThetaAboveLeaf101023132 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10102313) = true := by
  have h : ((childHL thetaAboveCell10102313)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell10102313) h
theorem e24KC2ThetaAboveLeaf101023133 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10102313) = true := by
  have h : ((childHH thetaAboveCell10102313)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell10102313) h
theorem e24KC2ThetaAboveLeaf101023200 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10102320) = true := by
  have h : ((childLL thetaAboveCell10102320)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell10102320) h
theorem e24KC2ThetaAboveLeaf101023201 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10102320) = true := by
  have h : ((childLH thetaAboveCell10102320)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell10102320) h
theorem e24KC2ThetaAboveLeaf101023202 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10102320) = true := by
  have h : ((childHL thetaAboveCell10102320)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell10102320) h
theorem e24KC2ThetaAboveLeaf101023203 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10102320) = true := by
  have h : ((childHH thetaAboveCell10102320)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell10102320) h
theorem e24KC2ThetaAboveLeaf101023210 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10102321) = true := by
  have h : ((childLL thetaAboveCell10102321)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell10102321) h
theorem e24KC2ThetaAboveLeaf101023211 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10102321) = true := by
  have h : ((childLH thetaAboveCell10102321)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell10102321) h
theorem e24KC2ThetaAboveLeaf101023212 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10102321) = true := by
  have h : ((childHL thetaAboveCell10102321)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell10102321) h
theorem e24KC2ThetaAboveLeaf101023213 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10102321) = true := by
  have h : ((childHH thetaAboveCell10102321)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell10102321) h
theorem e24KC2ThetaAboveLeaf10102322 :
    adaptiveCoverCheck 11 thetaAboveCell10102322 = true := by
  have h : (thetaAboveCell10102322).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell10102322 h
theorem e24KC2ThetaAboveLeaf10102323 :
    adaptiveCoverCheck 11 thetaAboveCell10102323 = true := by
  have h : (thetaAboveCell10102323).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell10102323 h
theorem e24KC2ThetaAboveLeaf101023300 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10102330) = true := by
  have h : ((childLL thetaAboveCell10102330)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell10102330) h
theorem e24KC2ThetaAboveLeaf101023301 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10102330) = true := by
  have h : ((childLH thetaAboveCell10102330)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell10102330) h
theorem e24KC2ThetaAboveLeaf101023302 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10102330) = true := by
  have h : ((childHL thetaAboveCell10102330)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell10102330) h
theorem e24KC2ThetaAboveLeaf101023303 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10102330) = true := by
  have h : ((childHH thetaAboveCell10102330)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell10102330) h
theorem e24KC2ThetaAboveLeaf101023310 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10102331) = true := by
  have h : ((childLL thetaAboveCell10102331)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell10102331) h
theorem e24KC2ThetaAboveLeaf101023311 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10102331) = true := by
  have h : ((childLH thetaAboveCell10102331)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell10102331) h
theorem e24KC2ThetaAboveLeaf101023312 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10102331) = true := by
  have h : ((childHL thetaAboveCell10102331)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell10102331) h
theorem e24KC2ThetaAboveLeaf101023313 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10102331) = true := by
  have h : ((childHH thetaAboveCell10102331)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell10102331) h
theorem e24KC2ThetaAboveLeaf10102332 :
    adaptiveCoverCheck 11 thetaAboveCell10102332 = true := by
  have h : (thetaAboveCell10102332).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell10102332 h
theorem e24KC2ThetaAboveLeaf10102333 :
    adaptiveCoverCheck 11 thetaAboveCell10102333 = true := by
  have h : (thetaAboveCell10102333).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell10102333 h
theorem e24KC2ThetaAboveLeaf1010300 :
    adaptiveCoverCheck 12 (childLL (childLL (childHH thetaAboveCell1010))) = true := by
  have h : ((childLL (childLL (childHH thetaAboveCell1010)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLL (childHH thetaAboveCell1010))) h
theorem e24KC2ThetaAboveLeaf1010301 :
    adaptiveCoverCheck 12 (childLH (childLL (childHH thetaAboveCell1010))) = true := by
  have h : ((childLH (childLL (childHH thetaAboveCell1010)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLL (childHH thetaAboveCell1010))) h
theorem e24KC2ThetaAboveLeaf1010302 :
    adaptiveCoverCheck 12 (childHL (childLL (childHH thetaAboveCell1010))) = true := by
  have h : ((childHL (childLL (childHH thetaAboveCell1010)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLL (childHH thetaAboveCell1010))) h
theorem e24KC2ThetaAboveLeaf1010303 :
    adaptiveCoverCheck 12 (childHH (childLL (childHH thetaAboveCell1010))) = true := by
  have h : ((childHH (childLL (childHH thetaAboveCell1010)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLL (childHH thetaAboveCell1010))) h
theorem e24KC2ThetaAboveLeaf1010310 :
    adaptiveCoverCheck 12 (childLL (childLH (childHH thetaAboveCell1010))) = true := by
  have h : ((childLL (childLH (childHH thetaAboveCell1010)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLH (childHH thetaAboveCell1010))) h
theorem e24KC2ThetaAboveLeaf1010311 :
    adaptiveCoverCheck 12 (childLH (childLH (childHH thetaAboveCell1010))) = true := by
  have h : ((childLH (childLH (childHH thetaAboveCell1010)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLH (childHH thetaAboveCell1010))) h
theorem e24KC2ThetaAboveLeaf1010312 :
    adaptiveCoverCheck 12 (childHL (childLH (childHH thetaAboveCell1010))) = true := by
  have h : ((childHL (childLH (childHH thetaAboveCell1010)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLH (childHH thetaAboveCell1010))) h
theorem e24KC2ThetaAboveLeaf1010313 :
    adaptiveCoverCheck 12 (childHH (childLH (childHH thetaAboveCell1010))) = true := by
  have h : ((childHH (childLH (childHH thetaAboveCell1010)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLH (childHH thetaAboveCell1010))) h
theorem e24KC2ThetaAboveLeaf101032000 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10103200) = true := by
  have h : ((childLL thetaAboveCell10103200)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell10103200) h
theorem e24KC2ThetaAboveLeaf101032001 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10103200) = true := by
  have h : ((childLH thetaAboveCell10103200)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell10103200) h
theorem e24KC2ThetaAboveLeaf101032002 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10103200) = true := by
  have h : ((childHL thetaAboveCell10103200)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell10103200) h
theorem e24KC2ThetaAboveLeaf101032003 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10103200) = true := by
  have h : ((childHH thetaAboveCell10103200)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell10103200) h
theorem e24KC2ThetaAboveLeaf101032010 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10103201) = true := by
  have h : ((childLL thetaAboveCell10103201)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell10103201) h
theorem e24KC2ThetaAboveLeaf101032011 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10103201) = true := by
  have h : ((childLH thetaAboveCell10103201)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell10103201) h
theorem e24KC2ThetaAboveLeaf101032012 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10103201) = true := by
  have h : ((childHL thetaAboveCell10103201)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell10103201) h
theorem e24KC2ThetaAboveLeaf101032013 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10103201) = true := by
  have h : ((childHH thetaAboveCell10103201)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell10103201) h
theorem e24KC2ThetaAboveLeaf1010320200 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell10103202)) = true := by
  have h : ((childLL (childLL thetaAboveCell10103202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell10103202)) h
theorem e24KC2ThetaAboveLeaf1010320201 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell10103202)) = true := by
  have h : ((childLH (childLL thetaAboveCell10103202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell10103202)) h
theorem e24KC2ThetaAboveLeaf1010320202 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell10103202)) = true := by
  have h : ((childHL (childLL thetaAboveCell10103202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell10103202)) h
theorem e24KC2ThetaAboveLeaf1010320203 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell10103202)) = true := by
  have h : ((childHH (childLL thetaAboveCell10103202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell10103202)) h
theorem e24KC2ThetaAboveLeaf1010320210 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell10103202)) = true := by
  have h : ((childLL (childLH thetaAboveCell10103202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell10103202)) h
theorem e24KC2ThetaAboveLeaf1010320211 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell10103202)) = true := by
  have h : ((childLH (childLH thetaAboveCell10103202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell10103202)) h
theorem e24KC2ThetaAboveLeaf1010320212 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell10103202)) = true := by
  have h : ((childHL (childLH thetaAboveCell10103202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell10103202)) h
theorem e24KC2ThetaAboveLeaf1010320213 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell10103202)) = true := by
  have h : ((childHH (childLH thetaAboveCell10103202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell10103202)) h
theorem e24KC2ThetaAboveLeaf101032022 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10103202) = true := by
  have h : ((childHL thetaAboveCell10103202)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell10103202) h
theorem e24KC2ThetaAboveLeaf101032023 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10103202) = true := by
  have h : ((childHH thetaAboveCell10103202)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell10103202) h
theorem e24KC2ThetaAboveLeaf1010320300 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell10103203)) = true := by
  have h : ((childLL (childLL thetaAboveCell10103203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell10103203)) h
theorem e24KC2ThetaAboveLeaf1010320301 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell10103203)) = true := by
  have h : ((childLH (childLL thetaAboveCell10103203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell10103203)) h
theorem e24KC2ThetaAboveLeaf1010320302 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell10103203)) = true := by
  have h : ((childHL (childLL thetaAboveCell10103203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell10103203)) h
theorem e24KC2ThetaAboveLeaf1010320303 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell10103203)) = true := by
  have h : ((childHH (childLL thetaAboveCell10103203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell10103203)) h
theorem e24KC2ThetaAboveLeaf1010320310 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell10103203)) = true := by
  have h : ((childLL (childLH thetaAboveCell10103203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell10103203)) h
theorem e24KC2ThetaAboveLeaf1010320311 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell10103203)) = true := by
  have h : ((childLH (childLH thetaAboveCell10103203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell10103203)) h
theorem e24KC2ThetaAboveLeaf1010320312 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell10103203)) = true := by
  have h : ((childHL (childLH thetaAboveCell10103203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell10103203)) h
theorem e24KC2ThetaAboveLeaf1010320313 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell10103203)) = true := by
  have h : ((childHH (childLH thetaAboveCell10103203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell10103203)) h
theorem e24KC2ThetaAboveLeaf101032032 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10103203) = true := by
  have h : ((childHL thetaAboveCell10103203)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell10103203) h
theorem e24KC2ThetaAboveLeaf101032033 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10103203) = true := by
  have h : ((childHH thetaAboveCell10103203)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell10103203) h
theorem e24KC2ThetaAboveLeaf101032100 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10103210) = true := by
  have h : ((childLL thetaAboveCell10103210)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell10103210) h
theorem e24KC2ThetaAboveLeaf101032101 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10103210) = true := by
  have h : ((childLH thetaAboveCell10103210)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell10103210) h
theorem e24KC2ThetaAboveLeaf101032102 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10103210) = true := by
  have h : ((childHL thetaAboveCell10103210)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell10103210) h
theorem e24KC2ThetaAboveLeaf101032103 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10103210) = true := by
  have h : ((childHH thetaAboveCell10103210)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell10103210) h
theorem e24KC2ThetaAboveLeaf101032110 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10103211) = true := by
  have h : ((childLL thetaAboveCell10103211)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell10103211) h
theorem e24KC2ThetaAboveLeaf101032111 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10103211) = true := by
  have h : ((childLH thetaAboveCell10103211)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell10103211) h
theorem e24KC2ThetaAboveLeaf101032112 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10103211) = true := by
  have h : ((childHL thetaAboveCell10103211)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell10103211) h
theorem e24KC2ThetaAboveLeaf101032113 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10103211) = true := by
  have h : ((childHH thetaAboveCell10103211)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell10103211) h
theorem e24KC2ThetaAboveLeaf1010321200 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell10103212)) = true := by
  have h : ((childLL (childLL thetaAboveCell10103212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell10103212)) h
theorem e24KC2ThetaAboveLeaf1010321201 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell10103212)) = true := by
  have h : ((childLH (childLL thetaAboveCell10103212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell10103212)) h
theorem e24KC2ThetaAboveLeaf1010321202 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell10103212)) = true := by
  have h : ((childHL (childLL thetaAboveCell10103212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell10103212)) h
theorem e24KC2ThetaAboveLeaf1010321203 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell10103212)) = true := by
  have h : ((childHH (childLL thetaAboveCell10103212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell10103212)) h
theorem e24KC2ThetaAboveLeaf1010321210 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell10103212)) = true := by
  have h : ((childLL (childLH thetaAboveCell10103212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell10103212)) h
theorem e24KC2ThetaAboveLeaf1010321211 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell10103212)) = true := by
  have h : ((childLH (childLH thetaAboveCell10103212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell10103212)) h
theorem e24KC2ThetaAboveLeaf1010321212 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell10103212)) = true := by
  have h : ((childHL (childLH thetaAboveCell10103212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell10103212)) h
theorem e24KC2ThetaAboveLeaf1010321213 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell10103212)) = true := by
  have h : ((childHH (childLH thetaAboveCell10103212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell10103212)) h
theorem e24KC2ThetaAboveLeaf101032122 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10103212) = true := by
  have h : ((childHL thetaAboveCell10103212)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell10103212) h
theorem e24KC2ThetaAboveLeaf101032123 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10103212) = true := by
  have h : ((childHH thetaAboveCell10103212)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell10103212) h
theorem e24KC2ThetaAboveLeaf1010321300 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell10103213)) = true := by
  have h : ((childLL (childLL thetaAboveCell10103213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell10103213)) h
theorem e24KC2ThetaAboveLeaf1010321301 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell10103213)) = true := by
  have h : ((childLH (childLL thetaAboveCell10103213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell10103213)) h
theorem e24KC2ThetaAboveLeaf1010321302 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell10103213)) = true := by
  have h : ((childHL (childLL thetaAboveCell10103213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell10103213)) h
theorem e24KC2ThetaAboveLeaf1010321303 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell10103213)) = true := by
  have h : ((childHH (childLL thetaAboveCell10103213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell10103213)) h
theorem e24KC2ThetaAboveLeaf1010321310 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell10103213)) = true := by
  have h : ((childLL (childLH thetaAboveCell10103213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell10103213)) h
theorem e24KC2ThetaAboveLeaf1010321311 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell10103213)) = true := by
  have h : ((childLH (childLH thetaAboveCell10103213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell10103213)) h
theorem e24KC2ThetaAboveLeaf1010321312 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell10103213)) = true := by
  have h : ((childHL (childLH thetaAboveCell10103213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell10103213)) h
theorem e24KC2ThetaAboveLeaf1010321313 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell10103213)) = true := by
  have h : ((childHH (childLH thetaAboveCell10103213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell10103213)) h
theorem e24KC2ThetaAboveLeaf101032132 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10103213) = true := by
  have h : ((childHL thetaAboveCell10103213)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell10103213) h
theorem e24KC2ThetaAboveLeaf101032133 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10103213) = true := by
  have h : ((childHH thetaAboveCell10103213)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell10103213) h
theorem e24KC2ThetaAboveLeaf101032200 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10103220) = true := by
  have h : ((childLL thetaAboveCell10103220)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell10103220) h
theorem e24KC2ThetaAboveLeaf101032201 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10103220) = true := by
  have h : ((childLH thetaAboveCell10103220)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell10103220) h
theorem e24KC2ThetaAboveLeaf101032202 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10103220) = true := by
  have h : ((childHL thetaAboveCell10103220)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell10103220) h
theorem e24KC2ThetaAboveLeaf101032203 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10103220) = true := by
  have h : ((childHH thetaAboveCell10103220)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell10103220) h
theorem e24KC2ThetaAboveLeaf101032210 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10103221) = true := by
  have h : ((childLL thetaAboveCell10103221)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell10103221) h
theorem e24KC2ThetaAboveLeaf101032211 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10103221) = true := by
  have h : ((childLH thetaAboveCell10103221)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell10103221) h
theorem e24KC2ThetaAboveLeaf101032212 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10103221) = true := by
  have h : ((childHL thetaAboveCell10103221)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell10103221) h
theorem e24KC2ThetaAboveLeaf101032213 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10103221) = true := by
  have h : ((childHH thetaAboveCell10103221)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell10103221) h
theorem e24KC2ThetaAboveLeaf10103222 :
    adaptiveCoverCheck 11 thetaAboveCell10103222 = true := by
  have h : (thetaAboveCell10103222).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell10103222 h
theorem e24KC2ThetaAboveLeaf10103223 :
    adaptiveCoverCheck 11 thetaAboveCell10103223 = true := by
  have h : (thetaAboveCell10103223).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell10103223 h
theorem e24KC2ThetaAboveLeaf101032300 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10103230) = true := by
  have h : ((childLL thetaAboveCell10103230)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell10103230) h
theorem e24KC2ThetaAboveLeaf101032301 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10103230) = true := by
  have h : ((childLH thetaAboveCell10103230)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell10103230) h
theorem e24KC2ThetaAboveLeaf101032302 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10103230) = true := by
  have h : ((childHL thetaAboveCell10103230)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell10103230) h
theorem e24KC2ThetaAboveLeaf101032303 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10103230) = true := by
  have h : ((childHH thetaAboveCell10103230)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell10103230) h
theorem e24KC2ThetaAboveLeaf101032310 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10103231) = true := by
  have h : ((childLL thetaAboveCell10103231)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell10103231) h
theorem e24KC2ThetaAboveLeaf101032311 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10103231) = true := by
  have h : ((childLH thetaAboveCell10103231)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell10103231) h
theorem e24KC2ThetaAboveLeaf101032312 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10103231) = true := by
  have h : ((childHL thetaAboveCell10103231)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell10103231) h
theorem e24KC2ThetaAboveLeaf101032313 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10103231) = true := by
  have h : ((childHH thetaAboveCell10103231)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell10103231) h
theorem e24KC2ThetaAboveLeaf10103232 :
    adaptiveCoverCheck 11 thetaAboveCell10103232 = true := by
  have h : (thetaAboveCell10103232).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell10103232 h
theorem e24KC2ThetaAboveLeaf10103233 :
    adaptiveCoverCheck 11 thetaAboveCell10103233 = true := by
  have h : (thetaAboveCell10103233).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell10103233 h
theorem e24KC2ThetaAboveLeaf101033000 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10103300) = true := by
  have h : ((childLL thetaAboveCell10103300)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell10103300) h
theorem e24KC2ThetaAboveLeaf101033001 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10103300) = true := by
  have h : ((childLH thetaAboveCell10103300)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell10103300) h

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

* `KernelOnly.PartE.E24KC5TerminalBatchT51200004`.
-/

public section

noncomputable section

section

/-! E24KC5 checkpoint-aware kernel batch. -/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellse876d675ca

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCellse876d675ca

open CertificateCellse876d675ca
theorem e24KC2ThetaAboveLeaf00003121 :
    adaptiveCoverCheck 11 thetaAboveCell00003121 = true := by
  have h : (thetaAboveCell00003121).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00003121 h
theorem e24KC2ThetaAboveLeaf000031220 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell00003122) = true := by
  have h : ((childLL thetaAboveCell00003122)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell00003122) h
theorem e24KC2ThetaAboveLeaf000031221 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell00003122) = true := by
  have h : ((childLH thetaAboveCell00003122)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell00003122) h
theorem e24KC2ThetaAboveLeaf000031222 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell00003122) = true := by
  have h : ((childHL thetaAboveCell00003122)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell00003122) h
theorem e24KC2ThetaAboveLeaf000031223 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell00003122) = true := by
  have h : ((childHH thetaAboveCell00003122)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell00003122) h
theorem e24KC2ThetaAboveLeaf000031230 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell00003123) = true := by
  have h : ((childLL thetaAboveCell00003123)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell00003123) h
theorem e24KC2ThetaAboveLeaf000031231 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell00003123) = true := by
  have h : ((childLH thetaAboveCell00003123)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell00003123) h
theorem e24KC2ThetaAboveLeaf000031232 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell00003123) = true := by
  have h : ((childHL thetaAboveCell00003123)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell00003123) h
theorem e24KC2ThetaAboveLeaf000031233 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell00003123) = true := by
  have h : ((childHH thetaAboveCell00003123)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell00003123) h
theorem e24KC2ThetaAboveLeaf00003130 :
    adaptiveCoverCheck 11 thetaAboveCell00003130 = true := by
  have h : (thetaAboveCell00003130).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00003130 h
theorem e24KC2ThetaAboveLeaf00003131 :
    adaptiveCoverCheck 11 thetaAboveCell00003131 = true := by
  have h : (thetaAboveCell00003131).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00003131 h
theorem e24KC2ThetaAboveLeaf000031320 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell00003132) = true := by
  have h : ((childLL thetaAboveCell00003132)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell00003132) h
theorem e24KC2ThetaAboveLeaf000031321 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell00003132) = true := by
  have h : ((childLH thetaAboveCell00003132)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell00003132) h
theorem e24KC2ThetaAboveLeaf000031322 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell00003132) = true := by
  have h : ((childHL thetaAboveCell00003132)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell00003132) h
theorem e24KC2ThetaAboveLeaf000031323 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell00003132) = true := by
  have h : ((childHH thetaAboveCell00003132)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell00003132) h
theorem e24KC2ThetaAboveLeaf000031330 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell00003133) = true := by
  have h : ((childLL thetaAboveCell00003133)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell00003133) h
theorem e24KC2ThetaAboveLeaf000031331 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell00003133) = true := by
  have h : ((childLH thetaAboveCell00003133)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell00003133) h
theorem e24KC2ThetaAboveLeaf000031332 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell00003133) = true := by
  have h : ((childHL thetaAboveCell00003133)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell00003133) h
theorem e24KC2ThetaAboveLeaf000031333 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell00003133) = true := by
  have h : ((childHH thetaAboveCell00003133)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell00003133) h
theorem e24KC2ThetaAboveLeaf0000320000 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell00003200)) = true := by
  have h : ((childLL (childLL thetaAboveCell00003200))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell00003200)) h
theorem e24KC2ThetaAboveLeaf0000320001 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell00003200)) = true := by
  have h : ((childLH (childLL thetaAboveCell00003200))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell00003200)) h
theorem e24KC2ThetaAboveLeaf0000320010 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell00003200)) = true := by
  have h : ((childLL (childLH thetaAboveCell00003200))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell00003200)) h
theorem e24KC2ThetaAboveLeaf0000320011 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell00003200)) = true := by
  have h : ((childLH (childLH thetaAboveCell00003200))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell00003200)) h
theorem e24KC2ThetaAboveLeaf0000320100 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell00003201)) = true := by
  have h : ((childLL (childLL thetaAboveCell00003201))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell00003201)) h
theorem e24KC2ThetaAboveLeaf0000320101 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell00003201)) = true := by
  have h : ((childLH (childLL thetaAboveCell00003201))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell00003201)) h
theorem e24KC2ThetaAboveLeaf0000320110 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell00003201)) = true := by
  have h : ((childLL (childLH thetaAboveCell00003201))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell00003201)) h
theorem e24KC2ThetaAboveLeaf0000320111 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell00003201)) = true := by
  have h : ((childLH (childLH thetaAboveCell00003201))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell00003201)) h
theorem e24KC2ThetaAboveLeaf0000320200 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell00003202)) = true := by
  have h : ((childLL (childLL thetaAboveCell00003202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell00003202)) h
theorem e24KC2ThetaAboveLeaf0000320201 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell00003202)) = true := by
  have h : ((childLH (childLL thetaAboveCell00003202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell00003202)) h
theorem e24KC2ThetaAboveLeaf0000320202 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell00003202)) = true := by
  have h : ((childHL (childLL thetaAboveCell00003202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell00003202)) h
theorem e24KC2ThetaAboveLeaf0000320203 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell00003202)) = true := by
  have h : ((childHH (childLL thetaAboveCell00003202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell00003202)) h
theorem e24KC2ThetaAboveLeaf0000320210 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell00003202)) = true := by
  have h : ((childLL (childLH thetaAboveCell00003202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell00003202)) h
theorem e24KC2ThetaAboveLeaf0000320211 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell00003202)) = true := by
  have h : ((childLH (childLH thetaAboveCell00003202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell00003202)) h
theorem e24KC2ThetaAboveLeaf0000320212 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell00003202)) = true := by
  have h : ((childHL (childLH thetaAboveCell00003202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell00003202)) h
theorem e24KC2ThetaAboveLeaf0000320213 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell00003202)) = true := by
  have h : ((childHH (childLH thetaAboveCell00003202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell00003202)) h
theorem e24KC2ThetaAboveLeaf000032022 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell00003202) = true := by
  have h : ((childHL thetaAboveCell00003202)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell00003202) h
theorem e24KC2ThetaAboveLeaf000032023 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell00003202) = true := by
  have h : ((childHH thetaAboveCell00003202)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell00003202) h
theorem e24KC2ThetaAboveLeaf0000320300 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell00003203)) = true := by
  have h : ((childLL (childLL thetaAboveCell00003203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell00003203)) h
theorem e24KC2ThetaAboveLeaf0000320301 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell00003203)) = true := by
  have h : ((childLH (childLL thetaAboveCell00003203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell00003203)) h
theorem e24KC2ThetaAboveLeaf0000320302 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell00003203)) = true := by
  have h : ((childHL (childLL thetaAboveCell00003203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell00003203)) h
theorem e24KC2ThetaAboveLeaf0000320303 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell00003203)) = true := by
  have h : ((childHH (childLL thetaAboveCell00003203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell00003203)) h
theorem e24KC2ThetaAboveLeaf0000320310 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell00003203)) = true := by
  have h : ((childLL (childLH thetaAboveCell00003203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell00003203)) h
theorem e24KC2ThetaAboveLeaf0000320311 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell00003203)) = true := by
  have h : ((childLH (childLH thetaAboveCell00003203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell00003203)) h
theorem e24KC2ThetaAboveLeaf0000320312 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell00003203)) = true := by
  have h : ((childHL (childLH thetaAboveCell00003203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell00003203)) h
theorem e24KC2ThetaAboveLeaf0000320313 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell00003203)) = true := by
  have h : ((childHH (childLH thetaAboveCell00003203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell00003203)) h
theorem e24KC2ThetaAboveLeaf000032032 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell00003203) = true := by
  have h : ((childHL thetaAboveCell00003203)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell00003203) h
theorem e24KC2ThetaAboveLeaf000032033 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell00003203) = true := by
  have h : ((childHH thetaAboveCell00003203)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell00003203) h
theorem e24KC2ThetaAboveLeaf0000321000 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell00003210)) = true := by
  have h : ((childLL (childLL thetaAboveCell00003210))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell00003210)) h
theorem e24KC2ThetaAboveLeaf0000321001 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell00003210)) = true := by
  have h : ((childLH (childLL thetaAboveCell00003210))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell00003210)) h
theorem e24KC2ThetaAboveLeaf0000321010 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell00003210)) = true := by
  have h : ((childLL (childLH thetaAboveCell00003210))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell00003210)) h
theorem e24KC2ThetaAboveLeaf0000321011 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell00003210)) = true := by
  have h : ((childLH (childLH thetaAboveCell00003210))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell00003210)) h
theorem e24KC2ThetaAboveLeaf0000321100 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell00003211)) = true := by
  have h : ((childLL (childLL thetaAboveCell00003211))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell00003211)) h
theorem e24KC2ThetaAboveLeaf0000321101 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell00003211)) = true := by
  have h : ((childLH (childLL thetaAboveCell00003211))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell00003211)) h
theorem e24KC2ThetaAboveLeaf0000321110 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell00003211)) = true := by
  have h : ((childLL (childLH thetaAboveCell00003211))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell00003211)) h
theorem e24KC2ThetaAboveLeaf0000321111 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell00003211)) = true := by
  have h : ((childLH (childLH thetaAboveCell00003211))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell00003211)) h
theorem e24KC2ThetaAboveLeaf0000321200 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell00003212)) = true := by
  have h : ((childLL (childLL thetaAboveCell00003212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell00003212)) h
theorem e24KC2ThetaAboveLeaf0000321201 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell00003212)) = true := by
  have h : ((childLH (childLL thetaAboveCell00003212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell00003212)) h
theorem e24KC2ThetaAboveLeaf0000321202 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell00003212)) = true := by
  have h : ((childHL (childLL thetaAboveCell00003212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell00003212)) h
theorem e24KC2ThetaAboveLeaf0000321203 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell00003212)) = true := by
  have h : ((childHH (childLL thetaAboveCell00003212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell00003212)) h
theorem e24KC2ThetaAboveLeaf0000321210 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell00003212)) = true := by
  have h : ((childLL (childLH thetaAboveCell00003212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell00003212)) h
theorem e24KC2ThetaAboveLeaf0000321211 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell00003212)) = true := by
  have h : ((childLH (childLH thetaAboveCell00003212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell00003212)) h
theorem e24KC2ThetaAboveLeaf0000321212 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell00003212)) = true := by
  have h : ((childHL (childLH thetaAboveCell00003212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell00003212)) h
theorem e24KC2ThetaAboveLeaf0000321213 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell00003212)) = true := by
  have h : ((childHH (childLH thetaAboveCell00003212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell00003212)) h
theorem e24KC2ThetaAboveLeaf000032122 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell00003212) = true := by
  have h : ((childHL thetaAboveCell00003212)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell00003212) h
theorem e24KC2ThetaAboveLeaf000032123 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell00003212) = true := by
  have h : ((childHH thetaAboveCell00003212)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell00003212) h
theorem e24KC2ThetaAboveLeaf0000321300 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell00003213)) = true := by
  have h : ((childLL (childLL thetaAboveCell00003213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell00003213)) h
theorem e24KC2ThetaAboveLeaf0000321301 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell00003213)) = true := by
  have h : ((childLH (childLL thetaAboveCell00003213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell00003213)) h
theorem e24KC2ThetaAboveLeaf0000321302 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell00003213)) = true := by
  have h : ((childHL (childLL thetaAboveCell00003213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell00003213)) h
theorem e24KC2ThetaAboveLeaf0000321303 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell00003213)) = true := by
  have h : ((childHH (childLL thetaAboveCell00003213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell00003213)) h
theorem e24KC2ThetaAboveLeaf0000321310 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell00003213)) = true := by
  have h : ((childLL (childLH thetaAboveCell00003213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell00003213)) h
theorem e24KC2ThetaAboveLeaf0000321311 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell00003213)) = true := by
  have h : ((childLH (childLH thetaAboveCell00003213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell00003213)) h
theorem e24KC2ThetaAboveLeaf0000321312 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell00003213)) = true := by
  have h : ((childHL (childLH thetaAboveCell00003213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell00003213)) h
theorem e24KC2ThetaAboveLeaf0000321313 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell00003213)) = true := by
  have h : ((childHH (childLH thetaAboveCell00003213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell00003213)) h
theorem e24KC2ThetaAboveLeaf000032132 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell00003213) = true := by
  have h : ((childHL thetaAboveCell00003213)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell00003213) h
theorem e24KC2ThetaAboveLeaf000032133 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell00003213) = true := by
  have h : ((childHH thetaAboveCell00003213)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell00003213) h
theorem e24KC2ThetaAboveLeaf00003220 :
    adaptiveCoverCheck 11 thetaAboveCell00003220 = true := by
  have h : (thetaAboveCell00003220).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00003220 h
theorem e24KC2ThetaAboveLeaf00003221 :
    adaptiveCoverCheck 11 thetaAboveCell00003221 = true := by
  have h : (thetaAboveCell00003221).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00003221 h
theorem e24KC2ThetaAboveLeaf00003222 :
    adaptiveCoverCheck 11 thetaAboveCell00003222 = true := by
  have h : (thetaAboveCell00003222).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00003222 h
theorem e24KC2ThetaAboveLeaf00003223 :
    adaptiveCoverCheck 11 thetaAboveCell00003223 = true := by
  have h : (thetaAboveCell00003223).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00003223 h
theorem e24KC2ThetaAboveLeaf00003230 :
    adaptiveCoverCheck 11 thetaAboveCell00003230 = true := by
  have h : (thetaAboveCell00003230).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00003230 h
theorem e24KC2ThetaAboveLeaf00003231 :
    adaptiveCoverCheck 11 thetaAboveCell00003231 = true := by
  have h : (thetaAboveCell00003231).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00003231 h
theorem e24KC2ThetaAboveLeaf00003232 :
    adaptiveCoverCheck 11 thetaAboveCell00003232 = true := by
  have h : (thetaAboveCell00003232).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00003232 h
theorem e24KC2ThetaAboveLeaf00003233 :
    adaptiveCoverCheck 11 thetaAboveCell00003233 = true := by
  have h : (thetaAboveCell00003233).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00003233 h
theorem e24KC2ThetaAboveLeaf0000330000 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell00003300)) = true := by
  have h : ((childLL (childLL thetaAboveCell00003300))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell00003300)) h
theorem e24KC2ThetaAboveLeaf0000330001 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell00003300)) = true := by
  have h : ((childLH (childLL thetaAboveCell00003300))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell00003300)) h
theorem e24KC2ThetaAboveLeaf0000330010 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell00003300)) = true := by
  have h : ((childLL (childLH thetaAboveCell00003300))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell00003300)) h
theorem e24KC2ThetaAboveLeaf0000330011 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell00003300)) = true := by
  have h : ((childLH (childLH thetaAboveCell00003300))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell00003300)) h
theorem e24KC2ThetaAboveLeaf0000330100 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell00003301)) = true := by
  have h : ((childLL (childLL thetaAboveCell00003301))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell00003301)) h
theorem e24KC2ThetaAboveLeaf0000330101 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell00003301)) = true := by
  have h : ((childLH (childLL thetaAboveCell00003301))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell00003301)) h
theorem e24KC2ThetaAboveLeaf0000330110 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell00003301)) = true := by
  have h : ((childLL (childLH thetaAboveCell00003301))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell00003301)) h
theorem e24KC2ThetaAboveLeaf0000330111 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell00003301)) = true := by
  have h : ((childLH (childLH thetaAboveCell00003301))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell00003301)) h
theorem e24KC2ThetaAboveLeaf0000330200 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell00003302)) = true := by
  have h : ((childLL (childLL thetaAboveCell00003302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell00003302)) h
theorem e24KC2ThetaAboveLeaf0000330201 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell00003302)) = true := by
  have h : ((childLH (childLL thetaAboveCell00003302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell00003302)) h
theorem e24KC2ThetaAboveLeaf0000330202 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell00003302)) = true := by
  have h : ((childHL (childLL thetaAboveCell00003302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell00003302)) h
theorem e24KC2ThetaAboveLeaf0000330203 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell00003302)) = true := by
  have h : ((childHH (childLL thetaAboveCell00003302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell00003302)) h
theorem e24KC2ThetaAboveLeaf0000330210 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell00003302)) = true := by
  have h : ((childLL (childLH thetaAboveCell00003302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell00003302)) h
theorem e24KC2ThetaAboveLeaf0000330211 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell00003302)) = true := by
  have h : ((childLH (childLH thetaAboveCell00003302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell00003302)) h
theorem e24KC2ThetaAboveLeaf0000330212 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell00003302)) = true := by
  have h : ((childHL (childLH thetaAboveCell00003302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell00003302)) h
theorem e24KC2ThetaAboveLeaf0000330213 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell00003302)) = true := by
  have h : ((childHH (childLH thetaAboveCell00003302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell00003302)) h
theorem e24KC2ThetaAboveLeaf000033022 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell00003302) = true := by
  have h : ((childHL thetaAboveCell00003302)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell00003302) h
theorem e24KC2ThetaAboveLeaf000033023 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell00003302) = true := by
  have h : ((childHH thetaAboveCell00003302)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell00003302) h
theorem e24KC2ThetaAboveLeaf0000330300 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell00003303)) = true := by
  have h : ((childLL (childLL thetaAboveCell00003303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell00003303)) h
theorem e24KC2ThetaAboveLeaf0000330301 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell00003303)) = true := by
  have h : ((childLH (childLL thetaAboveCell00003303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell00003303)) h
theorem e24KC2ThetaAboveLeaf0000330302 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell00003303)) = true := by
  have h : ((childHL (childLL thetaAboveCell00003303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell00003303)) h
theorem e24KC2ThetaAboveLeaf0000330303 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell00003303)) = true := by
  have h : ((childHH (childLL thetaAboveCell00003303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell00003303)) h
theorem e24KC2ThetaAboveLeaf0000330310 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell00003303)) = true := by
  have h : ((childLL (childLH thetaAboveCell00003303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell00003303)) h
theorem e24KC2ThetaAboveLeaf0000330311 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell00003303)) = true := by
  have h : ((childLH (childLH thetaAboveCell00003303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell00003303)) h
theorem e24KC2ThetaAboveLeaf0000330312 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell00003303)) = true := by
  have h : ((childHL (childLH thetaAboveCell00003303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell00003303)) h
theorem e24KC2ThetaAboveLeaf0000330313 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell00003303)) = true := by
  have h : ((childHH (childLH thetaAboveCell00003303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell00003303)) h
theorem e24KC2ThetaAboveLeaf000033032 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell00003303) = true := by
  have h : ((childHL thetaAboveCell00003303)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell00003303) h
theorem e24KC2ThetaAboveLeaf000033033 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell00003303) = true := by
  have h : ((childHH thetaAboveCell00003303)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell00003303) h
theorem e24KC2ThetaAboveLeaf0000331000 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell00003310)) = true := by
  have h : ((childLL (childLL thetaAboveCell00003310))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell00003310)) h
theorem e24KC2ThetaAboveLeaf0000331001 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell00003310)) = true := by
  have h : ((childLH (childLL thetaAboveCell00003310))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell00003310)) h
theorem e24KC2ThetaAboveLeaf0000331010 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell00003310)) = true := by
  have h : ((childLL (childLH thetaAboveCell00003310))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell00003310)) h
theorem e24KC2ThetaAboveLeaf0000331011 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell00003310)) = true := by
  have h : ((childLH (childLH thetaAboveCell00003310))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell00003310)) h
theorem e24KC2ThetaAboveLeaf0000331100 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell00003311)) = true := by
  have h : ((childLL (childLL thetaAboveCell00003311))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell00003311)) h
theorem e24KC2ThetaAboveLeaf0000331101 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell00003311)) = true := by
  have h : ((childLH (childLL thetaAboveCell00003311))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell00003311)) h
theorem e24KC2ThetaAboveLeaf0000331110 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell00003311)) = true := by
  have h : ((childLL (childLH thetaAboveCell00003311))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell00003311)) h
theorem e24KC2ThetaAboveLeaf0000331111 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell00003311)) = true := by
  have h : ((childLH (childLH thetaAboveCell00003311))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell00003311)) h
theorem e24KC2ThetaAboveLeaf0000331200 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell00003312)) = true := by
  have h : ((childLL (childLL thetaAboveCell00003312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell00003312)) h
theorem e24KC2ThetaAboveLeaf0000331201 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell00003312)) = true := by
  have h : ((childLH (childLL thetaAboveCell00003312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell00003312)) h
theorem e24KC2ThetaAboveLeaf0000331202 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell00003312)) = true := by
  have h : ((childHL (childLL thetaAboveCell00003312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell00003312)) h
theorem e24KC2ThetaAboveLeaf0000331203 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell00003312)) = true := by
  have h : ((childHH (childLL thetaAboveCell00003312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell00003312)) h
theorem e24KC2ThetaAboveLeaf0000331210 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell00003312)) = true := by
  have h : ((childLL (childLH thetaAboveCell00003312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell00003312)) h
theorem e24KC2ThetaAboveLeaf0000331211 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell00003312)) = true := by
  have h : ((childLH (childLH thetaAboveCell00003312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell00003312)) h
theorem e24KC2ThetaAboveLeaf0000331212 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell00003312)) = true := by
  have h : ((childHL (childLH thetaAboveCell00003312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell00003312)) h
theorem e24KC2ThetaAboveLeaf0000331213 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell00003312)) = true := by
  have h : ((childHH (childLH thetaAboveCell00003312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell00003312)) h
theorem e24KC2ThetaAboveLeaf000033122 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell00003312) = true := by
  have h : ((childHL thetaAboveCell00003312)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell00003312) h
theorem e24KC2ThetaAboveLeaf000033123 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell00003312) = true := by
  have h : ((childHH thetaAboveCell00003312)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell00003312) h
theorem e24KC2ThetaAboveLeaf0000331300 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell00003313)) = true := by
  have h : ((childLL (childLL thetaAboveCell00003313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell00003313)) h
theorem e24KC2ThetaAboveLeaf0000331301 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell00003313)) = true := by
  have h : ((childLH (childLL thetaAboveCell00003313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell00003313)) h
theorem e24KC2ThetaAboveLeaf0000331302 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell00003313)) = true := by
  have h : ((childHL (childLL thetaAboveCell00003313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell00003313)) h
theorem e24KC2ThetaAboveLeaf0000331303 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell00003313)) = true := by
  have h : ((childHH (childLL thetaAboveCell00003313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell00003313)) h
theorem e24KC2ThetaAboveLeaf0000331310 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell00003313)) = true := by
  have h : ((childLL (childLH thetaAboveCell00003313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell00003313)) h
theorem e24KC2ThetaAboveLeaf0000331311 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell00003313)) = true := by
  have h : ((childLH (childLH thetaAboveCell00003313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell00003313)) h
theorem e24KC2ThetaAboveLeaf0000331312 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell00003313)) = true := by
  have h : ((childHL (childLH thetaAboveCell00003313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell00003313)) h
theorem e24KC2ThetaAboveLeaf0000331313 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell00003313)) = true := by
  have h : ((childHH (childLH thetaAboveCell00003313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell00003313)) h
theorem e24KC2ThetaAboveLeaf000033132 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell00003313) = true := by
  have h : ((childHL thetaAboveCell00003313)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell00003313) h
theorem e24KC2ThetaAboveLeaf000033133 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell00003313) = true := by
  have h : ((childHH thetaAboveCell00003313)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell00003313) h
theorem e24KC2ThetaAboveLeaf00003320 :
    adaptiveCoverCheck 11 thetaAboveCell00003320 = true := by
  have h : (thetaAboveCell00003320).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00003320 h
theorem e24KC2ThetaAboveLeaf00003321 :
    adaptiveCoverCheck 11 thetaAboveCell00003321 = true := by
  have h : (thetaAboveCell00003321).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00003321 h
theorem e24KC2ThetaAboveLeaf00003322 :
    adaptiveCoverCheck 11 thetaAboveCell00003322 = true := by
  have h : (thetaAboveCell00003322).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00003322 h
theorem e24KC2ThetaAboveLeaf00003323 :
    adaptiveCoverCheck 11 thetaAboveCell00003323 = true := by
  have h : (thetaAboveCell00003323).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00003323 h
theorem e24KC2ThetaAboveLeaf00003330 :
    adaptiveCoverCheck 11 thetaAboveCell00003330 = true := by
  have h : (thetaAboveCell00003330).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00003330 h
theorem e24KC2ThetaAboveLeaf00003331 :
    adaptiveCoverCheck 11 thetaAboveCell00003331 = true := by
  have h : (thetaAboveCell00003331).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00003331 h
theorem e24KC2ThetaAboveLeaf00003332 :
    adaptiveCoverCheck 11 thetaAboveCell00003332 = true := by
  have h : (thetaAboveCell00003332).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00003332 h
theorem e24KC2ThetaAboveLeaf00003333 :
    adaptiveCoverCheck 11 thetaAboveCell00003333 = true := by
  have h : (thetaAboveCell00003333).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00003333 h
theorem e24KC2ThetaAboveLeaf000100 :
    adaptiveCoverCheck 13 (childLL (childLL thetaAboveCell0001)) = true := by
  have h : ((childLL (childLL thetaAboveCell0001))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLL (childLL thetaAboveCell0001)) h
theorem e24KC2ThetaAboveLeaf000101 :
    adaptiveCoverCheck 13 (childLH (childLL thetaAboveCell0001)) = true := by
  have h : ((childLH (childLL thetaAboveCell0001))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLH (childLL thetaAboveCell0001)) h
theorem e24KC2ThetaAboveLeaf000102 :
    adaptiveCoverCheck 13 (childHL (childLL thetaAboveCell0001)) = true := by
  have h : ((childHL (childLL thetaAboveCell0001))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHL (childLL thetaAboveCell0001)) h
theorem e24KC2ThetaAboveLeaf000103 :
    adaptiveCoverCheck 13 (childHH (childLL thetaAboveCell0001)) = true := by
  have h : ((childHH (childLL thetaAboveCell0001))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHH (childLL thetaAboveCell0001)) h
theorem e24KC2ThetaAboveLeaf000110 :
    adaptiveCoverCheck 13 (childLL (childLH thetaAboveCell0001)) = true := by
  have h : ((childLL (childLH thetaAboveCell0001))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLL (childLH thetaAboveCell0001)) h
theorem e24KC2ThetaAboveLeaf000111 :
    adaptiveCoverCheck 13 (childLH (childLH thetaAboveCell0001)) = true := by
  have h : ((childLH (childLH thetaAboveCell0001))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLH (childLH thetaAboveCell0001)) h
theorem e24KC2ThetaAboveLeaf000112 :
    adaptiveCoverCheck 13 (childHL (childLH thetaAboveCell0001)) = true := by
  have h : ((childHL (childLH thetaAboveCell0001))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHL (childLH thetaAboveCell0001)) h
theorem e24KC2ThetaAboveLeaf000113 :
    adaptiveCoverCheck 13 (childHH (childLH thetaAboveCell0001)) = true := by
  have h : ((childHH (childLH thetaAboveCell0001))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHH (childLH thetaAboveCell0001)) h
theorem e24KC2ThetaAboveLeaf0001200 :
    adaptiveCoverCheck 12 (childLL (childLL (childHL thetaAboveCell0001))) = true := by
  have h : ((childLL (childLL (childHL thetaAboveCell0001)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLL (childHL thetaAboveCell0001))) h
theorem e24KC2ThetaAboveLeaf0001201 :
    adaptiveCoverCheck 12 (childLH (childLL (childHL thetaAboveCell0001))) = true := by
  have h : ((childLH (childLL (childHL thetaAboveCell0001)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLL (childHL thetaAboveCell0001))) h
theorem e24KC2ThetaAboveLeaf00012020 :
    adaptiveCoverCheck 11 thetaAboveCell00012020 = true := by
  have h : (thetaAboveCell00012020).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00012020 h
theorem e24KC2ThetaAboveLeaf00012021 :
    adaptiveCoverCheck 11 thetaAboveCell00012021 = true := by
  have h : (thetaAboveCell00012021).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00012021 h
theorem e24KC2ThetaAboveLeaf000120220 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell00012022) = true := by
  have h : ((childLL thetaAboveCell00012022)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell00012022) h
theorem e24KC2ThetaAboveLeaf000120221 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell00012022) = true := by
  have h : ((childLH thetaAboveCell00012022)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell00012022) h
theorem e24KC2ThetaAboveLeaf000120222 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell00012022) = true := by
  have h : ((childHL thetaAboveCell00012022)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell00012022) h
theorem e24KC2ThetaAboveLeaf000120223 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell00012022) = true := by
  have h : ((childHH thetaAboveCell00012022)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell00012022) h
theorem e24KC2ThetaAboveLeaf000120230 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell00012023) = true := by
  have h : ((childLL thetaAboveCell00012023)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell00012023) h
theorem e24KC2ThetaAboveLeaf000120231 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell00012023) = true := by
  have h : ((childLH thetaAboveCell00012023)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell00012023) h
theorem e24KC2ThetaAboveLeaf000120232 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell00012023) = true := by
  have h : ((childHL thetaAboveCell00012023)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell00012023) h
theorem e24KC2ThetaAboveLeaf000120233 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell00012023) = true := by
  have h : ((childHH thetaAboveCell00012023)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell00012023) h
theorem e24KC2ThetaAboveLeaf00012030 :
    adaptiveCoverCheck 11 thetaAboveCell00012030 = true := by
  have h : (thetaAboveCell00012030).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00012030 h
theorem e24KC2ThetaAboveLeaf00012031 :
    adaptiveCoverCheck 11 thetaAboveCell00012031 = true := by
  have h : (thetaAboveCell00012031).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00012031 h
theorem e24KC2ThetaAboveLeaf000120320 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell00012032) = true := by
  have h : ((childLL thetaAboveCell00012032)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell00012032) h
theorem e24KC2ThetaAboveLeaf000120321 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell00012032) = true := by
  have h : ((childLH thetaAboveCell00012032)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell00012032) h
theorem e24KC2ThetaAboveLeaf000120322 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell00012032) = true := by
  have h : ((childHL thetaAboveCell00012032)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell00012032) h
theorem e24KC2ThetaAboveLeaf000120323 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell00012032) = true := by
  have h : ((childHH thetaAboveCell00012032)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell00012032) h
theorem e24KC2ThetaAboveLeaf000120330 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell00012033) = true := by
  have h : ((childLL thetaAboveCell00012033)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell00012033) h
theorem e24KC2ThetaAboveLeaf000120331 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell00012033) = true := by
  have h : ((childLH thetaAboveCell00012033)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell00012033) h
theorem e24KC2ThetaAboveLeaf000120332 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell00012033) = true := by
  have h : ((childHL thetaAboveCell00012033)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell00012033) h
theorem e24KC2ThetaAboveLeaf000120333 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell00012033) = true := by
  have h : ((childHH thetaAboveCell00012033)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell00012033) h
theorem e24KC2ThetaAboveLeaf0001210 :
    adaptiveCoverCheck 12 (childLL (childLH (childHL thetaAboveCell0001))) = true := by
  have h : ((childLL (childLH (childHL thetaAboveCell0001)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLH (childHL thetaAboveCell0001))) h
theorem e24KC2ThetaAboveLeaf0001211 :
    adaptiveCoverCheck 12 (childLH (childLH (childHL thetaAboveCell0001))) = true := by
  have h : ((childLH (childLH (childHL thetaAboveCell0001)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLH (childHL thetaAboveCell0001))) h
theorem e24KC2ThetaAboveLeaf00012120 :
    adaptiveCoverCheck 11 thetaAboveCell00012120 = true := by
  have h : (thetaAboveCell00012120).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00012120 h
theorem e24KC2ThetaAboveLeaf00012121 :
    adaptiveCoverCheck 11 thetaAboveCell00012121 = true := by
  have h : (thetaAboveCell00012121).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00012121 h
theorem e24KC2ThetaAboveLeaf000121220 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell00012122) = true := by
  have h : ((childLL thetaAboveCell00012122)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell00012122) h
theorem e24KC2ThetaAboveLeaf000121221 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell00012122) = true := by
  have h : ((childLH thetaAboveCell00012122)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell00012122) h
theorem e24KC2ThetaAboveLeaf000121222 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell00012122) = true := by
  have h : ((childHL thetaAboveCell00012122)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell00012122) h
theorem e24KC2ThetaAboveLeaf000121223 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell00012122) = true := by
  have h : ((childHH thetaAboveCell00012122)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell00012122) h
theorem e24KC2ThetaAboveLeaf000121230 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell00012123) = true := by
  have h : ((childLL thetaAboveCell00012123)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell00012123) h
theorem e24KC2ThetaAboveLeaf000121231 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell00012123) = true := by
  have h : ((childLH thetaAboveCell00012123)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell00012123) h
theorem e24KC2ThetaAboveLeaf000121232 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell00012123) = true := by
  have h : ((childHL thetaAboveCell00012123)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell00012123) h
theorem e24KC2ThetaAboveLeaf000121233 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell00012123) = true := by
  have h : ((childHH thetaAboveCell00012123)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell00012123) h
theorem e24KC2ThetaAboveLeaf00012130 :
    adaptiveCoverCheck 11 thetaAboveCell00012130 = true := by
  have h : (thetaAboveCell00012130).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00012130 h
theorem e24KC2ThetaAboveLeaf00012131 :
    adaptiveCoverCheck 11 thetaAboveCell00012131 = true := by
  have h : (thetaAboveCell00012131).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00012131 h
theorem e24KC2ThetaAboveLeaf000121320 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell00012132) = true := by
  have h : ((childLL thetaAboveCell00012132)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell00012132) h
theorem e24KC2ThetaAboveLeaf000121321 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell00012132) = true := by
  have h : ((childLH thetaAboveCell00012132)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell00012132) h
theorem e24KC2ThetaAboveLeaf000121322 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell00012132) = true := by
  have h : ((childHL thetaAboveCell00012132)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell00012132) h
theorem e24KC2ThetaAboveLeaf000121323 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell00012132) = true := by
  have h : ((childHH thetaAboveCell00012132)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell00012132) h
theorem e24KC2ThetaAboveLeaf000121330 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell00012133) = true := by
  have h : ((childLL thetaAboveCell00012133)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell00012133) h
theorem e24KC2ThetaAboveLeaf000121331 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell00012133) = true := by
  have h : ((childLH thetaAboveCell00012133)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell00012133) h
theorem e24KC2ThetaAboveLeaf000121332 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell00012133) = true := by
  have h : ((childHL thetaAboveCell00012133)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell00012133) h
theorem e24KC2ThetaAboveLeaf000121333 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell00012133) = true := by
  have h : ((childHH thetaAboveCell00012133)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell00012133) h
theorem e24KC2ThetaAboveLeaf0001220000 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell00012200)) = true := by
  have h : ((childLL (childLL thetaAboveCell00012200))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell00012200)) h
theorem e24KC2ThetaAboveLeaf0001220001 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell00012200)) = true := by
  have h : ((childLH (childLL thetaAboveCell00012200))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell00012200)) h
theorem e24KC2ThetaAboveLeaf0001220010 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell00012200)) = true := by
  have h : ((childLL (childLH thetaAboveCell00012200))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell00012200)) h
theorem e24KC2ThetaAboveLeaf0001220011 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell00012200)) = true := by
  have h : ((childLH (childLH thetaAboveCell00012200))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell00012200)) h
theorem e24KC2ThetaAboveLeaf0001220100 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell00012201)) = true := by
  have h : ((childLL (childLL thetaAboveCell00012201))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell00012201)) h
theorem e24KC2ThetaAboveLeaf0001220101 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell00012201)) = true := by
  have h : ((childLH (childLL thetaAboveCell00012201))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell00012201)) h
theorem e24KC2ThetaAboveLeaf0001220110 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell00012201)) = true := by
  have h : ((childLL (childLH thetaAboveCell00012201))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell00012201)) h
theorem e24KC2ThetaAboveLeaf0001220111 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell00012201)) = true := by
  have h : ((childLH (childLH thetaAboveCell00012201))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell00012201)) h
theorem e24KC2ThetaAboveLeaf0001220200 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell00012202)) = true := by
  have h : ((childLL (childLL thetaAboveCell00012202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell00012202)) h
theorem e24KC2ThetaAboveLeaf0001220201 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell00012202)) = true := by
  have h : ((childLH (childLL thetaAboveCell00012202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell00012202)) h
theorem e24KC2ThetaAboveLeaf0001220202 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell00012202)) = true := by
  have h : ((childHL (childLL thetaAboveCell00012202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell00012202)) h
theorem e24KC2ThetaAboveLeaf0001220203 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell00012202)) = true := by
  have h : ((childHH (childLL thetaAboveCell00012202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell00012202)) h
theorem e24KC2ThetaAboveLeaf0001220210 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell00012202)) = true := by
  have h : ((childLL (childLH thetaAboveCell00012202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell00012202)) h
theorem e24KC2ThetaAboveLeaf0001220211 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell00012202)) = true := by
  have h : ((childLH (childLH thetaAboveCell00012202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell00012202)) h
theorem e24KC2ThetaAboveLeaf0001220212 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell00012202)) = true := by
  have h : ((childHL (childLH thetaAboveCell00012202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell00012202)) h
theorem e24KC2ThetaAboveLeaf0001220213 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell00012202)) = true := by
  have h : ((childHH (childLH thetaAboveCell00012202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell00012202)) h
theorem e24KC2ThetaAboveLeaf000122022 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell00012202) = true := by
  have h : ((childHL thetaAboveCell00012202)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell00012202) h
theorem e24KC2ThetaAboveLeaf000122023 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell00012202) = true := by
  have h : ((childHH thetaAboveCell00012202)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell00012202) h
theorem e24KC2ThetaAboveLeaf0001220300 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell00012203)) = true := by
  have h : ((childLL (childLL thetaAboveCell00012203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell00012203)) h
theorem e24KC2ThetaAboveLeaf0001220301 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell00012203)) = true := by
  have h : ((childLH (childLL thetaAboveCell00012203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell00012203)) h
theorem e24KC2ThetaAboveLeaf0001220302 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell00012203)) = true := by
  have h : ((childHL (childLL thetaAboveCell00012203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell00012203)) h
theorem e24KC2ThetaAboveLeaf0001220303 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell00012203)) = true := by
  have h : ((childHH (childLL thetaAboveCell00012203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell00012203)) h
theorem e24KC2ThetaAboveLeaf0001220310 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell00012203)) = true := by
  have h : ((childLL (childLH thetaAboveCell00012203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell00012203)) h
theorem e24KC2ThetaAboveLeaf0001220311 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell00012203)) = true := by
  have h : ((childLH (childLH thetaAboveCell00012203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell00012203)) h
theorem e24KC2ThetaAboveLeaf0001220312 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell00012203)) = true := by
  have h : ((childHL (childLH thetaAboveCell00012203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell00012203)) h
theorem e24KC2ThetaAboveLeaf0001220313 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell00012203)) = true := by
  have h : ((childHH (childLH thetaAboveCell00012203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell00012203)) h
theorem e24KC2ThetaAboveLeaf000122032 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell00012203) = true := by
  have h : ((childHL thetaAboveCell00012203)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell00012203) h
theorem e24KC2ThetaAboveLeaf000122033 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell00012203) = true := by
  have h : ((childHH thetaAboveCell00012203)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell00012203) h
theorem e24KC2ThetaAboveLeaf0001221000 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell00012210)) = true := by
  have h : ((childLL (childLL thetaAboveCell00012210))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell00012210)) h
theorem e24KC2ThetaAboveLeaf0001221001 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell00012210)) = true := by
  have h : ((childLH (childLL thetaAboveCell00012210))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell00012210)) h
theorem e24KC2ThetaAboveLeaf0001221010 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell00012210)) = true := by
  have h : ((childLL (childLH thetaAboveCell00012210))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell00012210)) h
theorem e24KC2ThetaAboveLeaf0001221011 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell00012210)) = true := by
  have h : ((childLH (childLH thetaAboveCell00012210))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell00012210)) h
theorem e24KC2ThetaAboveLeaf0001221100 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell00012211)) = true := by
  have h : ((childLL (childLL thetaAboveCell00012211))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell00012211)) h
theorem e24KC2ThetaAboveLeaf0001221101 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell00012211)) = true := by
  have h : ((childLH (childLL thetaAboveCell00012211))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell00012211)) h
theorem e24KC2ThetaAboveLeaf0001221110 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell00012211)) = true := by
  have h : ((childLL (childLH thetaAboveCell00012211))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell00012211)) h
theorem e24KC2ThetaAboveLeaf0001221111 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell00012211)) = true := by
  have h : ((childLH (childLH thetaAboveCell00012211))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell00012211)) h
theorem e24KC2ThetaAboveLeaf0001221200 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell00012212)) = true := by
  have h : ((childLL (childLL thetaAboveCell00012212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell00012212)) h
theorem e24KC2ThetaAboveLeaf0001221201 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell00012212)) = true := by
  have h : ((childLH (childLL thetaAboveCell00012212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell00012212)) h
theorem e24KC2ThetaAboveLeaf0001221202 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell00012212)) = true := by
  have h : ((childHL (childLL thetaAboveCell00012212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell00012212)) h
theorem e24KC2ThetaAboveLeaf0001221203 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell00012212)) = true := by
  have h : ((childHH (childLL thetaAboveCell00012212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell00012212)) h
theorem e24KC2ThetaAboveLeaf0001221210 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell00012212)) = true := by
  have h : ((childLL (childLH thetaAboveCell00012212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell00012212)) h
theorem e24KC2ThetaAboveLeaf0001221211 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell00012212)) = true := by
  have h : ((childLH (childLH thetaAboveCell00012212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell00012212)) h
theorem e24KC2ThetaAboveLeaf0001221212 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell00012212)) = true := by
  have h : ((childHL (childLH thetaAboveCell00012212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell00012212)) h
theorem e24KC2ThetaAboveLeaf0001221213 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell00012212)) = true := by
  have h : ((childHH (childLH thetaAboveCell00012212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell00012212)) h
theorem e24KC2ThetaAboveLeaf000122122 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell00012212) = true := by
  have h : ((childHL thetaAboveCell00012212)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell00012212) h
theorem e24KC2ThetaAboveLeaf000122123 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell00012212) = true := by
  have h : ((childHH thetaAboveCell00012212)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell00012212) h
theorem e24KC2ThetaAboveLeaf0001221300 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell00012213)) = true := by
  have h : ((childLL (childLL thetaAboveCell00012213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell00012213)) h
theorem e24KC2ThetaAboveLeaf0001221301 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell00012213)) = true := by
  have h : ((childLH (childLL thetaAboveCell00012213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell00012213)) h
theorem e24KC2ThetaAboveLeaf0001221302 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell00012213)) = true := by
  have h : ((childHL (childLL thetaAboveCell00012213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell00012213)) h
theorem e24KC2ThetaAboveLeaf0001221303 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell00012213)) = true := by
  have h : ((childHH (childLL thetaAboveCell00012213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell00012213)) h
theorem e24KC2ThetaAboveLeaf0001221310 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell00012213)) = true := by
  have h : ((childLL (childLH thetaAboveCell00012213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell00012213)) h
theorem e24KC2ThetaAboveLeaf0001221311 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell00012213)) = true := by
  have h : ((childLH (childLH thetaAboveCell00012213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell00012213)) h
theorem e24KC2ThetaAboveLeaf0001221312 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell00012213)) = true := by
  have h : ((childHL (childLH thetaAboveCell00012213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell00012213)) h
theorem e24KC2ThetaAboveLeaf0001221313 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell00012213)) = true := by
  have h : ((childHH (childLH thetaAboveCell00012213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell00012213)) h
theorem e24KC2ThetaAboveLeaf000122132 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell00012213) = true := by
  have h : ((childHL thetaAboveCell00012213)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell00012213) h
theorem e24KC2ThetaAboveLeaf000122133 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell00012213) = true := by
  have h : ((childHH thetaAboveCell00012213)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell00012213) h
theorem e24KC2ThetaAboveLeaf00012220 :
    adaptiveCoverCheck 11 thetaAboveCell00012220 = true := by
  have h : (thetaAboveCell00012220).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00012220 h
theorem e24KC2ThetaAboveLeaf00012221 :
    adaptiveCoverCheck 11 thetaAboveCell00012221 = true := by
  have h : (thetaAboveCell00012221).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00012221 h
theorem e24KC2ThetaAboveLeaf00012222 :
    adaptiveCoverCheck 11 thetaAboveCell00012222 = true := by
  have h : (thetaAboveCell00012222).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00012222 h
theorem e24KC2ThetaAboveLeaf00012223 :
    adaptiveCoverCheck 11 thetaAboveCell00012223 = true := by
  have h : (thetaAboveCell00012223).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00012223 h
theorem e24KC2ThetaAboveLeaf00012230 :
    adaptiveCoverCheck 11 thetaAboveCell00012230 = true := by
  have h : (thetaAboveCell00012230).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00012230 h
theorem e24KC2ThetaAboveLeaf00012231 :
    adaptiveCoverCheck 11 thetaAboveCell00012231 = true := by
  have h : (thetaAboveCell00012231).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00012231 h
theorem e24KC2ThetaAboveLeaf00012232 :
    adaptiveCoverCheck 11 thetaAboveCell00012232 = true := by
  have h : (thetaAboveCell00012232).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00012232 h
theorem e24KC2ThetaAboveLeaf00012233 :
    adaptiveCoverCheck 11 thetaAboveCell00012233 = true := by
  have h : (thetaAboveCell00012233).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00012233 h
theorem e24KC2ThetaAboveLeaf0001230000 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell00012300)) = true := by
  have h : ((childLL (childLL thetaAboveCell00012300))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell00012300)) h
theorem e24KC2ThetaAboveLeaf0001230001 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell00012300)) = true := by
  have h : ((childLH (childLL thetaAboveCell00012300))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell00012300)) h
theorem e24KC2ThetaAboveLeaf0001230010 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell00012300)) = true := by
  have h : ((childLL (childLH thetaAboveCell00012300))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell00012300)) h
theorem e24KC2ThetaAboveLeaf0001230011 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell00012300)) = true := by
  have h : ((childLH (childLH thetaAboveCell00012300))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell00012300)) h
theorem e24KC2ThetaAboveLeaf0001230100 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell00012301)) = true := by
  have h : ((childLL (childLL thetaAboveCell00012301))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell00012301)) h
theorem e24KC2ThetaAboveLeaf0001230101 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell00012301)) = true := by
  have h : ((childLH (childLL thetaAboveCell00012301))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell00012301)) h
theorem e24KC2ThetaAboveLeaf0001230110 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell00012301)) = true := by
  have h : ((childLL (childLH thetaAboveCell00012301))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell00012301)) h
theorem e24KC2ThetaAboveLeaf0001230111 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell00012301)) = true := by
  have h : ((childLH (childLH thetaAboveCell00012301))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell00012301)) h
theorem e24KC2ThetaAboveLeaf0001230200 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell00012302)) = true := by
  have h : ((childLL (childLL thetaAboveCell00012302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell00012302)) h
theorem e24KC2ThetaAboveLeaf0001230201 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell00012302)) = true := by
  have h : ((childLH (childLL thetaAboveCell00012302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell00012302)) h
theorem e24KC2ThetaAboveLeaf0001230202 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell00012302)) = true := by
  have h : ((childHL (childLL thetaAboveCell00012302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell00012302)) h
theorem e24KC2ThetaAboveLeaf0001230203 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell00012302)) = true := by
  have h : ((childHH (childLL thetaAboveCell00012302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell00012302)) h
theorem e24KC2ThetaAboveLeaf0001230210 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell00012302)) = true := by
  have h : ((childLL (childLH thetaAboveCell00012302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell00012302)) h
theorem e24KC2ThetaAboveLeaf0001230211 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell00012302)) = true := by
  have h : ((childLH (childLH thetaAboveCell00012302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell00012302)) h
theorem e24KC2ThetaAboveLeaf0001230212 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell00012302)) = true := by
  have h : ((childHL (childLH thetaAboveCell00012302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell00012302)) h
theorem e24KC2ThetaAboveLeaf0001230213 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell00012302)) = true := by
  have h : ((childHH (childLH thetaAboveCell00012302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell00012302)) h
theorem e24KC2ThetaAboveLeaf000123022 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell00012302) = true := by
  have h : ((childHL thetaAboveCell00012302)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell00012302) h
theorem e24KC2ThetaAboveLeaf000123023 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell00012302) = true := by
  have h : ((childHH thetaAboveCell00012302)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell00012302) h
theorem e24KC2ThetaAboveLeaf0001230300 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell00012303)) = true := by
  have h : ((childLL (childLL thetaAboveCell00012303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell00012303)) h
theorem e24KC2ThetaAboveLeaf0001230301 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell00012303)) = true := by
  have h : ((childLH (childLL thetaAboveCell00012303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell00012303)) h
theorem e24KC2ThetaAboveLeaf0001230302 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell00012303)) = true := by
  have h : ((childHL (childLL thetaAboveCell00012303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell00012303)) h
theorem e24KC2ThetaAboveLeaf0001230303 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell00012303)) = true := by
  have h : ((childHH (childLL thetaAboveCell00012303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell00012303)) h
theorem e24KC2ThetaAboveLeaf0001230310 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell00012303)) = true := by
  have h : ((childLL (childLH thetaAboveCell00012303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell00012303)) h
theorem e24KC2ThetaAboveLeaf0001230311 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell00012303)) = true := by
  have h : ((childLH (childLH thetaAboveCell00012303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell00012303)) h
theorem e24KC2ThetaAboveLeaf0001230312 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell00012303)) = true := by
  have h : ((childHL (childLH thetaAboveCell00012303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell00012303)) h
theorem e24KC2ThetaAboveLeaf0001230313 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell00012303)) = true := by
  have h : ((childHH (childLH thetaAboveCell00012303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell00012303)) h
theorem e24KC2ThetaAboveLeaf000123032 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell00012303) = true := by
  have h : ((childHL thetaAboveCell00012303)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell00012303) h
theorem e24KC2ThetaAboveLeaf000123033 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell00012303) = true := by
  have h : ((childHH thetaAboveCell00012303)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell00012303) h
theorem e24KC2ThetaAboveLeaf0001231000 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell00012310)) = true := by
  have h : ((childLL (childLL thetaAboveCell00012310))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell00012310)) h
theorem e24KC2ThetaAboveLeaf0001231001 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell00012310)) = true := by
  have h : ((childLH (childLL thetaAboveCell00012310))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell00012310)) h
theorem e24KC2ThetaAboveLeaf0001231003 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell00012310)) = true := by
  have h : ((childHH (childLL thetaAboveCell00012310))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell00012310)) h
theorem e24KC2ThetaAboveLeaf0001231010 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell00012310)) = true := by
  have h : ((childLL (childLH thetaAboveCell00012310))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell00012310)) h
theorem e24KC2ThetaAboveLeaf0001231011 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell00012310)) = true := by
  have h : ((childLH (childLH thetaAboveCell00012310))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell00012310)) h
theorem e24KC2ThetaAboveLeaf0001231012 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell00012310)) = true := by
  have h : ((childHL (childLH thetaAboveCell00012310))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell00012310)) h
theorem e24KC2ThetaAboveLeaf0001231013 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell00012310)) = true := by
  have h : ((childHH (childLH thetaAboveCell00012310))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell00012310)) h
theorem e24KC2ThetaAboveLeaf0001231100 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell00012311)) = true := by
  have h : ((childLL (childLL thetaAboveCell00012311))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell00012311)) h
theorem e24KC2ThetaAboveLeaf0001231101 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell00012311)) = true := by
  have h : ((childLH (childLL thetaAboveCell00012311))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell00012311)) h
theorem e24KC2ThetaAboveLeaf0001231102 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell00012311)) = true := by
  have h : ((childHL (childLL thetaAboveCell00012311))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell00012311)) h
theorem e24KC2ThetaAboveLeaf0001231103 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell00012311)) = true := by
  have h : ((childHH (childLL thetaAboveCell00012311))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell00012311)) h
theorem e24KC2ThetaAboveLeaf0001231110 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell00012311)) = true := by
  have h : ((childLL (childLH thetaAboveCell00012311))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell00012311)) h
theorem e24KC2ThetaAboveLeaf0001231111 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell00012311)) = true := by
  have h : ((childLH (childLH thetaAboveCell00012311))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell00012311)) h
theorem e24KC2ThetaAboveLeaf0001231112 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell00012311)) = true := by
  have h : ((childHL (childLH thetaAboveCell00012311))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell00012311)) h
theorem e24KC2ThetaAboveLeaf0001231113 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell00012311)) = true := by
  have h : ((childHH (childLH thetaAboveCell00012311))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell00012311)) h
theorem e24KC2ThetaAboveLeaf0001231200 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell00012312)) = true := by
  have h : ((childLL (childLL thetaAboveCell00012312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell00012312)) h
theorem e24KC2ThetaAboveLeaf0001231201 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell00012312)) = true := by
  have h : ((childLH (childLL thetaAboveCell00012312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell00012312)) h
theorem e24KC2ThetaAboveLeaf0001231202 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell00012312)) = true := by
  have h : ((childHL (childLL thetaAboveCell00012312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell00012312)) h
theorem e24KC2ThetaAboveLeaf0001231203 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell00012312)) = true := by
  have h : ((childHH (childLL thetaAboveCell00012312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell00012312)) h
theorem e24KC2ThetaAboveLeaf0001231210 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell00012312)) = true := by
  have h : ((childLL (childLH thetaAboveCell00012312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell00012312)) h
theorem e24KC2ThetaAboveLeaf0001231211 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell00012312)) = true := by
  have h : ((childLH (childLH thetaAboveCell00012312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell00012312)) h
theorem e24KC2ThetaAboveLeaf0001231212 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell00012312)) = true := by
  have h : ((childHL (childLH thetaAboveCell00012312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell00012312)) h
theorem e24KC2ThetaAboveLeaf0001231213 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell00012312)) = true := by
  have h : ((childHH (childLH thetaAboveCell00012312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell00012312)) h
theorem e24KC2ThetaAboveLeaf000123122 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell00012312) = true := by
  have h : ((childHL thetaAboveCell00012312)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell00012312) h
theorem e24KC2ThetaAboveLeaf000123123 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell00012312) = true := by
  have h : ((childHH thetaAboveCell00012312)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell00012312) h
theorem e24KC2ThetaAboveLeaf0001231300 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell00012313)) = true := by
  have h : ((childLL (childLL thetaAboveCell00012313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell00012313)) h
theorem e24KC2ThetaAboveLeaf0001231301 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell00012313)) = true := by
  have h : ((childLH (childLL thetaAboveCell00012313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell00012313)) h
theorem e24KC2ThetaAboveLeaf0001231302 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell00012313)) = true := by
  have h : ((childHL (childLL thetaAboveCell00012313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell00012313)) h
theorem e24KC2ThetaAboveLeaf0001231303 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell00012313)) = true := by
  have h : ((childHH (childLL thetaAboveCell00012313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell00012313)) h
theorem e24KC2ThetaAboveLeaf0001231310 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell00012313)) = true := by
  have h : ((childLL (childLH thetaAboveCell00012313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell00012313)) h
theorem e24KC2ThetaAboveLeaf0001231311 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell00012313)) = true := by
  have h : ((childLH (childLH thetaAboveCell00012313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell00012313)) h
theorem e24KC2ThetaAboveLeaf0001231312 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell00012313)) = true := by
  have h : ((childHL (childLH thetaAboveCell00012313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell00012313)) h
theorem e24KC2ThetaAboveLeaf0001231313 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell00012313)) = true := by
  have h : ((childHH (childLH thetaAboveCell00012313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell00012313)) h
theorem e24KC2ThetaAboveLeaf000123132 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell00012313) = true := by
  have h : ((childHL thetaAboveCell00012313)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell00012313) h
theorem e24KC2ThetaAboveLeaf000123133 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell00012313) = true := by
  have h : ((childHH thetaAboveCell00012313)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell00012313) h
theorem e24KC2ThetaAboveLeaf00012320 :
    adaptiveCoverCheck 11 thetaAboveCell00012320 = true := by
  have h : (thetaAboveCell00012320).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00012320 h
theorem e24KC2ThetaAboveLeaf00012321 :
    adaptiveCoverCheck 11 thetaAboveCell00012321 = true := by
  have h : (thetaAboveCell00012321).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00012321 h
theorem e24KC2ThetaAboveLeaf00012322 :
    adaptiveCoverCheck 11 thetaAboveCell00012322 = true := by
  have h : (thetaAboveCell00012322).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00012322 h
theorem e24KC2ThetaAboveLeaf00012323 :
    adaptiveCoverCheck 11 thetaAboveCell00012323 = true := by
  have h : (thetaAboveCell00012323).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00012323 h
theorem e24KC2ThetaAboveLeaf00012330 :
    adaptiveCoverCheck 11 thetaAboveCell00012330 = true := by
  have h : (thetaAboveCell00012330).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00012330 h
theorem e24KC2ThetaAboveLeaf00012331 :
    adaptiveCoverCheck 11 thetaAboveCell00012331 = true := by
  have h : (thetaAboveCell00012331).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00012331 h
theorem e24KC2ThetaAboveLeaf00012332 :
    adaptiveCoverCheck 11 thetaAboveCell00012332 = true := by
  have h : (thetaAboveCell00012332).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00012332 h
theorem e24KC2ThetaAboveLeaf00012333 :
    adaptiveCoverCheck 11 thetaAboveCell00012333 = true := by
  have h : (thetaAboveCell00012333).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00012333 h
theorem e24KC2ThetaAboveLeaf0001300 :
    adaptiveCoverCheck 12 (childLL (childLL (childHH thetaAboveCell0001))) = true := by
  have h : ((childLL (childLL (childHH thetaAboveCell0001)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLL (childHH thetaAboveCell0001))) h
theorem e24KC2ThetaAboveLeaf0001301 :
    adaptiveCoverCheck 12 (childLH (childLL (childHH thetaAboveCell0001))) = true := by
  have h : ((childLH (childLL (childHH thetaAboveCell0001)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLL (childHH thetaAboveCell0001))) h
theorem e24KC2ThetaAboveLeaf00013020 :
    adaptiveCoverCheck 11 thetaAboveCell00013020 = true := by
  have h : (thetaAboveCell00013020).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00013020 h
theorem e24KC2ThetaAboveLeaf00013021 :
    adaptiveCoverCheck 11 thetaAboveCell00013021 = true := by
  have h : (thetaAboveCell00013021).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00013021 h
theorem e24KC2ThetaAboveLeaf000130220 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell00013022) = true := by
  have h : ((childLL thetaAboveCell00013022)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell00013022) h
theorem e24KC2ThetaAboveLeaf000130221 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell00013022) = true := by
  have h : ((childLH thetaAboveCell00013022)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell00013022) h
theorem e24KC2ThetaAboveLeaf000130222 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell00013022) = true := by
  have h : ((childHL thetaAboveCell00013022)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell00013022) h
theorem e24KC2ThetaAboveLeaf000130223 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell00013022) = true := by
  have h : ((childHH thetaAboveCell00013022)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell00013022) h
theorem e24KC2ThetaAboveLeaf000130230 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell00013023) = true := by
  have h : ((childLL thetaAboveCell00013023)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell00013023) h
theorem e24KC2ThetaAboveLeaf000130231 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell00013023) = true := by
  have h : ((childLH thetaAboveCell00013023)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell00013023) h
theorem e24KC2ThetaAboveLeaf000130232 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell00013023) = true := by
  have h : ((childHL thetaAboveCell00013023)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell00013023) h
theorem e24KC2ThetaAboveLeaf000130233 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell00013023) = true := by
  have h : ((childHH thetaAboveCell00013023)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell00013023) h
theorem e24KC2ThetaAboveLeaf00013030 :
    adaptiveCoverCheck 11 thetaAboveCell00013030 = true := by
  have h : (thetaAboveCell00013030).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00013030 h
theorem e24KC2ThetaAboveLeaf00013031 :
    adaptiveCoverCheck 11 thetaAboveCell00013031 = true := by
  have h : (thetaAboveCell00013031).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00013031 h
theorem e24KC2ThetaAboveLeaf000130320 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell00013032) = true := by
  have h : ((childLL thetaAboveCell00013032)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell00013032) h
theorem e24KC2ThetaAboveLeaf000130321 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell00013032) = true := by
  have h : ((childLH thetaAboveCell00013032)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell00013032) h
theorem e24KC2ThetaAboveLeaf000130322 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell00013032) = true := by
  have h : ((childHL thetaAboveCell00013032)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell00013032) h
theorem e24KC2ThetaAboveLeaf000130323 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell00013032) = true := by
  have h : ((childHH thetaAboveCell00013032)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell00013032) h
theorem e24KC2ThetaAboveLeaf000130330 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell00013033) = true := by
  have h : ((childLL thetaAboveCell00013033)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell00013033) h
theorem e24KC2ThetaAboveLeaf000130331 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell00013033) = true := by
  have h : ((childLH thetaAboveCell00013033)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell00013033) h
theorem e24KC2ThetaAboveLeaf000130332 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell00013033) = true := by
  have h : ((childHL thetaAboveCell00013033)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell00013033) h
theorem e24KC2ThetaAboveLeaf000130333 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell00013033) = true := by
  have h : ((childHH thetaAboveCell00013033)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell00013033) h
theorem e24KC2ThetaAboveLeaf0001310 :
    adaptiveCoverCheck 12 (childLL (childLH (childHH thetaAboveCell0001))) = true := by
  have h : ((childLL (childLH (childHH thetaAboveCell0001)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLH (childHH thetaAboveCell0001))) h
theorem e24KC2ThetaAboveLeaf0001311 :
    adaptiveCoverCheck 12 (childLH (childLH (childHH thetaAboveCell0001))) = true := by
  have h : ((childLH (childLH (childHH thetaAboveCell0001)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLH (childHH thetaAboveCell0001))) h
theorem e24KC2ThetaAboveLeaf00013120 :
    adaptiveCoverCheck 11 thetaAboveCell00013120 = true := by
  have h : (thetaAboveCell00013120).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00013120 h
theorem e24KC2ThetaAboveLeaf00013121 :
    adaptiveCoverCheck 11 thetaAboveCell00013121 = true := by
  have h : (thetaAboveCell00013121).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00013121 h
theorem e24KC2ThetaAboveLeaf000131220 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell00013122) = true := by
  have h : ((childLL thetaAboveCell00013122)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell00013122) h
theorem e24KC2ThetaAboveLeaf000131221 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell00013122) = true := by
  have h : ((childLH thetaAboveCell00013122)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell00013122) h
theorem e24KC2ThetaAboveLeaf000131222 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell00013122) = true := by
  have h : ((childHL thetaAboveCell00013122)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell00013122) h
theorem e24KC2ThetaAboveLeaf000131223 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell00013122) = true := by
  have h : ((childHH thetaAboveCell00013122)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell00013122) h
theorem e24KC2ThetaAboveLeaf000131230 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell00013123) = true := by
  have h : ((childLL thetaAboveCell00013123)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell00013123) h
theorem e24KC2ThetaAboveLeaf000131231 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell00013123) = true := by
  have h : ((childLH thetaAboveCell00013123)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell00013123) h
theorem e24KC2ThetaAboveLeaf000131232 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell00013123) = true := by
  have h : ((childHL thetaAboveCell00013123)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell00013123) h
theorem e24KC2ThetaAboveLeaf000131233 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell00013123) = true := by
  have h : ((childHH thetaAboveCell00013123)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell00013123) h
theorem e24KC2ThetaAboveLeaf00013130 :
    adaptiveCoverCheck 11 thetaAboveCell00013130 = true := by
  have h : (thetaAboveCell00013130).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00013130 h
theorem e24KC2ThetaAboveLeaf00013131 :
    adaptiveCoverCheck 11 thetaAboveCell00013131 = true := by
  have h : (thetaAboveCell00013131).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00013131 h
theorem e24KC2ThetaAboveLeaf000131320 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell00013132) = true := by
  have h : ((childLL thetaAboveCell00013132)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell00013132) h
theorem e24KC2ThetaAboveLeaf000131321 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell00013132) = true := by
  have h : ((childLH thetaAboveCell00013132)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell00013132) h
theorem e24KC2ThetaAboveLeaf000131322 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell00013132) = true := by
  have h : ((childHL thetaAboveCell00013132)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell00013132) h
theorem e24KC2ThetaAboveLeaf000131323 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell00013132) = true := by
  have h : ((childHH thetaAboveCell00013132)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell00013132) h
theorem e24KC2ThetaAboveLeaf000131330 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell00013133) = true := by
  have h : ((childLL thetaAboveCell00013133)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell00013133) h
theorem e24KC2ThetaAboveLeaf000131331 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell00013133) = true := by
  have h : ((childLH thetaAboveCell00013133)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell00013133) h
theorem e24KC2ThetaAboveLeaf000131332 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell00013133) = true := by
  have h : ((childHL thetaAboveCell00013133)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell00013133) h
theorem e24KC2ThetaAboveLeaf000131333 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell00013133) = true := by
  have h : ((childHH thetaAboveCell00013133)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell00013133) h
theorem e24KC2ThetaAboveLeaf0001320000 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell00013200)) = true := by
  have h : ((childLL (childLL thetaAboveCell00013200))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell00013200)) h
theorem e24KC2ThetaAboveLeaf0001320001 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell00013200)) = true := by
  have h : ((childLH (childLL thetaAboveCell00013200))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell00013200)) h
theorem e24KC2ThetaAboveLeaf0001320002 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell00013200)) = true := by
  have h : ((childHL (childLL thetaAboveCell00013200))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell00013200)) h
theorem e24KC2ThetaAboveLeaf0001320003 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell00013200)) = true := by
  have h : ((childHH (childLL thetaAboveCell00013200))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell00013200)) h
theorem e24KC2ThetaAboveLeaf0001320010 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell00013200)) = true := by
  have h : ((childLL (childLH thetaAboveCell00013200))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell00013200)) h
theorem e24KC2ThetaAboveLeaf0001320011 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell00013200)) = true := by
  have h : ((childLH (childLH thetaAboveCell00013200))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell00013200)) h
theorem e24KC2ThetaAboveLeaf0001320012 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell00013200)) = true := by
  have h : ((childHL (childLH thetaAboveCell00013200))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell00013200)) h
theorem e24KC2ThetaAboveLeaf0001320013 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell00013200)) = true := by
  have h : ((childHH (childLH thetaAboveCell00013200))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell00013200)) h
theorem e24KC2ThetaAboveLeaf0001320100 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell00013201)) = true := by
  have h : ((childLL (childLL thetaAboveCell00013201))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell00013201)) h
theorem e24KC2ThetaAboveLeaf0001320101 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell00013201)) = true := by
  have h : ((childLH (childLL thetaAboveCell00013201))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell00013201)) h
theorem e24KC2ThetaAboveLeaf0001320102 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell00013201)) = true := by
  have h : ((childHL (childLL thetaAboveCell00013201))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell00013201)) h
theorem e24KC2ThetaAboveLeaf0001320103 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell00013201)) = true := by
  have h : ((childHH (childLL thetaAboveCell00013201))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell00013201)) h
theorem e24KC2ThetaAboveLeaf0001320110 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell00013201)) = true := by
  have h : ((childLL (childLH thetaAboveCell00013201))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell00013201)) h
theorem e24KC2ThetaAboveLeaf0001320111 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell00013201)) = true := by
  have h : ((childLH (childLH thetaAboveCell00013201))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell00013201)) h
theorem e24KC2ThetaAboveLeaf0001320112 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell00013201)) = true := by
  have h : ((childHL (childLH thetaAboveCell00013201))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell00013201)) h
theorem e24KC2ThetaAboveLeaf0001320113 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell00013201)) = true := by
  have h : ((childHH (childLH thetaAboveCell00013201))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell00013201)) h
theorem e24KC2ThetaAboveLeaf0001320200 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell00013202)) = true := by
  have h : ((childLL (childLL thetaAboveCell00013202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell00013202)) h
theorem e24KC2ThetaAboveLeaf0001320201 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell00013202)) = true := by
  have h : ((childLH (childLL thetaAboveCell00013202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell00013202)) h
theorem e24KC2ThetaAboveLeaf0001320202 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell00013202)) = true := by
  have h : ((childHL (childLL thetaAboveCell00013202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell00013202)) h
theorem e24KC2ThetaAboveLeaf0001320203 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell00013202)) = true := by
  have h : ((childHH (childLL thetaAboveCell00013202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell00013202)) h
theorem e24KC2ThetaAboveLeaf0001320210 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell00013202)) = true := by
  have h : ((childLL (childLH thetaAboveCell00013202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell00013202)) h
theorem e24KC2ThetaAboveLeaf0001320211 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell00013202)) = true := by
  have h : ((childLH (childLH thetaAboveCell00013202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell00013202)) h
theorem e24KC2ThetaAboveLeaf0001320212 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell00013202)) = true := by
  have h : ((childHL (childLH thetaAboveCell00013202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell00013202)) h
theorem e24KC2ThetaAboveLeaf0001320213 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell00013202)) = true := by
  have h : ((childHH (childLH thetaAboveCell00013202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell00013202)) h
theorem e24KC2ThetaAboveLeaf000132022 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell00013202) = true := by
  have h : ((childHL thetaAboveCell00013202)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell00013202) h
theorem e24KC2ThetaAboveLeaf000132023 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell00013202) = true := by
  have h : ((childHH thetaAboveCell00013202)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell00013202) h
theorem e24KC2ThetaAboveLeaf0001320300 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell00013203)) = true := by
  have h : ((childLL (childLL thetaAboveCell00013203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell00013203)) h
theorem e24KC2ThetaAboveLeaf0001320301 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell00013203)) = true := by
  have h : ((childLH (childLL thetaAboveCell00013203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell00013203)) h
theorem e24KC2ThetaAboveLeaf0001320302 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell00013203)) = true := by
  have h : ((childHL (childLL thetaAboveCell00013203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell00013203)) h
theorem e24KC2ThetaAboveLeaf0001320303 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell00013203)) = true := by
  have h : ((childHH (childLL thetaAboveCell00013203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell00013203)) h
theorem e24KC2ThetaAboveLeaf0001320310 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell00013203)) = true := by
  have h : ((childLL (childLH thetaAboveCell00013203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell00013203)) h
theorem e24KC2ThetaAboveLeaf0001320311 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell00013203)) = true := by
  have h : ((childLH (childLH thetaAboveCell00013203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell00013203)) h
theorem e24KC2ThetaAboveLeaf0001320312 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell00013203)) = true := by
  have h : ((childHL (childLH thetaAboveCell00013203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell00013203)) h
theorem e24KC2ThetaAboveLeaf0001320313 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell00013203)) = true := by
  have h : ((childHH (childLH thetaAboveCell00013203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell00013203)) h
theorem e24KC2ThetaAboveLeaf000132032 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell00013203) = true := by
  have h : ((childHL thetaAboveCell00013203)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell00013203) h
theorem e24KC2ThetaAboveLeaf000132033 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell00013203) = true := by
  have h : ((childHH thetaAboveCell00013203)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell00013203) h
theorem e24KC2ThetaAboveLeaf0001321000 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell00013210)) = true := by
  have h : ((childLL (childLL thetaAboveCell00013210))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell00013210)) h
theorem e24KC2ThetaAboveLeaf0001321001 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell00013210)) = true := by
  have h : ((childLH (childLL thetaAboveCell00013210))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell00013210)) h
theorem e24KC2ThetaAboveLeaf0001321002 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell00013210)) = true := by
  have h : ((childHL (childLL thetaAboveCell00013210))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell00013210)) h
theorem e24KC2ThetaAboveLeaf0001321003 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell00013210)) = true := by
  have h : ((childHH (childLL thetaAboveCell00013210))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell00013210)) h
theorem e24KC2ThetaAboveLeaf0001321010 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell00013210)) = true := by
  have h : ((childLL (childLH thetaAboveCell00013210))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell00013210)) h
theorem e24KC2ThetaAboveLeaf0001321011 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell00013210)) = true := by
  have h : ((childLH (childLH thetaAboveCell00013210))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell00013210)) h
theorem e24KC2ThetaAboveLeaf0001321012 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell00013210)) = true := by
  have h : ((childHL (childLH thetaAboveCell00013210))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell00013210)) h
theorem e24KC2ThetaAboveLeaf0001321013 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell00013210)) = true := by
  have h : ((childHH (childLH thetaAboveCell00013210))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell00013210)) h
theorem e24KC2ThetaAboveLeaf0001321100 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell00013211)) = true := by
  have h : ((childLL (childLL thetaAboveCell00013211))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell00013211)) h
theorem e24KC2ThetaAboveLeaf0001321101 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell00013211)) = true := by
  have h : ((childLH (childLL thetaAboveCell00013211))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell00013211)) h
theorem e24KC2ThetaAboveLeaf0001321102 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell00013211)) = true := by
  have h : ((childHL (childLL thetaAboveCell00013211))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell00013211)) h
theorem e24KC2ThetaAboveLeaf0001321103 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell00013211)) = true := by
  have h : ((childHH (childLL thetaAboveCell00013211))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell00013211)) h
theorem e24KC2ThetaAboveLeaf0001321110 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell00013211)) = true := by
  have h : ((childLL (childLH thetaAboveCell00013211))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell00013211)) h
theorem e24KC2ThetaAboveLeaf0001321111 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell00013211)) = true := by
  have h : ((childLH (childLH thetaAboveCell00013211))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell00013211)) h
theorem e24KC2ThetaAboveLeaf0001321112 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell00013211)) = true := by
  have h : ((childHL (childLH thetaAboveCell00013211))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell00013211)) h
theorem e24KC2ThetaAboveLeaf0001321113 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell00013211)) = true := by
  have h : ((childHH (childLH thetaAboveCell00013211))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell00013211)) h
theorem e24KC2ThetaAboveLeaf0001321200 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell00013212)) = true := by
  have h : ((childLL (childLL thetaAboveCell00013212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell00013212)) h
theorem e24KC2ThetaAboveLeaf0001321201 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell00013212)) = true := by
  have h : ((childLH (childLL thetaAboveCell00013212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell00013212)) h
theorem e24KC2ThetaAboveLeaf0001321202 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell00013212)) = true := by
  have h : ((childHL (childLL thetaAboveCell00013212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell00013212)) h
theorem e24KC2ThetaAboveLeaf0001321203 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell00013212)) = true := by
  have h : ((childHH (childLL thetaAboveCell00013212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell00013212)) h
theorem e24KC2ThetaAboveLeaf0001321210 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell00013212)) = true := by
  have h : ((childLL (childLH thetaAboveCell00013212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell00013212)) h
theorem e24KC2ThetaAboveLeaf0001321211 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell00013212)) = true := by
  have h : ((childLH (childLH thetaAboveCell00013212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell00013212)) h
theorem e24KC2ThetaAboveLeaf0001321212 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell00013212)) = true := by
  have h : ((childHL (childLH thetaAboveCell00013212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell00013212)) h
theorem e24KC2ThetaAboveLeaf0001321213 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell00013212)) = true := by
  have h : ((childHH (childLH thetaAboveCell00013212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell00013212)) h
theorem e24KC2ThetaAboveLeaf000132122 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell00013212) = true := by
  have h : ((childHL thetaAboveCell00013212)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell00013212) h
theorem e24KC2ThetaAboveLeaf000132123 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell00013212) = true := by
  have h : ((childHH thetaAboveCell00013212)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell00013212) h
theorem e24KC2ThetaAboveLeaf0001321300 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell00013213)) = true := by
  have h : ((childLL (childLL thetaAboveCell00013213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell00013213)) h
theorem e24KC2ThetaAboveLeaf0001321301 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell00013213)) = true := by
  have h : ((childLH (childLL thetaAboveCell00013213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell00013213)) h
theorem e24KC2ThetaAboveLeaf0001321302 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell00013213)) = true := by
  have h : ((childHL (childLL thetaAboveCell00013213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell00013213)) h
theorem e24KC2ThetaAboveLeaf0001321303 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell00013213)) = true := by
  have h : ((childHH (childLL thetaAboveCell00013213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell00013213)) h
theorem e24KC2ThetaAboveLeaf0001321310 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell00013213)) = true := by
  have h : ((childLL (childLH thetaAboveCell00013213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell00013213)) h
theorem e24KC2ThetaAboveLeaf0001321311 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell00013213)) = true := by
  have h : ((childLH (childLH thetaAboveCell00013213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell00013213)) h
theorem e24KC2ThetaAboveLeaf0001321312 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell00013213)) = true := by
  have h : ((childHL (childLH thetaAboveCell00013213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell00013213)) h
theorem e24KC2ThetaAboveLeaf0001321313 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell00013213)) = true := by
  have h : ((childHH (childLH thetaAboveCell00013213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell00013213)) h
theorem e24KC2ThetaAboveLeaf000132132 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell00013213) = true := by
  have h : ((childHL thetaAboveCell00013213)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell00013213) h
theorem e24KC2ThetaAboveLeaf000132133 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell00013213) = true := by
  have h : ((childHH thetaAboveCell00013213)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell00013213) h
theorem e24KC2ThetaAboveLeaf00013220 :
    adaptiveCoverCheck 11 thetaAboveCell00013220 = true := by
  have h : (thetaAboveCell00013220).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00013220 h
theorem e24KC2ThetaAboveLeaf00013221 :
    adaptiveCoverCheck 11 thetaAboveCell00013221 = true := by
  have h : (thetaAboveCell00013221).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00013221 h
theorem e24KC2ThetaAboveLeaf00013222 :
    adaptiveCoverCheck 11 thetaAboveCell00013222 = true := by
  have h : (thetaAboveCell00013222).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00013222 h
theorem e24KC2ThetaAboveLeaf00013223 :
    adaptiveCoverCheck 11 thetaAboveCell00013223 = true := by
  have h : (thetaAboveCell00013223).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00013223 h
theorem e24KC2ThetaAboveLeaf00013230 :
    adaptiveCoverCheck 11 thetaAboveCell00013230 = true := by
  have h : (thetaAboveCell00013230).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00013230 h
theorem e24KC2ThetaAboveLeaf00013231 :
    adaptiveCoverCheck 11 thetaAboveCell00013231 = true := by
  have h : (thetaAboveCell00013231).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00013231 h
theorem e24KC2ThetaAboveLeaf00013232 :
    adaptiveCoverCheck 11 thetaAboveCell00013232 = true := by
  have h : (thetaAboveCell00013232).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00013232 h
theorem e24KC2ThetaAboveLeaf00013233 :
    adaptiveCoverCheck 11 thetaAboveCell00013233 = true := by
  have h : (thetaAboveCell00013233).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00013233 h
theorem e24KC2ThetaAboveLeaf0001330000 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell00013300)) = true := by
  have h : ((childLL (childLL thetaAboveCell00013300))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell00013300)) h
theorem e24KC2ThetaAboveLeaf0001330001 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell00013300)) = true := by
  have h : ((childLH (childLL thetaAboveCell00013300))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell00013300)) h
theorem e24KC2ThetaAboveLeaf0001330002 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell00013300)) = true := by
  have h : ((childHL (childLL thetaAboveCell00013300))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell00013300)) h
theorem e24KC2ThetaAboveLeaf0001330003 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell00013300)) = true := by
  have h : ((childHH (childLL thetaAboveCell00013300))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell00013300)) h
theorem e24KC2ThetaAboveLeaf0001330010 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell00013300)) = true := by
  have h : ((childLL (childLH thetaAboveCell00013300))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell00013300)) h
theorem e24KC2ThetaAboveLeaf0001330011 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell00013300)) = true := by
  have h : ((childLH (childLH thetaAboveCell00013300))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell00013300)) h
theorem e24KC2ThetaAboveLeaf0001330012 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell00013300)) = true := by
  have h : ((childHL (childLH thetaAboveCell00013300))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell00013300)) h
theorem e24KC2ThetaAboveLeaf0001330013 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell00013300)) = true := by
  have h : ((childHH (childLH thetaAboveCell00013300))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell00013300)) h
theorem e24KC2ThetaAboveLeaf0001330100 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell00013301)) = true := by
  have h : ((childLL (childLL thetaAboveCell00013301))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell00013301)) h
theorem e24KC2ThetaAboveLeaf0001330101 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell00013301)) = true := by
  have h : ((childLH (childLL thetaAboveCell00013301))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell00013301)) h
theorem e24KC2ThetaAboveLeaf0001330102 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell00013301)) = true := by
  have h : ((childHL (childLL thetaAboveCell00013301))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell00013301)) h
theorem e24KC2ThetaAboveLeaf0001330103 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell00013301)) = true := by
  have h : ((childHH (childLL thetaAboveCell00013301))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell00013301)) h
theorem e24KC2ThetaAboveLeaf0001330110 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell00013301)) = true := by
  have h : ((childLL (childLH thetaAboveCell00013301))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell00013301)) h
theorem e24KC2ThetaAboveLeaf0001330111 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell00013301)) = true := by
  have h : ((childLH (childLH thetaAboveCell00013301))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell00013301)) h
theorem e24KC2ThetaAboveLeaf0001330112 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell00013301)) = true := by
  have h : ((childHL (childLH thetaAboveCell00013301))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell00013301)) h
theorem e24KC2ThetaAboveLeaf0001330113 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell00013301)) = true := by
  have h : ((childHH (childLH thetaAboveCell00013301))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell00013301)) h
theorem e24KC2ThetaAboveLeaf0001330200 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell00013302)) = true := by
  have h : ((childLL (childLL thetaAboveCell00013302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell00013302)) h
theorem e24KC2ThetaAboveLeaf0001330201 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell00013302)) = true := by
  have h : ((childLH (childLL thetaAboveCell00013302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell00013302)) h
theorem e24KC2ThetaAboveLeaf0001330202 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell00013302)) = true := by
  have h : ((childHL (childLL thetaAboveCell00013302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell00013302)) h
theorem e24KC2ThetaAboveLeaf0001330203 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell00013302)) = true := by
  have h : ((childHH (childLL thetaAboveCell00013302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell00013302)) h
theorem e24KC2ThetaAboveLeaf0001330210 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell00013302)) = true := by
  have h : ((childLL (childLH thetaAboveCell00013302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell00013302)) h
theorem e24KC2ThetaAboveLeaf0001330211 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell00013302)) = true := by
  have h : ((childLH (childLH thetaAboveCell00013302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell00013302)) h
theorem e24KC2ThetaAboveLeaf0001330212 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell00013302)) = true := by
  have h : ((childHL (childLH thetaAboveCell00013302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell00013302)) h
theorem e24KC2ThetaAboveLeaf0001330213 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell00013302)) = true := by
  have h : ((childHH (childLH thetaAboveCell00013302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell00013302)) h
theorem e24KC2ThetaAboveLeaf000133022 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell00013302) = true := by
  have h : ((childHL thetaAboveCell00013302)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell00013302) h
theorem e24KC2ThetaAboveLeaf000133023 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell00013302) = true := by
  have h : ((childHH thetaAboveCell00013302)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell00013302) h
theorem e24KC2ThetaAboveLeaf0001330300 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell00013303)) = true := by
  have h : ((childLL (childLL thetaAboveCell00013303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell00013303)) h
theorem e24KC2ThetaAboveLeaf0001330301 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell00013303)) = true := by
  have h : ((childLH (childLL thetaAboveCell00013303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell00013303)) h
theorem e24KC2ThetaAboveLeaf0001330302 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell00013303)) = true := by
  have h : ((childHL (childLL thetaAboveCell00013303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell00013303)) h
theorem e24KC2ThetaAboveLeaf0001330303 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell00013303)) = true := by
  have h : ((childHH (childLL thetaAboveCell00013303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell00013303)) h
theorem e24KC2ThetaAboveLeaf0001330310 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell00013303)) = true := by
  have h : ((childLL (childLH thetaAboveCell00013303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell00013303)) h
theorem e24KC2ThetaAboveLeaf0001330311 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell00013303)) = true := by
  have h : ((childLH (childLH thetaAboveCell00013303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell00013303)) h
theorem e24KC2ThetaAboveLeaf0001330312 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell00013303)) = true := by
  have h : ((childHL (childLH thetaAboveCell00013303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell00013303)) h
theorem e24KC2ThetaAboveLeaf0001330313 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell00013303)) = true := by
  have h : ((childHH (childLH thetaAboveCell00013303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell00013303)) h
theorem e24KC2ThetaAboveLeaf000133032 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell00013303) = true := by
  have h : ((childHL thetaAboveCell00013303)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell00013303) h
theorem e24KC2ThetaAboveLeaf000133033 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell00013303) = true := by
  have h : ((childHH thetaAboveCell00013303)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell00013303) h
theorem e24KC2ThetaAboveLeaf0001331000 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell00013310)) = true := by
  have h : ((childLL (childLL thetaAboveCell00013310))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell00013310)) h
theorem e24KC2ThetaAboveLeaf0001331001 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell00013310)) = true := by
  have h : ((childLH (childLL thetaAboveCell00013310))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell00013310)) h
theorem e24KC2ThetaAboveLeaf0001331002 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell00013310)) = true := by
  have h : ((childHL (childLL thetaAboveCell00013310))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell00013310)) h
theorem e24KC2ThetaAboveLeaf0001331003 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell00013310)) = true := by
  have h : ((childHH (childLL thetaAboveCell00013310))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell00013310)) h
theorem e24KC2ThetaAboveLeaf0001331010 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell00013310)) = true := by
  have h : ((childLL (childLH thetaAboveCell00013310))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell00013310)) h
theorem e24KC2ThetaAboveLeaf0001331011 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell00013310)) = true := by
  have h : ((childLH (childLH thetaAboveCell00013310))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell00013310)) h
theorem e24KC2ThetaAboveLeaf0001331012 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell00013310)) = true := by
  have h : ((childHL (childLH thetaAboveCell00013310))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell00013310)) h
theorem e24KC2ThetaAboveLeaf0001331013 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell00013310)) = true := by
  have h : ((childHH (childLH thetaAboveCell00013310))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell00013310)) h
theorem e24KC2ThetaAboveLeaf0001331100 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell00013311)) = true := by
  have h : ((childLL (childLL thetaAboveCell00013311))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell00013311)) h
theorem e24KC2ThetaAboveLeaf0001331101 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell00013311)) = true := by
  have h : ((childLH (childLL thetaAboveCell00013311))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell00013311)) h
theorem e24KC2ThetaAboveLeaf0001331102 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell00013311)) = true := by
  have h : ((childHL (childLL thetaAboveCell00013311))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell00013311)) h
theorem e24KC2ThetaAboveLeaf0001331103 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell00013311)) = true := by
  have h : ((childHH (childLL thetaAboveCell00013311))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell00013311)) h
theorem e24KC2ThetaAboveLeaf0001331110 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell00013311)) = true := by
  have h : ((childLL (childLH thetaAboveCell00013311))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell00013311)) h
theorem e24KC2ThetaAboveLeaf0001331111 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell00013311)) = true := by
  have h : ((childLH (childLH thetaAboveCell00013311))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell00013311)) h
theorem e24KC2ThetaAboveLeaf0001331112 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell00013311)) = true := by
  have h : ((childHL (childLH thetaAboveCell00013311))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell00013311)) h
theorem e24KC2ThetaAboveLeaf0001331113 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell00013311)) = true := by
  have h : ((childHH (childLH thetaAboveCell00013311))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell00013311)) h
theorem e24KC2ThetaAboveLeaf0001331200 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell00013312)) = true := by
  have h : ((childLL (childLL thetaAboveCell00013312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell00013312)) h
theorem e24KC2ThetaAboveLeaf0001331201 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell00013312)) = true := by
  have h : ((childLH (childLL thetaAboveCell00013312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell00013312)) h

end PartE
end GerverSofa

end

end

end

end

end

end
