/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

-- Optional aggregate for the Ricci-flow local-existence scaffold.
-- Keep this out of the root target so routine `lake build PoincareCurvature`
-- iterations do not rebuild the heaviest research modules.
import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.GaugeReduction.Diffeomorph3FlowExistence
import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.GaugeReduction.ModelGaugeFlowODE
import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.GaugeReduction.Diffeomorph3FlowTimeDerivative
import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.GaugeReduction.Diffeomorph3FlowSubsingleton
import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.ParabolicHolder
import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.HeatKernel1D
import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.Parabolic.FunctionSpace
import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.Parabolic.HigherFunctionSpace
import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.Parabolic.HigherMatrix
import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.Parabolic.HigherLocalFrameGram
import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.Parabolic.MatrixC0Alpha
import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.Parabolic.LocalFrameGram
import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.SmoothRealization
import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.SmoothRealizationGaugeRoutes
import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.SmoothRealizationMetricCone
import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.SmoothApproxClosure
import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.GeometricGaugeFlow
import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.IsEmptyChartClosure
import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.LocalExistence.RankOne
import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.LocalExistence.RankOneDeTurck
import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.LocalExistence.RankOneGaugeReduced
import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.LocalExistence.RicciFlatClosure
import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.LocalExistence.RicciFlatClosureGaugeReduced
import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.LocalExistence.IsEmptyDeTurckFamily
import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.LocalExistence.EinsteinAux
import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.LocalExistence.Einstein

/-! # Ricci Flow Local Existence -/
