/-
Copyright (c) 2026 William Blair. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Blair
-/

import LeanPool.InflationTermination.PalomarSolutions.TriangleInflation
import LeanPool.InflationTermination.PalomarSolutions.TriangleInflationClassification
import LeanPool.InflationTermination.TriangleInflation
import LeanPool.InflationTermination.TriangleInflation.ConvexOrder
import LeanPool.InflationTermination.TriangleInflation.Defect
import LeanPool.InflationTermination.TriangleInflation.DefectLaw
import LeanPool.InflationTermination.TriangleInflation.Defs
import LeanPool.InflationTermination.TriangleInflation.Exponent
import LeanPool.InflationTermination.TriangleInflation.Fan
import LeanPool.InflationTermination.TriangleInflation.Finner
import LeanPool.InflationTermination.TriangleInflation.FinnerMeasure
import LeanPool.InflationTermination.TriangleInflation.Graph
import LeanPool.InflationTermination.TriangleInflation.Graph.Classification
import LeanPool.InflationTermination.TriangleInflation.Graph.ClassificationTheorem
import LeanPool.InflationTermination.TriangleInflation.Graph.CycleObstruction
import LeanPool.InflationTermination.TriangleInflation.Graph.CycleWitness
import LeanPool.InflationTermination.TriangleInflation.Graph.Cycles
import LeanPool.InflationTermination.TriangleInflation.Graph.Defs
import LeanPool.InflationTermination.TriangleInflation.Graph.DoubleStar
import LeanPool.InflationTermination.TriangleInflation.Graph.DoubleStarForest
import LeanPool.InflationTermination.TriangleInflation.Graph.FivePath
import LeanPool.InflationTermination.TriangleInflation.Graph.FivePathWitness
import LeanPool.InflationTermination.TriangleInflation.Graph.Flips
import LeanPool.InflationTermination.TriangleInflation.Graph.Linear
import LeanPool.InflationTermination.TriangleInflation.Graph.RootSink
import LeanPool.InflationTermination.TriangleInflation.Graph.Soundness
import LeanPool.InflationTermination.TriangleInflation.Graph.SquareWitness
import LeanPool.InflationTermination.TriangleInflation.Graph.Transport
import LeanPool.InflationTermination.TriangleInflation.Graph.Triangle
import LeanPool.InflationTermination.TriangleInflation.Graph.TriangleWitness
import LeanPool.InflationTermination.TriangleInflation.Main
import LeanPool.InflationTermination.TriangleInflation.Rate

/-!
# Inflation termination for classical pair-source networks

Source: url:https://github.com/williamjblair/inflation-termination
Authors: William Blair
Status: verified
Main declarations: `TriangleInflation.Graph.classification_NW`, `TriangleInflation.no_finite_characterizing_order`
Tags: causal-inference, probability, inflation-hierarchy, graph-theory
MSC: 60A05, 05C05
-/

/-
Upstream MIT license notice (retained for the Apache 2.0 port):

MIT License

Copyright (c) 2026 William Blair

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.

-/
