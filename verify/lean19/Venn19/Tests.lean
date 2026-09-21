import VennCore.Checker
import VennCore.Connectivity
import VennCore.Symmetry
import VennCore.Incidence
import VennCore.Rotation
import VennCore.Links
import VennCore.CurvePolygon

open Venn19

-- Bit numbering follows character positions, not usual binary-print order.
#guard (parsePattern 19 (.str "1000000000000000000")).toOption == some 1
#guard (parsePattern 19 (.str "0000000000000000001")).toOption == some (2^18)
#guard rotate 1 == 2^18
#guard rotate 2 == 1

-- Connected in the full graph, disconnected when the middle vertex is excluded.
#guard GraphProof.connectedCheck #[#[1], #[0, 2], #[1]] (fun _ => true)
#guard !GraphProof.connectedCheck #[#[1], #[0, 2], #[1]] (fun v => v != 1)

-- A fabricated parent edge and a cycle with nondecreasing ranks are rejected.
#guard !GraphProof.treeCheck #[#[], #[]] (fun _ => true) ⟨0, #[0, 0], #[1, 2]⟩
#guard !GraphProof.treeCheck #[#[], #[2], #[1]] (fun _ => true) ⟨0, #[0, 2, 1], #[1, 2, 2]⟩

-- Link permutations may be bijective and still have more than one cycle.
#guard singleLink #[1, 2, 3, 4] (Std.HashMap.ofList [(1, 2), (2, 3), (3, 4), (4, 1)])
#guard !singleLink #[1, 2, 3, 4] (Std.HashMap.ofList [(1, 2), (2, 1), (3, 4), (4, 3)])

-- The symmetry key preserves the cyclic order, rather than forgetting orientation.
#guard faceKey #[0, 1, 3, 2] == faceKey #[3, 2, 0, 1]
#guard faceKey #[0, 1, 3, 2] != faceKey #[0, 2, 3, 1]
#guard !rotationWitnessCheckFor #[#[0, 1, 3, 2]]

-- Two oppositely oriented quadrilaterals give a valid incidence certificate.
private def doubleQuad : Array Face := #[#[0, 1, 2, 3], #[0, 3, 2, 1]]
private def squareGraph : Graph := #[#[1, 3], #[0, 2], #[1, 3], #[0, 2]]
#guard incidenceCheck doubleQuad squareGraph
#guard !coverageCheck doubleQuad 5
#guard !edgesCheck #[#[0, 1, 2, 3]] squareGraph
#guard !edgesCheck doubleQuad #[#[2], #[0, 2], #[1, 3], #[0, 2]]
#guard distinctCornersCheck doubleQuad
#guard !distinctCornersCheck #[#[0, 1, 0, 3]]

-- An actual 19-element face orbit passes; incomplete or reversed orbits fail.
private def squareOrbit : Array Face :=
  (Array.range 19).map fun n => #[0, 1, 3, 2].map (steps regionStep n)
#guard faceRotationCheck squareOrbit
#guard fixedTriangleCheck squareOrbit
#guard !faceRotationCheck (squareOrbit.pop)
#guard !faceRotationCheck (squareOrbit.set! 0 #[0, 2, 3, 1])

-- Complete triangle-dart link certificates: valid sphere and corrupt witnesses.
private def doubleQuadStars := LinkProof.propose doubleQuad 4
#guard LinkProof.check doubleQuad 4 doubleQuadStars
#guard !LinkProof.check doubleQuad 5 (LinkProof.propose doubleQuad 5)
#guard !LinkProof.check doubleQuad 4
  (doubleQuadStars.set! 0 ((doubleQuadStars.getD 0 #[]).pop))
#guard !LinkProof.coverageCheck doubleQuad 4
  (doubleQuadStars.set! 0 #[])
#guard !LinkProof.rowCheck doubleQuad 4 0
  ((doubleQuadStars.getD 0 #[]) ++ (doubleQuadStars.getD 0 #[]))
#guard !LinkProof.rowCheck doubleQuad 4 0 #[24, 25, 26]
-- Two spheres pinched at vertex 0 have two link cycles, so are not a surface.
private def pinchedQuads : Array Face :=
  #[#[0, 1, 2, 3], #[0, 3, 2, 1], #[0, 4, 5, 6], #[0, 6, 5, 4]]
#guard !LinkProof.check pinchedQuads 7 (LinkProof.propose pinchedQuads 7)

-- Midpoint curve certificates must cover every labelled arm, not just one cycle.
private def bitDoubleQuad : Array Face := #[#[0,1,3,2],#[0,2,3,1]]
private def bitCurve := CurveProof.propose bitDoubleQuad 4 0
#guard CurveProof.check bitDoubleQuad 4 0 bitCurve
#guard CurveProof.labelsCheck bitDoubleQuad 4 2
#guard CurveProof.crossingLabelsCheck bitDoubleQuad 4
#guard !CurveProof.check bitDoubleQuad 4 1 bitCurve
#guard !CurveProof.supportsCheck 8 #[(0,1),(1,2),(3,3)]
#guard !CurveProof.supportsCheck 4 #[(0,0),(1,1),(4,4)]
#guard !CurveProof.check bitDoubleQuad 4 0
  { bitCurve with triangles := bitCurve.triangles.pop }
#guard !CurveProof.check bitDoubleQuad 4 0
  { bitCurve with vertices := bitCurve.vertices.set! 0 (0,1) }
#guard !CurveProof.labelsCheck #[#[0,3,5,6]] 8 3
#guard !CurveProof.crossingLabelsCheck #[#[0,1,2,4]] 8
private def twoBitSpheres : Array Face :=
  #[#[0,1,3,2],#[0,2,3,1],#[4,5,7,6],#[4,6,7,5]]
private def oneOfTwoCycles := CurveProof.propose twoBitSpheres 8 0
#guard CurveProof.polygonCheck twoBitSpheres 8 0 oneOfTwoCycles
#guard !CurveProof.coverageCheck twoBitSpheres 8 0 oneOfTwoCycles
#guard !CurveProof.check twoBitSpheres 8 0 oneOfTwoCycles
