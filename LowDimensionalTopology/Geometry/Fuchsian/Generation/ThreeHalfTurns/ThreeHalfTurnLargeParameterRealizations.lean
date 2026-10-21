module
public import LowDimensionalTopology.Geometry.Fuchsian.Generation.ThreeHalfTurns.Classification
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set
open scoped UpperHalfPlane
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- Every real parameter at least one is realized by three actual half-turns
in their own discrete non-elementary group. The explicit centers give the
parameter, while the proved geometric classification supplies discreteness. -/
theorem three_halfturn_every_large_parameter_realizable (lam:ℝ) (hlam:1≤lam) :
    ∃f g h:Mobius.complexMobiusGroup,orderOf f=2 ∧ orderOf g=2 ∧ orderOf h=2 ∧
      _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup (Subgroup.closure ({f,g,h}:Set Mobius.complexMobiusGroup)) ∧
      Nonempty (FuchsianDisc (Subgroup.closure ({f,g,h}:Set Mobius.complexMobiusGroup))) ∧
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure ({f,g,h}:Set Mobius.complexMobiusGroup)) ∧
      _root_.LowDimensionalTopology.Geometry.Mobius.mobiusTraceAbs (f*g*h)/2=lam := by
  let w:ℍ:=UpperHalfPlane.mk ⟨4*lam/3,1⟩ (by norm_num)
  have hw:0<w.re:=by change 0<4*lam/3;linarith only [hlam]
  let T:=halfTurnCanonical_center_triangle 1 2 (by norm_num) (by norm_num) w hw
  let A:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL 1 (by norm_num)
  let B:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL (1*2) (by norm_num)
  let C:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL w
  have hA:_root_.LowDimensionalTopology.Geometry.Hyperbolic.IsHalfTurnAt A T.a:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL_at 1 (by norm_num)
  have hB:_root_.LowDimensionalTopology.Geometry.Hyperbolic.IsHalfTurnAt B T.b:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL_at (1*2) (by norm_num)
  have hC:_root_.LowDimensionalTopology.Geometry.Hyperbolic.IsHalfTurnAt C T.c:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL_at w
  have ht:Matrix.trace (A*B*C).val=2*lam:=by
    dsimp only [A,B,C]
    rw [axisHalfTurns_point_triple_trace]
    change ((1*2)/1-1/(1*2))*(4*lam/3)/1=2*lam
    ring
  have habs:|Matrix.trace (A*B*C).val|=2*lam:=by
    rw [ht,abs_of_pos (by linarith only [hlam])]
  have hInv:_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfTurnTriangleInvariant T=lam:=by
    have he:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfTurn_triple_abs_trace T A B C hA hB hC
    rw [habs] at he
    linarith only [he]
  have hlarge:1≤_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfTurnTriangleInvariant T:=by rwa [hInv]
  have hd:=(threeHalfTurn_large_parameter_discrete_freeProduct T A B C hA hB hC hlarge).1
  let P:=threeHalfTurn_real_halfPlaneData A B C hd
  have hNE:=threeHalfTurn_large_parameter_nonElementary T A B C hA hB hC hlarge
  refine ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C,hA.1,hB.1,hC.1,hd,
    ⟨P.asFuchsianDisc⟩,hNE,?_⟩
  rw [←map_mul,←map_mul,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_traceAbs,habs]
  ring

end LowDimensionalTopology.Geometry.Fuchsian
