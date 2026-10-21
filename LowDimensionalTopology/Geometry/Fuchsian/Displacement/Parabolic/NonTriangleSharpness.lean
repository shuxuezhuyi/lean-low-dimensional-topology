/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.Covolume.TriangleCovolume
public import LowDimensionalTopology.Geometry.Fuchsian.Generation.ThreeHalfTurns.HalfTurnSchottkySharpness
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set
open scoped UpperHalfPlane OnePoint MatrixGroups
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- The actual original parabolic example group is not a geometric
triangle group, by its proved genuine second-kind limit set. -/
theorem schottkyParabolicGroup_not_triangle (c:ℝ) (hc:4<c) :
    ¬IsMobiusTriangleGroup (schottkyParabolicGroup c) :=
  secondKind_not_mobiusTriangleGroup (schottkyParabolicGroup_data c hc).asFuchsianDisc
    (schottkyParabolicSL_pair_nonElementary c (by linarith only [hc]))
    (schottkyParabolicGroup_secondKind c hc)

/-- The actual original parabolic/hyperbolic example group is not a
geometric triangle group; no signature exclusion is assumed. -/
theorem halfTurnSchottkyGroup_not_triangle (v:ℝ) (hv:0<v) (hvu:v<1/2) :
    ¬IsMobiusTriangleGroup (halfTurnSchottkyGroup v hv) :=
  secondKind_not_mobiusTriangleGroup (halfTurnSchottkyGroup_data v hv hvu).asFuchsianDisc
    (halfTurnSchottkyGroup_nonElementary v hv) (halfTurnSchottkyGroup_secondKind v hv hvu)

/-- Actual discrete non-elementary nontriangle parabolic pairs have
true whole-half-plane displacement infima arbitrarily close to one. -/
theorem nontriangle_parabolic_sharpness (ε:ℝ) (hε:0<ε) :
    ∃c:ℝ,∃_hc:4<c,
      ¬IsMobiusTriangleGroup (schottkyParabolicGroup c) ∧
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (schottkyParabolicGroup c) ∧
      1<_root_.LowDimensionalTopology.Geometry.Hyperbolic.displacementP (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1)) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (schottkyParabolicSL c)) ∧
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.displacementP (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1)) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (schottkyParabolicSL c))<1+ε := by
  obtain ⟨c,hc,_hSecond,hNE,hlo,hhi⟩:=schottkyParabolic_secondKind_approaches ε hε
  exact ⟨c,hc,schottkyParabolicGroup_not_triangle c hc,hNE,hlo,hhi⟩

/-- Actual discrete non-elementary nontriangle parabolic/hyperbolic
pairs have true whole-half-plane infima arbitrarily close to one half. -/
theorem nontriangle_parabolic_hyperbolic_sharpness (ε:ℝ) (hε:0<ε) :
    ∃v:ℝ,∃hv:0<v,∃_hvu:v<1/2,
      ¬IsMobiusTriangleGroup (halfTurnSchottkyGroup v hv) ∧
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (halfTurnSchottkyGroup v hv) ∧
      _root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (halfTurnSchottkyProductSL v hv)) ∧
      1/2<_root_.LowDimensionalTopology.Geometry.Hyperbolic.displacementP (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1)) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (halfTurnSchottkyProductSL v hv)) ∧
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.displacementP (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1)) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (halfTurnSchottkyProductSL v hv))<1/2+ε := by
  obtain ⟨v,hv,hvu,_hSecond,hNE,hHyp,hlo,hhi⟩:=halfTurnSchottky_secondKind_approaches ε hε
  exact ⟨v,hv,hvu,halfTurnSchottkyGroup_not_triangle v hv hvu,hNE,hHyp,hlo,hhi⟩

end LowDimensionalTopology.Geometry.Fuchsian
