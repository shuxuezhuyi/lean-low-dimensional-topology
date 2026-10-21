/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.Examples.AxisCosetCounterexamples
public import LowDimensionalTopology.Geometry.Hyperbolic.Area.TriangleAreaFinite
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory Topology
open scoped UpperHalfPlane OnePoint
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- The actual original dilation group acts discontinuously on the entire upper half-plane. -/
theorem dilationBoundaryGroup_discontinuous :
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn _root_.LowDimensionalTopology.Geometry.DiscreteGroups.orbitCounterexampleDilationGroup _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet :=
  axisCounterexampleGroupData.discontinuous

/-- The actual open vertical strip in the native upper half-plane. -/
def dilationBoundaryStrip : Set ℍ:={z|1<z.re ∧z.re<2}

theorem dilationBoundaryStrip_open : IsOpen dilationBoundaryStrip :=
  (isOpen_lt continuous_const UpperHalfPlane.continuous_re).inter
    (isOpen_lt UpperHalfPlane.continuous_re continuous_const)

theorem dilationBoundaryStrip_closure : closure dilationBoundaryStrip={z:ℍ|1≤z.re ∧z.re≤2} := by
  change closure (UpperHalfPlane.re ⁻¹' Ioo 1 2)=UpperHalfPlane.re ⁻¹' Icc 1 2
  rw [←UpperHalfPlane.isOpenMap_re.preimage_closure_eq_closure_preimage UpperHalfPlane.continuous_re,
    closure_Ioo (by norm_num : (1:ℝ)≠2)]

theorem dilationBoundaryStrip_frontier : frontier dilationBoundaryStrip={z:ℍ|z.re=1 ∨z.re=2} := by
  rw [frontier,dilationBoundaryStrip_closure,dilationBoundaryStrip_open.interior_eq]
  ext z
  change ((1≤z.re ∧z.re≤2) ∧¬(1<z.re ∧z.re<2))↔z.re=1 ∨z.re=2
  constructor
  · rintro ⟨⟨h1,h2⟩,h⟩
    by_cases he:z.re=1
    · exact Or.inl he
    · exact Or.inr (by by_contra hn;exact h ⟨lt_of_le_of_ne h1 (Ne.symm he),lt_of_le_of_ne h2 hn⟩)
  · rintro (h|h) <;> rw [h] <;> norm_num

theorem dilationBoundaryStrip_connected : IsConnected dilationBoundaryStrip := by
  let R:Set ℂ:={z|0<z.im ∧1<z.re ∧z.re<2}
  have hR:IsConnected R:=by
    refine ⟨⟨⟨3/2,1⟩,by norm_num [R]⟩,?_⟩
    exact ((convex_halfSpace_gt Complex.imCLM.toLinearMap.isLinear 0).inter
      ((convex_halfSpace_gt Complex.reCLM.toLinearMap.isLinear 1).inter
        (convex_halfSpace_lt Complex.reCLM.toLinearMap.isLinear 2))).isPreconnected
  have h:=hR.preimage_of_isOpenMap UpperHalfPlane.coe_injective
    UpperHalfPlane.isOpenEmbedding_coe.isOpenMap (by
      rintro z hz
      exact ⟨⟨z,hz.1⟩,rfl⟩)
  have he:UpperHalfPlane.coe ⁻¹' R=dilationBoundaryStrip:=by
    ext z
    change (0<z.im ∧1<z.re ∧z.re<2)↔(1<z.re ∧z.re<2)
    simp only [z.im_pos,true_and]
  rwa [he] at h

theorem dilationBoundaryStrip_frontier_null : volume (frontier dilationBoundaryStrip)=0 := by
  have he:frontier dilationBoundaryStrip=
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical 1).carrier ∪(_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical 2).carrier:=by
    rw [dilationBoundaryStrip_frontier]
    rfl
  rw [he]
  exact measure_union_null (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.volume_zero
    _) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.volume_zero _)

local instance : MulAction _root_.LowDimensionalTopology.Geometry.DiscreteGroups.orbitCounterexampleDilationGroup ℍ:=axisCounterexampleGroupData.nativeAction

theorem dilationBoundaryAction_zpow_re (n:ℤ) (z:ℍ) :
    ((⟨_root_.LowDimensionalTopology.Geometry.DiscreteGroups.orbitCounterexampleDilation^n,Subgroup.zpow_mem_zpowers _
      _⟩:
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.orbitCounterexampleDilationGroup) • z).re=(2:ℝ)^n*z.re := by
  rw [axisCounterexampleGroupData.nativeAction_realSL _ _
    (axisCounterexampleDilation_zpow_real
      n).symm,_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL_re]

/-- Every genuine boundary point is carried to a different genuine boundary point by the actual cyclic group. -/
theorem dilationBoundaryStrip_boundary_mates (z:ℍ) (hz:z∈frontier dilationBoundaryStrip) :
    ∃g:_root_.LowDimensionalTopology.Geometry.DiscreteGroups.orbitCounterexampleDilationGroup,g • z∈frontier dilationBoundaryStrip ∧g • z≠z := by
  rw [dilationBoundaryStrip_frontier] at hz
  rcases hz with hz|hz
  · let g:_root_.LowDimensionalTopology.Geometry.DiscreteGroups.orbitCounterexampleDilationGroup:=⟨_root_.LowDimensionalTopology.Geometry.DiscreteGroups.orbitCounterexampleDilation^ (1:ℤ),Subgroup.zpow_mem_zpowers _ _⟩
    have hr:(g • z).re=2:=by rw [dilationBoundaryAction_zpow_re,hz];norm_num
    refine ⟨g,?_,?_⟩
    · rw [dilationBoundaryStrip_frontier]
      exact Or.inr hr
    · intro h
      have he:=congrArg UpperHalfPlane.re h
      rw [hr,hz] at he
      norm_num at he
  · let g:_root_.LowDimensionalTopology.Geometry.DiscreteGroups.orbitCounterexampleDilationGroup:=⟨_root_.LowDimensionalTopology.Geometry.DiscreteGroups.orbitCounterexampleDilation^ (-1:ℤ),Subgroup.zpow_mem_zpowers _ _⟩
    have hr:(g • z).re=1:=by rw [dilationBoundaryAction_zpow_re,hz];norm_num
    refine ⟨g,?_,?_⟩
    · rw [dilationBoundaryStrip_frontier]
      exact Or.inl hr
    · intro h
      have he:=congrArg UpperHalfPlane.re h
      rw [hr,hz] at he
      norm_num at he

/-- The imaginary-axis orbit misses the entire closed strip, so no genuine fundamental selector fits it. -/
theorem dilationBoundaryStrip_not_fundamental (μ:Measure ℍ) :
    ¬_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain _root_.LowDimensionalTopology.Geometry.DiscreteGroups.orbitCounterexampleDilationGroup ℍ μ dilationBoundaryStrip := by
  intro hD
  let z:ℍ:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe 0 1 (by norm_num)
  obtain ⟨g,hg⟩:=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain.closure_meetsEveryOrbit _root_.LowDimensionalTopology.Geometry.DiscreteGroups.orbitCounterexampleDilationGroup ℍ hD z
  obtain ⟨n,hn⟩:=Subgroup.mem_zpowers_iff.mp g.property
  have he:g=(⟨_root_.LowDimensionalTopology.Geometry.DiscreteGroups.orbitCounterexampleDilation^n,Subgroup.zpow_mem_zpowers _ _⟩:_root_.LowDimensionalTopology.Geometry.DiscreteGroups.orbitCounterexampleDilationGroup):=
    Subtype.ext hn.symm
  rw [dilationBoundaryStrip_closure] at hg
  have hr:(g • z).re=0:=by rw [he,dilationBoundaryAction_zpow_re];simp [z,_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe]
  change 1≤(g • z).re ∧(g • z).re≤2 at hg
  rw [hr] at hg
  norm_num at hg

/-- All other domain conditions and literal boundary mating hold for the actual discrete group, but the fundamental-domain conclusion fails. -/
theorem dilationBoundaryStrip_counterexample :
    _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup _root_.LowDimensionalTopology.Geometry.DiscreteGroups.orbitCounterexampleDilationGroup ∧
      IsOpen dilationBoundaryStrip ∧IsConnected dilationBoundaryStrip ∧
      volume (frontier dilationBoundaryStrip)=0 ∧
      (∀z∈frontier dilationBoundaryStrip,
        ∃g:_root_.LowDimensionalTopology.Geometry.DiscreteGroups.orbitCounterexampleDilationGroup,g • z∈frontier dilationBoundaryStrip ∧g • z≠z) ∧
      ¬_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain _root_.LowDimensionalTopology.Geometry.DiscreteGroups.orbitCounterexampleDilationGroup ℍ volume dilationBoundaryStrip := by
  exact ⟨_root_.LowDimensionalTopology.Geometry.DiscreteGroups.orbitCounterexampleDilationGroup_discrete,dilationBoundaryStrip_open,
    dilationBoundaryStrip_connected,dilationBoundaryStrip_frontier_null,
    dilationBoundaryStrip_boundary_mates,dilationBoundaryStrip_not_fundamental volume⟩

end LowDimensionalTopology.Geometry.Fuchsian
