/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.TriangleGroup.MobiusTriangleGroups
public import LowDimensionalTopology.Geometry.Fuchsian.Generation.TwoParabolics.TwoParabolicFuchsianModels
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set
open scoped UpperHalfPlane OnePoint MatrixGroups
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
  LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

theorem standardHeckeMobiusGroup_isTriangle (q : ℕ∞) (hq : 3≤q) :
    IsMobiusTriangleGroup (standardHeckeMobiusGroup q hq) :=
  isMobiusTriangleGroup_native_image _ _ (standardHeckeGroup_isHecke q hq).isTriangleGroup

theorem unitHeckeMobiusGroup_isTriangle (q : ℕ∞) (hq : 3≤q) :
    IsMobiusTriangleGroup (unitHeckeMobiusGroup q hq) := by
  let D:=unitHeckeDilationSL q hq
  have he:=nativeConformal_range_conjugate_eq (standardHeckeGroup q hq) (unitHeckeGroup q hq)
    (standardHeckeGroup_le_conformal q hq) (unitHeckeGroup_le_conformal q hq)
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry D) ⟨D,rfl⟩ rfl
  change _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate (halfPlaneConformalMobiusHom (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneConformalElement D))
    (standardHeckeMobiusGroup q hq)=unitHeckeMobiusGroup q hq at he
  rw [halfPlaneConformalMobiusHom_matrix] at he
  have h:=(standardHeckeMobiusGroup_isTriangle q hq).conjugation (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius D)
  rwa [he] at h

theorem twoIdealMobiusGroup_isTriangle (p : ℕ) (hp : 2≤p) :
    IsMobiusTriangleGroup
      (nativeConformalSubgroupMobiusHom (triangleConformalGroup (twoIdealIntegralTriangle p hp))
        inf_le_right).range := by
  apply isMobiusTriangleGroup_native_image
  refine ⟨p,⊤,⊤,by exact_mod_cast hp,by simp,by simp,?_⟩
  have ha:=twoIdealIntegralTriangle_angles p hp
  refine ⟨twoIdealIntegralTriangle p hp,?_,?_,?_,rfl⟩
  · simpa only [triangleOrderAngle_nat] using ha.1
  · simpa only [triangleOrderAngle_top] using ha.2.1
  · simpa only [triangleOrderAngle_top] using ha.2.2

theorem twoParabolicCanonicalGroup_small_isTriangle (c : ℝ) (hc : 1≤c) (h4 : c<4)
    (hd : _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup (twoParabolicCanonicalGroup c)) :
    IsMobiusTriangleGroup (twoParabolicCanonicalGroup c) := by
  rcases twoParabolic_small_group_models c hc h4 hd with ⟨n,hn,_hodd,_he,hmodel⟩|⟨p,hp,_he,hmodel⟩
  · rw [hmodel]
    exact unitHeckeMobiusGroup_isTriangle n (by exact_mod_cast hn)
  · rw [hmodel]
    exact (twoIdealMobiusGroup_isTriangle p hp).conjugation _

theorem twoParabolicCanonicalGroup_parameter_ge_four (c : ℝ) (hc : 1≤c)
    (hd : _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup (twoParabolicCanonicalGroup c))
    (hnt : ¬IsMobiusTriangleGroup (twoParabolicCanonicalGroup c)) : 4≤c := by
  by_contra hn
  exact hnt (twoParabolicCanonicalGroup_small_isTriangle c hc (lt_of_not_ge hn) hd)

theorem fuchsian_two_parabolic_small_trace_triangle
    (f g : Mobius.complexMobiusGroup)
    (D : FuchsianDisc (Subgroup.closure ({f,g} : Set Mobius.complexMobiusGroup)))
    (hf : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic f)
    (hg : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic g)
    (hne : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure ({f,g} : Set Mobius.complexMobiusGroup)))
    (hsmall : (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusCommutatorTrace f g).re<18) :
    IsMobiusTriangleGroup (Subgroup.closure ({f,g} : Set Mobius.complexMobiusGroup)) := by
  obtain ⟨q,hmodel⟩:=fuchsian_two_parabolic_exceptional_group_models f g D hf hg hne hsmall
  apply isMobiusTriangleGroup_of_conjugate _ q
  rcases hmodel with ⟨n,hn,_hodd,hG,_htrace⟩|⟨p,hp,hG,_htrace⟩
  · rw [hG]
    exact unitHeckeMobiusGroup_isTriangle n (by exact_mod_cast hn)
  · rw [hG]
    exact twoIdealMobiusGroup_isTriangle p hp

theorem fuchsian_two_parabolic_nontriangle_trace_ge_eighteen
    (f g : Mobius.complexMobiusGroup)
    (D : FuchsianDisc (Subgroup.closure ({f,g} : Set Mobius.complexMobiusGroup)))
    (hf : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic f)
    (hg : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic g)
    (hne : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure ({f,g} : Set Mobius.complexMobiusGroup)))
    (hnt : ¬IsMobiusTriangleGroup (Subgroup.closure ({f,g} : Set Mobius.complexMobiusGroup))) :
    18≤(_root_.LowDimensionalTopology.Geometry.Mobius.mobiusCommutatorTrace f g).re := by
  by_contra hn
  exact hnt (fuchsian_two_parabolic_small_trace_triangle f g D hf hg hne (lt_of_not_ge hn))

end LowDimensionalTopology.Geometry.Fuchsian
