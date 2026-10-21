module
public import LowDimensionalTopology.Geometry.Fuchsian.Signature.Realization.GeneralSignatureTargetGroup
public import LowDimensionalTopology.Geometry.Fuchsian.TriangleGroup.Hecke.HeckeDiscreteness
public import LowDimensionalTopology.Geometry.Fuchsian.TriangleGroup.NativeTriangleProperness
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set
open scoped UpperHalfPlane
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
  LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis

section
variable (g:ℕ) (orders:List ℕ) (s t:ℕ)
    (ho:∀m∈orders,2≤m) (hdef:0<generalCoreDeficit g orders s t)
    (d:ℝ) (hd:0<d) (hb:_root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance (generalCoreTheta g orders s t) d=Real.pi)

/-- The entire actual retained subgroup preserves the original orientation. -/
theorem generalCoreTargetGroup_conformal :
    generalCoreTargetGroup g orders s t ho hdef d hd hb≤_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneConformalIsometryGroup :=
  (generalCoreTargetGroup_le_aux g orders s t ho hdef d hd hb).trans
    (cofiniteMixedTangentialGenerated_conformal (generalCoreTheta g orders s t) d
      (generalCoreTheta_mem g orders s t ho hdef) hd hb (generalCoreAuxPairing g orders s t)
      (generalCoreAuxPairing_involutive g orders s t) (generalCoreAuxPairing_angle_profile g orders s t))

/-- The faithful actual sphere representation of the retained native group. -/
def generalCoreTargetMobiusHom :
    generalCoreTargetGroup g orders s t ho hdef d hd hb→*Mobius.complexMobiusGroup :=
  nativeConformalSubgroupMobiusHom _ (generalCoreTargetGroup_conformal g orders s t ho hdef d hd hb)

def generalCoreTargetMobiusGroup : Subgroup Mobius.complexMobiusGroup :=
  (generalCoreTargetMobiusHom g orders s t ho hdef d hd hb).range

/-- The actual native target and its entire projective image are isomorphic. -/
def generalCoreTargetMobiusEquiv :
    generalCoreTargetGroup g orders s t ho hdef d hd hb≃*
      generalCoreTargetMobiusGroup g orders s t ho hdef d hd hb :=
  MulEquiv.ofBijective (generalCoreTargetMobiusHom g orders s t ho hdef d hd hb).rangeRestrict
    ⟨fun _ _ he=>(nativeConformalSubgroupMobiusHom_isometry _
      (generalCoreTargetGroup_conformal g orders s t ho hdef d hd hb)).injective
        (congrArg Subtype.val he),
      (generalCoreTargetMobiusHom g orders s t ho hdef d hd hb).rangeRestrict_surjective⟩

/-- Actual Fuchsian data is inherited from the proved auxiliary tessellation. -/
theorem generalCoreTargetMobiusData :
    HalfPlaneFuchsianGroup (generalCoreTargetMobiusGroup g orders s t ho hdef d hd hb) := by
  let generalSignatureTargetNativeDiscrete :
      DiscreteTopology (generalCoreTargetGroup g orders s t ho hdef d hd hb):=
    generalCoreTargetGroup_discrete g orders s t ho hdef d hd hb
  exact nativeConformalSubgroup_halfPlaneData _
    (generalCoreTargetGroup_conformal g orders s t ho hdef d hd hb)

/-- Finite generation refers to the same entire actual projective target. -/
theorem generalCoreTargetMobiusGroup_fg :
    (generalCoreTargetMobiusGroup g orders s t ho hdef d hd hb).FG := by
  let generalSignatureTargetNativeFG :
      Group.FG (generalCoreTargetGroup g orders s t ho hdef d hd hb):=
    (Group.fg_iff_subgroup_fg _).mpr (generalCoreTargetGroup_fg g orders s t ho hdef d hd hb)
  apply (Group.fg_iff_subgroup_fg _).mp
  exact Group.fg_of_surjective
    (generalCoreTargetMobiusHom g orders s t ho hdef d hd hb).rangeRestrict_surjective

/-- The actual boundary representation preserves every original native point. -/
theorem generalCoreTargetMobiusEquiv_action
    (f:generalCoreTargetGroup g orders s t ho hdef d hd hb) (z:ℍ) :
    letI:=(generalCoreTargetMobiusData g orders s t ho hdef d hd hb).nativeAction
    generalCoreTargetMobiusEquiv g orders s t ho hdef d hd hb f • z=f.val z := by
  let originalTargetAction:=(generalCoreTargetMobiusData g orders s t ho hdef d hd hb).nativeAction
  apply _root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint_injective
  rw [←(generalCoreTargetMobiusData g orders s t ho hdef d hd hb).nativeAction_boundary]
  exact nativeConformalSubgroupMobiusHom_action _
    (generalCoreTargetGroup_conformal g orders s t ho hdef d hd hb) f z

end
end LowDimensionalTopology.Geometry.Fuchsian
