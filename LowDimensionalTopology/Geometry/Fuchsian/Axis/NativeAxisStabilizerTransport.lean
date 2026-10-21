module
public import LowDimensionalTopology.Geometry.Fuchsian.Axis.DihedralAxisFundamentalDomains
public import LowDimensionalTopology.Geometry.Fuchsian.Axis.CyclicAxisFundamentalDomains
public import LowDimensionalTopology.Geometry.Fuchsian.Dirichlet.SimpleAxisDirichletRegions
@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set MeasureTheory
open scoped OnePoint Pointwise UpperHalfPlane Topology
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- The compactified axis trace is exactly the original embedding of the native imaginary geodesic. -/
theorem imaginaryAxis_boundary_image :
    _root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint '' (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical 0).carrier = _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedImaginaryAxis := by
  ext p
  constructor
  · rintro ⟨z,hz,rfl⟩
    refine ⟨Real.log z.im,?_⟩
    change ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.imaginaryAxisParam (Real.log z.im):ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) = ((z:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)
    apply congrArg ((↑) : ℂ → _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.imaginaryAxisParam_coe,Real.exp_log z.im_pos]
    apply Complex.ext
    · simpa only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,mul_zero,zero_mul,sub_zero,UpperHalfPlane.coe_re] using hz.symm
    · simp
  · rintro ⟨t,rfl⟩
    refine ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.imaginaryAxisParam t,?_,rfl⟩
    change (_root_.LowDimensionalTopology.Geometry.Hyperbolic.imaginaryAxisParam t).re = 0
    simp [_root_.LowDimensionalTopology.Geometry.Hyperbolic.imaginaryAxisParam]

/-- The full axis subgroup inside the original subgroup, without changing its elements. -/
def nativeAxisStabilizer (H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) : Subgroup H :=
  (_root_.LowDimensionalTopology.Geometry.Surfaces.mobiusSetStabilizer H
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedImaginaryAxis).subgroupOf H

/-- Native set stabilization is exactly stabilization of the actual extended axis trace. -/
theorem HalfPlaneFuchsianGroup.nativeAxisStabilizer_eq {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : HalfPlaneFuchsianGroup H) :
    letI := P.nativeAction
    nativeAxisStabilizer H = MulAction.stabilizer H (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical 0).carrier := by
  let nativeAxisStabilizerEqualityAction := P.nativeAction
  have hi : Function.Injective (Set.image _root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint) := Set.image_injective.mpr _root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint_injective
  ext g
  have hcomm : _root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint '' ((g • ·) ''
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical 0).carrier) =
      g.val.val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedImaginaryAxis := by
    rw [←imaginaryAxis_boundary_image,image_image,image_image]
    congr 1
    funext z
    exact (P.nativeAction_boundary g z).symm
  change (g.val ∈ H ∧ g.val.val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedImaginaryAxis =
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedImaginaryAxis) ↔
    (g • ·) '' (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical
      0).carrier = (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical 0).carrier
  constructor
  · intro hg
    apply hi
    rw [hcomm,hg.2,imaginaryAxis_boundary_image]
  · intro hg
    refine ⟨g.property,?_⟩
    rw [←hcomm,hg,imaginaryAxis_boundary_image]

/-- The two full-stabilizer types retain exactly the same original Mobius elements. -/
def nativeAxisStabilizerEquiv (H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) :
    nativeAxisStabilizer H ≃* _root_.LowDimensionalTopology.Geometry.Surfaces.mobiusSetStabilizer H _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedImaginaryAxis :=
  Subgroup.subgroupOfEquivOfLe (_root_.LowDimensionalTopology.Geometry.Surfaces.mobiusSetStabilizer_le H
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedImaginaryAxis)

/-- Relabeling the full stabilizer does not alter its genuine native action. -/
theorem HalfPlaneFuchsianGroup.nativeAxisStabilizerEquiv_action {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : HalfPlaneFuchsianGroup H) (g : nativeAxisStabilizer H) (z : ℍ) :
    P.nativeHom g.val z = P.axisStabilizerData.nativeHom (nativeAxisStabilizerEquiv H g) z := by
  rfl

/-- Genuine orbit selectors and area pass to the literal subgroup of the parent group. -/
theorem HalfPlaneFuchsianGroup.nativeAxis_fundamental_relabel {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : HalfPlaneFuchsianGroup H) {D : Set ℍ}
    (hD : letI := P.axisStabilizerData.nativeAction
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain (_root_.LowDimensionalTopology.Geometry.Surfaces.mobiusSetStabilizer H _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedImaginaryAxis) ℍ volume D) :
    letI := P.nativeAction
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain (nativeAxisStabilizer H) ℍ volume D := by
  let nativeAxisParentRelabelAction := P.nativeAction
  let nativeAxisActualRelabelAction := P.axisStabilizerData.nativeAction
  have he (g : nativeAxisStabilizer H) (z : ℍ) :
      (Homeomorph.refl ℍ) (g • z) = nativeAxisStabilizerEquiv H g • (Homeomorph.refl ℍ) z :=
    P.nativeAxisStabilizerEquiv_action g z
  refine ⟨hD.isOpen,hD.isConnected,?_,hD.null_frontier⟩
  obtain ⟨F,hF,hDF,hFcl⟩ := hD.exists_fundamentalSet
  exact ⟨F,_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalSet.equivariant_preimage
    (nativeAxisStabilizerEquiv H) (Equiv.refl ℍ) he hF,hDF,hFcl⟩

/-- Relabeling retains the actual closed-tile compact-hit condition. -/
theorem HalfPlaneFuchsianGroup.nativeAxis_compact_hits_relabel {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : HalfPlaneFuchsianGroup H) (D : Set ℍ)
    (hD : letI := P.axisStabilizerData.nativeAction
      ∀ B : Set ℍ, IsCompact B →
        {g : _root_.LowDimensionalTopology.Geometry.Surfaces.mobiusSetStabilizer H
          _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedImaginaryAxis | ((g • ·) '' closure D ∩
          B).Nonempty}.Finite)
    (B : Set ℍ) (hB : IsCompact B) :
    letI := P.nativeAction
    {g : nativeAxisStabilizer H | ((g • ·) '' closure D ∩ B).Nonempty}.Finite := by
  let nativeAxisParentCompactRelabelAction := P.nativeAction
  let nativeAxisActualCompactRelabelAction := P.axisStabilizerData.nativeAction
  have he (g : nativeAxisStabilizer H) (z : ℍ) : g • z = nativeAxisStabilizerEquiv H g • z :=
    P.nativeAxisStabilizerEquiv_action g z
  have h := (hD B hB).preimage (nativeAxisStabilizerEquiv H).injective.injOn
  simpa only [Set.preimage_ofPred_eq,he] using h

end LowDimensionalTopology.Geometry.Fuchsian
