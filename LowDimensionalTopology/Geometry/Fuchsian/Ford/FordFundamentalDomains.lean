/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Fuchsian.Ford.FordExteriorGeometry
public import LowDimensionalTopology.Geometry.Fuchsian.Dirichlet.DirichletGeometry
public import LowDimensionalTopology.Geometry.Fuchsian.Ford.FordOrdinaryAdapters
public import LowDimensionalTopology.Geometry.Hyperbolic.Models.HalfPlane.FullHalfPlaneIsometries
@[expose] public section
open Set Filter MeasureTheory
open scoped Topology OnePoint Pointwise UpperHalfPlane MatrixGroups
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Surfaces LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Inversive LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
noncomputable section

/-- The original actual Mobius subgroup in the standard half-plane model. -/
structure HalfPlaneFuchsianGroup (H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) where
  preserves : ∀g : H,g.val.val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet=_root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet
  discrete : _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup H

def HalfPlaneFuchsianGroup.fullHom {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P :
  HalfPlaneFuchsianGroup H) :
    H→*_root_.LowDimensionalTopology.Geometry.Hyperbolic.fullHalfPlaneGroup where
  toFun g:=⟨_root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusToFull g.val,P.preserves g⟩
  map_one':=rfl
  map_mul' _ _:=rfl

def HalfPlaneFuchsianGroup.nativeHom {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P
  : HalfPlaneFuchsianGroup H) :
    H→*(ℍ ≃ᵢ ℍ):=_root_.LowDimensionalTopology.Geometry.Hyperbolic.fullHalfPlaneNativeHom.comp P.fullHom

@[instance_reducible]
def HalfPlaneFuchsianGroup.nativeAction {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P : HalfPlaneFuchsianGroup H) :
    MulAction H ℍ:=MulAction.compHom ℍ P.nativeHom

/-- The native action is exactly the original sphere action on every actual finite point. -/
theorem HalfPlaneFuchsianGroup.nativeAction_boundary {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : HalfPlaneFuchsianGroup H) (g : H) (z : ℍ) :
    letI :=P.nativeAction
    g.val.val (_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint z)=_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint (g • z) := by
  let :=P.nativeAction
  exact _root_.LowDimensionalTopology.Geometry.Hyperbolic.fullHalfPlaneNativeEquiv_action (P.fullHom g) z

theorem HalfPlaneFuchsianGroup.nativeAction_realSL {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : HalfPlaneFuchsianGroup H) (g : H) (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A=g.val) (z : ℍ) :
    letI :=P.nativeAction
    g • z=A • z := by
  let :=P.nativeAction
  apply _root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint_injective
  rw [←P.nativeAction_boundary,←hA]
  exact _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_action A z

theorem realSL_im_lt_iff_denominator (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (z : ℍ) :
    (A • z).im<z.im ↔ 1<‖realSLDenominator A z‖ := by
  have hp : 0<Complex.normSq (realSLDenominator A z):=
    UpperHalfPlane.normSq_denom_pos (Matrix.SpecialLinearGroup.mapGL ℝ A) z.im_ne_zero
  rw [realSL_im_action,div_lt_iff₀ hp,Complex.normSq_eq_norm_sq]
  constructor
  · intro h
    by_contra hn
    have hnle : ‖realSLDenominator A z‖≤1:=le_of_not_gt hn
    have hs : ‖realSLDenominator A z‖^2≤1:=by nlinarith [norm_nonneg (realSLDenominator A z)]
    have hm:=mul_le_mul_of_nonneg_left hs z.im_pos.le
    nlinarith
  · intro h
    have hs : 1<‖realSLDenominator A z‖^2:=by nlinarith
    have hm:=mul_pos z.im_pos (sub_pos.mpr hs)
    nlinarith

theorem strictFordRegion_im_action {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : HalfPlaneFuchsianGroup H) (hsep : HasSeparatingMobiusNeighborhood H ∞)
    (z : ℍ) (hz : z∈strictFordRegion H) (g : H) (hg : g≠1) :
    letI :=P.nativeAction
    (g • z).im<z.im := by
  let :=P.nativeAction
  obtain ⟨A,hA⟩:=mobius_preserves_halfPlane_exists_SL g.val (P.preserves g)
  have hAH : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A∈H:=hA ▸ g.property
  have hc : A 1 0≠0:=by
    intro hc
    have he:=separating_infty_affine_identity H hsep A hAH hc
    exact hg (Subtype.val_injective (hA.symm.trans he))
  rw [P.nativeAction_realSL g A hA]
  exact (realSL_im_lt_iff_denominator A z).mpr (hz A hAH hc)

theorem strictFordRegion_orbit_unique {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : HalfPlaneFuchsianGroup H) (hsep : HasSeparatingMobiusNeighborhood H ∞)
    (x y : ℍ) (hx : x∈strictFordRegion H) (hy : y∈strictFordRegion H) :
    letI :=P.nativeAction
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitProjection H ℍ x=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitProjection H ℍ y→x=y := by
  let :=P.nativeAction
  intro hxy
  obtain ⟨g,hgy⟩:=(Quotient.exact hxy : MulAction.orbitRel H ℍ x y)
  change g • y=x at hgy
  by_cases hg : g=1
  · simpa only [hg,one_smul] using hgy.symm
  · have h1:=strictFordRegion_im_action P hsep y hy g hg
    have h2:=strictFordRegion_im_action P hsep x hx g⁻¹ (inv_ne_one.mpr hg)
    have hback : g⁻¹ • x=y:=by rw [←hgy,inv_smul_smul]
    rw [hgy] at h1
    rw [hback] at h2
    exact False.elim (lt_asymm h1 h2)

theorem strictFordRegion_closure_meetsEveryOrbit {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : HalfPlaneFuchsianGroup H) (hsep : HasSeparatingMobiusNeighborhood H ∞) :
    letI :=P.nativeAction
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.MeetsEveryOrbit H ℍ (closure (strictFordRegion H)) := by
  let :=P.nativeAction
  intro z
  obtain ⟨B,hB,_hheight,hBext⟩:=exists_ford_exterior_of_separating_infty H P.discrete hsep z
  refine ⟨⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B,hB⟩,?_⟩
  rw [P.nativeAction_realSL _ B rfl,closure_strictFordRegion]
  exact hBext

/-- The genuine sphere group acts on the actual half-plane and its Ford region is a genuine fundamental domain. -/
theorem strictFordRegion_fundamental_of_separating {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : HalfPlaneFuchsianGroup H) (hsep : HasSeparatingMobiusNeighborhood H ∞) :
    letI :=P.nativeAction
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain H ℍ volume (strictFordRegion H) := by
  let :=P.nativeAction
  refine ⟨strictFordRegion_isOpen H P.discrete hsep,
    strictFordRegion_isConnected H P.discrete hsep,?_,strictFordRegion_frontier_volume_zero H P.discrete hsep⟩
  exact exists_fundamentalSet_between _ _ subset_closure
    (strictFordRegion_closure_meetsEveryOrbit P hsep)
    (fun x hx y hy hxy=>strictFordRegion_orbit_unique P hsep x y hx hy hxy)


/-- The exact original ordinary/free infinity convention supplies the full genuine Ford-domain conclusion. -/
theorem strictFordRegion_isFundamentalDomain_of_infty_ordinary_free {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : HalfPlaneFuchsianGroup H) (hinf : (∞ : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)∈_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusOrdinarySet H)
    (hfree : ∀g : H,g • (∞ : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)=∞→g=1) :
    letI :=P.nativeAction
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain H ℍ volume (strictFordRegion H) :=
  strictFordRegion_fundamental_of_separating P
    (separatingMobiusNeighborhood_of_ordinary_all H P.discrete ∞ hinf hfree)

/-- The existing source Fuchsian-disc data specialize to the actual standard half-plane model. -/
theorem HalfPlaneFuchsianGroup.ofFuchsianDisc {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D : FuchsianDisc H) (hD :
      D.carrier=_root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet) : HalfPlaneFuchsianGroup H where
  preserves g:=by rw [←hD];exact D.image_eq g
  discrete:=D.discrete

/-- Existing whole-disc normalization supplies this native data for every actual Fuchsian model. -/
theorem FuchsianDisc.normalizedHalfPlaneData {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D : FuchsianDisc H) : HalfPlaneFuchsianGroup D.normalizedGroup where
  preserves g:=D.normalizedGroup_preserves_halfPlane g.val g.property
  discrete:=D.normalizedGroup_discrete

end
end LowDimensionalTopology.Geometry.Fuchsian
