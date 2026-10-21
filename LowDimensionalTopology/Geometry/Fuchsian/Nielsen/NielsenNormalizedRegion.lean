/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Hyperbolic.Models.Disc.ExtendedCarrier
public import LowDimensionalTopology.Geometry.Hyperbolic.Convexity.IdealHull.NielsenBoundaryChart
public import LowDimensionalTopology.Geometry.Fuchsian.Nielsen.NielsenConjugation
@[expose] public section
open Set
open scoped Topology OnePoint Complex.UnitDisc UpperHalfPlane
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
noncomputable section

theorem nielsen_cayley_image_halfPlanePoint (S : Set ℍ) :
    Hyperbolic.extendedCayley '' (Hyperbolic.extendedHalfPlanePoint '' S)=Hyperbolic.extendedDiscPoint '' (Hyperbolic.halfPlaneToDisc '' S) := by
  rw [Set.image_image,Set.image_image]
  congr 1
  funext z
  change Hyperbolic.extendedCayley (((z : ℍ) : ℂ) : OnePoint ℂ)=(((Hyperbolic.halfPlaneToDisc z : 𝔻) : ℂ) : OnePoint ℂ)
  exact Hyperbolic.extendedCayley_halfPlane z

theorem FuchsianDisc.nielsenHalfPlane_limit_subset
    {H : Subgroup Mobius.complexMobiusGroup}
    (D : FuchsianDisc H) (hD : D.carrier=Hyperbolic.openHalfPlaneSet) : DiscreteGroups.mobiusLimitSet H⊆Hyperbolic.halfPlaneIdealBoundary := by
  have hh:=D.loxodromic_limit_subset_frontier
  rwa [hD,nielsen_openHalfPlane_frontier] at hh

theorem FuchsianDisc.nielsenHalfPlaneArcRegion_eq_cayleySupporting
    {H : Subgroup Mobius.complexMobiusGroup}
    (D : FuchsianDisc H)
    (hD : D.carrier=Hyperbolic.openHalfPlaneSet)
    (hH : DiscreteGroups.IsNonElementary H)
    (hinf : (∞ : OnePoint ℂ)∈DiscreteGroups.mobiusLimitSet H) :
    Hyperbolic.nielsenHalfPlaneArcRegion (DiscreteGroups.mobiusLimitSet H)=
      Hyperbolic.halfPlaneToDisc ⁻¹' nielsenSupportingRegion (DiscreteGroups.Action.Actions.subgroupConjugate Hyperbolic.cayleyMobius H) := by
  let E:=D.nielsenConjugate Hyperbolic.cayleyMobius
  have hE : E.carrier=Hyperbolic.extendedUnitDisc:=by
    rw [Fuchsian.FuchsianDisc.nielsenConjugate_carrier,hD,cayleyMobius_image_openHalfPlane]
  have hA : Hyperbolic.nielsenCayleyIdealSet (Hyperbolic.nielsenHalfPlaneRealSet (DiscreteGroups.mobiusLimitSet H))=
      nielsenIdealLimitSet (DiscreteGroups.Action.Actions.subgroupConjugate Hyperbolic.cayleyMobius H):=by
    apply (Set.image_injective.mpr OnePoint.coe_injective)
    rw [Hyperbolic.nielsen_cayleyIdealSet_image _ (D.nielsenHalfPlane_limit_subset hD) hinf,
      E.nielsenIdealLimitSet_image hE]
    exact nielsen_mobiusLimitSet_conjugation H Hyperbolic.cayleyMobius
  rw [Hyperbolic.nielsenHalfPlaneArcRegion_eq_cayleySupport _ (DiscreteGroups.mobiusLimitSet_isClosed H)
    (Hyperbolic.nielsenHalfPlaneRealSet_infinite _ (fun hf=>DiscreteGroups.mobiusLimitSet_not_countable H hH
      hf.countable)
      (D.nielsenHalfPlane_limit_subset hD) hinf).nonempty hinf,hA]
  rfl

theorem FuchsianDisc.nielsenHalfPlaneArcRegion_cayley_image
    {H : Subgroup Mobius.complexMobiusGroup}
    (D : FuchsianDisc H)
    (hD : D.carrier=Hyperbolic.openHalfPlaneSet)
    (hH : DiscreteGroups.IsNonElementary H)
    (hinf : (∞ : OnePoint ℂ)∈DiscreteGroups.mobiusLimitSet H) :
    Hyperbolic.extendedCayley '' (Hyperbolic.extendedHalfPlanePoint '' Hyperbolic.nielsenHalfPlaneArcRegion
      (DiscreteGroups.mobiusLimitSet H))=
      Hyperbolic.extendedDiscPoint '' nielsenSupportingRegion (DiscreteGroups.Action.Actions.subgroupConjugate Hyperbolic.cayleyMobius H) := by
  rw [nielsen_cayley_image_halfPlanePoint,D.nielsenHalfPlaneArcRegion_eq_cayleySupporting hD hH hinf,
    Set.image_preimage_eq (f:=Hyperbolic.halfPlaneToDisc) _ Hyperbolic.cayleyHomeomorph.surjective]

theorem FuchsianDisc.nielsenHalfPlaneArcRegion_isOpen
    {H : Subgroup Mobius.complexMobiusGroup}
    (D : FuchsianDisc H)
    (hD : D.carrier=Hyperbolic.openHalfPlaneSet)
    (hH : DiscreteGroups.IsNonElementary H)
    (hinf : (∞ : OnePoint ℂ)∈DiscreteGroups.mobiusLimitSet H) :
    IsOpen (Hyperbolic.nielsenHalfPlaneArcRegion (DiscreteGroups.mobiusLimitSet H)) :=
  Hyperbolic.nielsenHalfPlaneArcRegion_isOpen _ (DiscreteGroups.mobiusLimitSet_isClosed H)
    (fun hf=>DiscreteGroups.mobiusLimitSet_not_countable H hH hf.countable) (D.nielsenHalfPlane_limit_subset hD) hinf

theorem FuchsianDisc.nielsenHalfPlaneArcRegion_hConvex
    {H : Subgroup Mobius.complexMobiusGroup}
    (D : FuchsianDisc H)
    (hD : D.carrier=Hyperbolic.openHalfPlaneSet)
    (hH : DiscreteGroups.IsNonElementary H)
    (hinf : (∞ : OnePoint ℂ)∈DiscreteGroups.mobiusLimitSet H) :
    Hyperbolic.HConvex (Hyperbolic.nielsenHalfPlaneArcRegion (DiscreteGroups.mobiusLimitSet H)) :=
  Hyperbolic.nielsenHalfPlaneArcRegion_hConvex _ (DiscreteGroups.mobiusLimitSet_isClosed H)
    (fun hf=>DiscreteGroups.mobiusLimitSet_not_countable H hH hf.countable) (D.nielsenHalfPlane_limit_subset hD) hinf

theorem FuchsianDisc.nielsenHalfPlaneArcRegion_nonempty
    {H : Subgroup Mobius.complexMobiusGroup}
    (D : FuchsianDisc H)
    (hD : D.carrier=Hyperbolic.openHalfPlaneSet)
    (hH : DiscreteGroups.IsNonElementary H)
    (hinf : (∞ : OnePoint ℂ)∈DiscreteGroups.mobiusLimitSet H) :
    (Hyperbolic.nielsenHalfPlaneArcRegion (DiscreteGroups.mobiusLimitSet H)).Nonempty :=
  Hyperbolic.nielsenHalfPlaneArcRegion_nonempty _ (DiscreteGroups.mobiusLimitSet_isClosed H)
    (fun hf=>DiscreteGroups.mobiusLimitSet_not_countable H hH hf.countable) (D.nielsenHalfPlane_limit_subset hD) hinf

/-- Actual-action invariance of the source-defined complementary-arc region in its true half-plane chart. -/
theorem FuchsianDisc.nielsenHalfPlaneArcRegion_invariant
    {H : Subgroup Mobius.complexMobiusGroup}
    (D : FuchsianDisc H)
    (hD : D.carrier=Hyperbolic.openHalfPlaneSet)
    (hH : DiscreteGroups.IsNonElementary H)
    (hinf : (∞ : OnePoint ℂ)∈DiscreteGroups.mobiusLimitSet H) :
    ∀g : H,∀p∈Hyperbolic.extendedHalfPlanePoint '' Hyperbolic.nielsenHalfPlaneArcRegion (DiscreteGroups.mobiusLimitSet
      H),
      g • p∈Hyperbolic.extendedHalfPlanePoint '' Hyperbolic.nielsenHalfPlaneArcRegion (DiscreteGroups.mobiusLimitSet H) := by
  let K:=DiscreteGroups.Action.Actions.subgroupConjugate Hyperbolic.cayleyMobius H
  let E:=D.nielsenConjugate Hyperbolic.cayleyMobius
  have hE : E.carrier=Hyperbolic.extendedUnitDisc:=by
    rw [Fuchsian.FuchsianDisc.nielsenConjugate_carrier,hD,cayleyMobius_image_openHalfPlane]
  have hK : DiscreteGroups.IsNonElementary K:=hH.conjugation Hyperbolic.cayleyMobius
  intro g p hp
  have hCp : Hyperbolic.cayleyMobius • p∈Hyperbolic.extendedDiscPoint '' nielsenSupportingRegion K:=by
    rw [←D.nielsenHalfPlaneArcRegion_cayley_image hD hH hinf]
    exact mem_image_of_mem _ hp
  let k : K:=⟨Hyperbolic.cayleyMobius*g.val*Hyperbolic.cayleyMobius⁻¹,
    (DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff _ H _).mpr ⟨g.val,g.property,rfl⟩⟩
  have hi:=E.nielsenSupportingRegion_invariant hE hK k _ hCp
  have hgp : Hyperbolic.cayleyMobius • (g • p)∈Hyperbolic.extendedDiscPoint '' nielsenSupportingRegion K:=by
    convert hi using 1
    change Hyperbolic.cayleyMobius • (g.val •
      p)=(Hyperbolic.cayleyMobius*g.val*Hyperbolic.cayleyMobius⁻¹) • (Hyperbolic.cayleyMobius • p)
    simp only [mul_smul,inv_smul_smul]
  rw [←D.nielsenHalfPlaneArcRegion_cayley_image hD hH hinf] at hgp
  obtain ⟨q,hq,hqe⟩:=hgp
  exact Hyperbolic.cayleyMobius.val.injective hqe ▸ hq

/-- Genuine source minimality, obtained from actual limit-set closure and proved geometric hull facts. -/
theorem FuchsianDisc.nielsenHalfPlaneArcRegion_minimal
    {H : Subgroup Mobius.complexMobiusGroup}
    (D : FuchsianDisc H)
    (hD : D.carrier=Hyperbolic.openHalfPlaneSet)
    (hH : DiscreteGroups.IsNonElementary H)
    (hinf : (∞ : OnePoint ℂ)∈DiscreteGroups.mobiusLimitSet H)
    (S : Set ℍ) (hopen : IsOpen S) (hne : S.Nonempty) (hc : Hyperbolic.HConvex S)
    (hi : ∀g : H,∀p∈Hyperbolic.extendedHalfPlanePoint '' S,g • p∈Hyperbolic.extendedHalfPlanePoint '' S) :
    Hyperbolic.nielsenHalfPlaneArcRegion (DiscreteGroups.mobiusLimitSet H)⊆S := by
  let K:=DiscreteGroups.Action.Actions.subgroupConjugate Hyperbolic.cayleyMobius H
  let E:=D.nielsenConjugate Hyperbolic.cayleyMobius
  have hE : E.carrier=Hyperbolic.extendedUnitDisc:=by
    rw [Fuchsian.FuchsianDisc.nielsenConjugate_carrier,hD,cayleyMobius_image_openHalfPlane]
  have hK : DiscreteGroups.IsNonElementary K:=hH.conjugation Hyperbolic.cayleyMobius
  have hlim:=nielsen_limitSet_subset_closure H hH (Hyperbolic.extendedHalfPlanePoint '' S) (hne.image _) hi
  have hcl : DiscreteGroups.mobiusLimitSet K⊆closure (Hyperbolic.extendedDiscPoint '' (Hyperbolic.halfPlaneToDisc '' S)):=by
    rw [←nielsen_mobiusLimitSet_conjugation H Hyperbolic.cayleyMobius]
    have hh:=image_mono hlim (f:=Hyperbolic.extendedCayley)
    have hclosure:=image_closure_subset_closure_image (s:=Hyperbolic.extendedHalfPlanePoint ''
      S) Hyperbolic.extendedCayley.continuous
    rw [nielsen_cayley_image_halfPlanePoint] at hclosure
    exact hh.trans hclosure
  have hm:=E.nielsenSupportingRegion_minimal_from_sphericalClosure hE hK
    (Hyperbolic.halfPlaneToDisc '' S) (Hyperbolic.cayleyHomeomorph.isOpenMap _ hopen) (hne.image _)
    ((Hyperbolic.hConvex_iff_cayley_discHConvex S).mp hc) hcl
  intro z hz
  rw [D.nielsenHalfPlaneArcRegion_eq_cayleySupporting hD hH hinf] at hz
  exact Hyperbolic.cayleyHomeomorph.injective.mem_set_image.mp (hm hz)

end
end LowDimensionalTopology.Geometry.Fuchsian
