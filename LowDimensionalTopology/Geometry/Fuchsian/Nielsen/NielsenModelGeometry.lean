/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Mobius.Circle.GeometricDisc
public import LowDimensionalTopology.Geometry.Hyperbolic.Models.Disc.ExtendedCarrier
public import LowDimensionalTopology.Geometry.Fuchsian.Nielsen.NielsenConjugation
public import LowDimensionalTopology.Geometry.Hyperbolic.Models.HalfPlane.FullHalfPlaneIsometries
@[expose] public section
open Set
open scoped Topology OnePoint UpperHalfPlane Complex.UnitDisc
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
noncomputable section

def nielsenModelCoordinateSet
    (q : Mobius.complexMobiusGroup)
    (S : Set (OnePoint ℂ)) : Set ℍ:=
  Hyperbolic.extendedHalfPlanePoint ⁻¹' (q.val '' S)

def nielsenModelSet
    (q : Mobius.complexMobiusGroup)
    (T : Set ℍ) : Set (OnePoint ℂ):=
  q⁻¹.val '' (Hyperbolic.extendedHalfPlanePoint '' T)

theorem nielsen_mobius_image_mul
    (q r : Mobius.complexMobiusGroup)
    (S : Set (OnePoint ℂ)) :
    (q*r).val '' S=q.val '' (r.val '' S) := by rw [Set.image_image];rfl

theorem nielsen_mobius_inverse_image
    (q : Mobius.complexMobiusGroup)
    (S : Set (OnePoint ℂ)) :
    q⁻¹.val '' (q.val '' S)=S := q.val.symm_image_image S

theorem nielsen_halfPlanePoint_range : range Hyperbolic.extendedHalfPlanePoint=Hyperbolic.openHalfPlaneSet :=
  Hyperbolic.halfPlaneBoundaryPoint_range

theorem nielsen_halfPlanePoint_isOpenEmbedding : Topology.IsOpenEmbedding Hyperbolic.extendedHalfPlanePoint :=
  Hyperbolic.halfPlaneBoundaryPoint_isOpenEmbedding

theorem nielsen_modelCoordinate_image
    (q : Mobius.complexMobiusGroup)
    (S : Set (OnePoint ℂ))
    (hS : q.val '' S⊆Hyperbolic.openHalfPlaneSet) :
    Hyperbolic.extendedHalfPlanePoint '' nielsenModelCoordinateSet q S=q.val '' S := by
  rw [nielsenModelCoordinateSet,image_preimage_eq_inter_range,nielsen_halfPlanePoint_range]
  exact inter_eq_left.mpr hS

theorem nielsen_modelSet_coordinate (q : Mobius.complexMobiusGroup) (T : Set ℍ) :
    nielsenModelCoordinateSet q (nielsenModelSet q T)=T := by
  change Hyperbolic.extendedHalfPlanePoint ⁻¹' (q.val '' (q⁻¹.val '' (Hyperbolic.extendedHalfPlanePoint '' T)))=T
  rw [show q.val '' (q⁻¹.val '' (Hyperbolic.extendedHalfPlanePoint '' T))=Hyperbolic.extendedHalfPlanePoint '' T from
    q.val.image_symm_image _]
  exact nielsen_halfPlanePoint_isOpenEmbedding.injective.preimage_image T

theorem nielsen_modelSet_coordinate_inverse
    (q : Mobius.complexMobiusGroup)
    (S : Set (OnePoint ℂ))
    (hS : q.val '' S⊆Hyperbolic.openHalfPlaneSet) : nielsenModelSet q (nielsenModelCoordinateSet q S)=S := by
  rw [nielsenModelSet,nielsen_modelCoordinate_image q S hS,nielsen_mobius_inverse_image]

theorem nielsen_modelSet_subset
    {D : Set (OnePoint ℂ)}
    (q : Mobius.complexMobiusGroup)
    (hq : q.val '' D=Hyperbolic.openHalfPlaneSet)
    (T : Set ℍ) : nielsenModelSet q T⊆D := by
  have hh : Hyperbolic.extendedHalfPlanePoint '' T⊆q.val '' D:=by
    rw [hq,←nielsen_halfPlanePoint_range]
    exact image_subset_range _ _
  have hm:=image_mono hh (f:=q⁻¹.val)
  rwa [nielsen_mobius_inverse_image] at hm

theorem nielsen_modelCoordinate_nonempty
    (q : Mobius.complexMobiusGroup)
    (S : Set (OnePoint ℂ))
    (hS : q.val '' S⊆Hyperbolic.openHalfPlaneSet) (hne : S.Nonempty) :
    (nielsenModelCoordinateSet q S).Nonempty := by
  have hh : (Hyperbolic.extendedHalfPlanePoint '' nielsenModelCoordinateSet q S).Nonempty:=by
    rw [nielsen_modelCoordinate_image q S hS]
    exact hne.image _
  exact hh.of_image

theorem nielsen_modelCoordinate_isOpen
    (q : Mobius.complexMobiusGroup)
    (S : Set (OnePoint ℂ))
    (hS : IsOpen S) : IsOpen (nielsenModelCoordinateSet q S) :=
  ((Mobius.mobiusBoundaryHomeomorph q).isOpenMap _ hS).preimage nielsen_halfPlanePoint_isOpenEmbedding.continuous

theorem nielsen_modelSet_isOpen
    (q : Mobius.complexMobiusGroup)
    (T : Set ℍ)
    (hT : IsOpen T) :
    IsOpen (nielsenModelSet q T) :=
  (Mobius.mobiusBoundaryHomeomorph q⁻¹).isOpenMap _ (nielsen_halfPlanePoint_isOpenEmbedding.isOpenMap _ hT)

/-- Two actual whole-domain half-plane charts differ by a genuine native hyperbolic isometry. -/
theorem nielsen_modelCoordinate_hConvex_of_chart
    {D S : Set (OnePoint ℂ)}
    (q r : Mobius.complexMobiusGroup)
    (hq : q.val '' D=Hyperbolic.openHalfPlaneSet)
    (hr : r.val '' D=Hyperbolic.openHalfPlaneSet)
    (hSD : S⊆D)
    (hc : Hyperbolic.HConvex (nielsenModelCoordinateSet r S)) : Hyperbolic.HConvex (nielsenModelCoordinateSet q S) := by
  have hg : (q*r⁻¹).val '' Hyperbolic.openHalfPlaneSet=Hyperbolic.openHalfPlaneSet:=by
    calc
      _=q.val '' (r⁻¹.val '' Hyperbolic.openHalfPlaneSet):=nielsen_mobius_image_mul q r⁻¹ _
      _=q.val '' D:=congrArg (fun U=>q.val '' U) (by rw [←hr,nielsen_mobius_inverse_image])
      _=Hyperbolic.openHalfPlaneSet:=hq
  obtain ⟨A,hA⟩:=mobius_preserves_halfPlane_exists_SL (q*r⁻¹) hg
  have hact (w : ℍ) : Hyperbolic.extendedHalfPlanePoint (A • w)=(q*r⁻¹) • Hyperbolic.extendedHalfPlanePoint w:=by
    rw [←hA]
    exact (Hyperbolic.realSLMobius_action A w).symm
  have he : nielsenModelCoordinateSet q S=(fun w : ℍ=>A • w) '' nielsenModelCoordinateSet r S:=by
    ext z
    constructor
    · rintro ⟨p,hp,hpz⟩
      have hrp : r.val p∈Hyperbolic.openHalfPlaneSet:=by rw [←hr];exact mem_image_of_mem _ (hSD hp)
      obtain ⟨w,hw⟩:=nielsen_halfPlanePoint_range.symm ▸ hrp
      refine ⟨w,⟨p,hp,hw.symm⟩,?_⟩
      apply nielsen_halfPlanePoint_isOpenEmbedding.injective
      rw [hact,hw]
      change (q*r⁻¹) • (r • p)=Hyperbolic.extendedHalfPlanePoint z
      change q • p=Hyperbolic.extendedHalfPlanePoint z at hpz
      simpa only [mul_smul,inv_smul_smul] using hpz
    · rintro ⟨w,⟨p,hp,hpw⟩,rfl⟩
      refine ⟨p,hp,?_⟩
      rw [hact,←hpw]
      change q • p=(q*r⁻¹) • (r • p)
      simp only [mul_smul,inv_smul_smul]
  rw [he]
  exact hc.isometry_image (isometry_smul ℍ A)

theorem nielsen_modelCoordinate_hConvex_iff
    {D S : Set (OnePoint ℂ)}
    (q r : Mobius.complexMobiusGroup)
    (hq : q.val '' D=Hyperbolic.openHalfPlaneSet)
    (hr : r.val '' D=Hyperbolic.openHalfPlaneSet)
    (hSD : S⊆D) :
    Hyperbolic.HConvex (nielsenModelCoordinateSet q S) ↔ Hyperbolic.HConvex (nielsenModelCoordinateSet r S) :=
  ⟨nielsen_modelCoordinate_hConvex_of_chart r q hr hq hSD,
    nielsen_modelCoordinate_hConvex_of_chart q r hq hr hSD⟩

/-- Genuine hyperbolic convexity in an arbitrary original geometric disc, using its proved
whole-domain half-plane model; the preceding theorem proves chart independence. -/
def FuchsianDisc.HyperbolicallyConvex
    {H : Subgroup Mobius.complexMobiusGroup}
    (D : FuchsianDisc H)
    (S : Set (OnePoint ℂ)) : Prop:=Hyperbolic.HConvex (nielsenModelCoordinateSet D.halfPlaneNormalizer S)

theorem FuchsianDisc.hyperbolicallyConvex_iff_chart
    {H : Subgroup Mobius.complexMobiusGroup}
    (D : FuchsianDisc H)
    (q : Mobius.complexMobiusGroup)
    (hq : q.val '' D.carrier=Hyperbolic.openHalfPlaneSet)
    (S : Set (OnePoint ℂ)) (hS : S⊆D.carrier) :
    D.HyperbolicallyConvex S ↔ Hyperbolic.HConvex (nielsenModelCoordinateSet q S) :=
  nielsen_modelCoordinate_hConvex_iff D.halfPlaneNormalizer q D.halfPlaneNormalizer_image hq hS


theorem nielsen_modelSet_openHalfPlane
    {D : Set (OnePoint ℂ)}
    (q : Mobius.complexMobiusGroup)
    (hq : q.val '' D=Hyperbolic.openHalfPlaneSet)
    (L : Hyperbolic.HalfPlaneLine)
    (z : ℍ)
    (hz : z∉L.carrier) :
    nielsenModelSet q (Hyperbolic.openHHalfPlane L z)=
      connectedComponentIn (D\nielsenModelSet q L.carrier) (q⁻¹.val (Hyperbolic.extendedHalfPlanePoint z)) := by
  change q⁻¹.val '' (Hyperbolic.extendedHalfPlanePoint '' connectedComponentIn L.carrierᶜ z)=_
  rw [Hyperbolic.embedding_image_connectedComponentIn nielsen_halfPlanePoint_isOpenEmbedding.isEmbedding hz]
  change (Mobius.mobiusBoundaryHomeomorph q⁻¹) ''
    connectedComponentIn (Hyperbolic.extendedHalfPlanePoint '' L.carrierᶜ) (Hyperbolic.extendedHalfPlanePoint z)=_
  rw [(Mobius.mobiusBoundaryHomeomorph q⁻¹).image_connectedComponentIn (mem_image_of_mem _ hz),
    image_compl_eq_range_sdiff_image nielsen_halfPlanePoint_isOpenEmbedding.injective,
    nielsen_halfPlanePoint_range]
  change connectedComponentIn (q⁻¹.val '' (Hyperbolic.openHalfPlaneSet\Hyperbolic.extendedHalfPlanePoint '' L.carrier))
    (q⁻¹.val (Hyperbolic.extendedHalfPlanePoint z))=_
  rw [image_sdiff q⁻¹.val.injective]
  have he : q⁻¹.val '' Hyperbolic.openHalfPlaneSet=D:=by rw [←hq,nielsen_mobius_inverse_image]
  rw [he]
  rfl

theorem nielsen_modelCoordinate_identity (S : Set ℍ) :
    nielsenModelCoordinateSet 1 (Hyperbolic.extendedHalfPlanePoint '' S)=S := by
  rw [nielsenModelCoordinateSet,show (1 : Mobius.complexMobiusGroup).val=(1 : Equiv.Perm (OnePoint ℂ)) from rfl,
    Equiv.Perm.coe_one,Set.image_id]
  exact nielsen_halfPlanePoint_isOpenEmbedding.injective.preimage_image S

theorem FuchsianDisc.hyperbolicallyConvex_halfPlane
    {H : Subgroup Mobius.complexMobiusGroup}
    (D : FuchsianDisc H)
    (hD : D.carrier=Hyperbolic.openHalfPlaneSet)
    (S : Set ℍ) :
    D.HyperbolicallyConvex (Hyperbolic.extendedHalfPlanePoint '' S) ↔ Hyperbolic.HConvex S := by
  have hq : (1 : Mobius.complexMobiusGroup).val '' D.carrier=Hyperbolic.openHalfPlaneSet:=by
    rw [hD]
    change id '' Hyperbolic.openHalfPlaneSet=Hyperbolic.openHalfPlaneSet
    exact image_id _
  have hsub : Hyperbolic.extendedHalfPlanePoint '' S⊆D.carrier:=by
    rw [hD,←nielsen_halfPlanePoint_range]
    exact image_subset_range _ _
  rw [D.hyperbolicallyConvex_iff_chart 1 hq _ hsub,nielsen_modelCoordinate_identity]


theorem nielsen_modelSet_point_mem
    (q : Mobius.complexMobiusGroup)
    (T : Set ℍ)
    (z : ℍ) :
    q⁻¹.val (Hyperbolic.extendedHalfPlanePoint z)∈nielsenModelSet q T ↔ z∈T := by
  constructor
  · rintro ⟨p,⟨w,hw,rfl⟩,he⟩
    exact nielsen_halfPlanePoint_isOpenEmbedding.injective (q⁻¹.val.injective he) ▸ hw
  · intro hz
    exact ⟨Hyperbolic.extendedHalfPlanePoint z,mem_image_of_mem _ hz,rfl⟩


theorem nielsen_inverseCayley_discPoint (z : 𝔻) :
    Hyperbolic.cayleyMobius⁻¹.val (Hyperbolic.extendedDiscPoint z)=Hyperbolic.extendedHalfPlanePoint (Hyperbolic.discToHalfPlane z) := by
  apply Hyperbolic.cayleyMobius.val.injective
  change Hyperbolic.cayleyMobius.val (Hyperbolic.cayleyMobius.val.symm (Hyperbolic.extendedDiscPoint z))=_
  rw [Hyperbolic.cayleyMobius.val.apply_symm_apply,Hyperbolic.cayleyMobius_apply]
  change (((z : 𝔻) : ℂ) : OnePoint ℂ)=Hyperbolic.extendedCayley (((Hyperbolic.discToHalfPlane z : ℍ) : ℂ) : OnePoint ℂ)
  rw [Hyperbolic.extendedCayley_halfPlane,Hyperbolic.halfPlaneToDisc_discToHalfPlane]

theorem nielsen_modelCoordinate_inverseCayley (S : Set 𝔻) :
    nielsenModelCoordinateSet Hyperbolic.cayleyMobius⁻¹ (Hyperbolic.extendedDiscPoint '' S)=Hyperbolic.discToHalfPlane '' S := by
  rw [nielsenModelCoordinateSet,Set.image_image]
  simp_rw [nielsen_inverseCayley_discPoint]
  rw [←Set.image_image]
  exact nielsen_halfPlanePoint_isOpenEmbedding.injective.preimage_image _

theorem FuchsianDisc.hyperbolicallyConvex_disc
    {H : Subgroup Mobius.complexMobiusGroup}
    (D : FuchsianDisc H)
    (hD : D.carrier=Hyperbolic.extendedUnitDisc)
    (S : Set 𝔻) :
    D.HyperbolicallyConvex (Hyperbolic.extendedDiscPoint '' S) ↔ Hyperbolic.DiscHConvex S := by
  have hq : Hyperbolic.cayleyMobius⁻¹.val '' D.carrier=Hyperbolic.openHalfPlaneSet:=by
    rw [hD,←cayleyMobius_image_openHalfPlane,nielsen_mobius_inverse_image]
  have hsub : Hyperbolic.extendedDiscPoint '' S⊆D.carrier:=by
    rintro _ ⟨z,_,rfl⟩
    rw [hD]
    exact ⟨(z : ℂ),z.norm_lt_one,rfl⟩
  rw [D.hyperbolicallyConvex_iff_chart Hyperbolic.cayleyMobius⁻¹ hq _ hsub,nielsen_modelCoordinate_inverseCayley,
    Hyperbolic.hConvex_iff_cayley_discHConvex,Set.image_image]
  have he : Hyperbolic.halfPlaneToDisc ∘ Hyperbolic.discToHalfPlane=id:=funext Hyperbolic.halfPlaneToDisc_discToHalfPlane
  change Hyperbolic.DiscHConvex ((Hyperbolic.halfPlaneToDisc ∘ Hyperbolic.discToHalfPlane) ''
    S) ↔ Hyperbolic.DiscHConvex S
  rw [he,Set.image_id]

end
end LowDimensionalTopology.Geometry.Fuchsian
