/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Mobius.Circle.GeometricDisc
public import LowDimensionalTopology.Geometry.Hyperbolic.Models.Disc.ExtendedCarrier
public import LowDimensionalTopology.Geometry.Hyperbolic.ModelMaps.PoincareKlein.Ambient
public import LowDimensionalTopology.Geometry.Fuchsian.Nielsen.NielsenConvexity
public import LowDimensionalTopology.Geometry.Hyperbolic.Convexity.IdealHull.NielsenHalfspaces
public import LowDimensionalTopology.Geometry.Fuchsian.Basic.FuchsianNormalization
public import LowDimensionalTopology.Geometry.Hyperbolic.Metric.HyperbolicBalls
@[expose] public section
open Set Filter
open scoped Topology OnePoint Complex.UnitDisc UpperHalfPlane
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
noncomputable section

/-- The finite complex coordinates of the group's true spherical limit set. -/
def nielsenIdealLimitSet (H : Subgroup Mobius.complexMobiusGroup) : Set ℂ:=
  ((↑) : ℂ → Mobius.ExtendedComplex) ⁻¹' DiscreteGroups.mobiusLimitSet H

theorem nielsenIdealLimitSet_isClosed (H : Subgroup Mobius.complexMobiusGroup) :
    IsClosed (nielsenIdealLimitSet H):=
  (DiscreteGroups.mobiusLimitSet_isClosed H).preimage OnePoint.continuous_coe

theorem FuchsianDisc.nielsenIdealLimitSet_unitCircle
    {H : Subgroup Mobius.complexMobiusGroup}
    (D : FuchsianDisc H) (hD : D.carrier=Hyperbolic.extendedUnitDisc) :
    ∀p∈nielsenIdealLimitSet H,‖p‖=1 := by
  intro p hp
  have hb:=D.loxodromic_limit_subset_frontier hp
  rw [hD,nielsen_unitDisc_frontier] at hb
  exact (Hyperbolic.coe_mem_extendedDiscIdealBoundary p).mp hb

theorem FuchsianDisc.nielsenIdealLimitSet_image
    {H : Subgroup Mobius.complexMobiusGroup}
    (D : FuchsianDisc H) (hD : D.carrier=Hyperbolic.extendedUnitDisc) :
    ((↑) : ℂ → Mobius.ExtendedComplex) '' nielsenIdealLimitSet H=DiscreteGroups.mobiusLimitSet H := by
  apply subset_antisymm
  · rintro _ ⟨p,hp,rfl⟩
    exact hp
  · intro p hp
    have hb:=D.loxodromic_limit_subset_frontier hp
    rw [hD,nielsen_unitDisc_frontier] at hb
    obtain ⟨z,_,rfl⟩:=hb
    exact ⟨z,hp,rfl⟩

theorem FuchsianDisc.nielsenIdealLimitSet_infinite
    {H : Subgroup Mobius.complexMobiusGroup}
    (D : FuchsianDisc H)
    (hD : D.carrier=Hyperbolic.extendedUnitDisc)
    (hH : DiscreteGroups.IsNonElementary H) :
    (nielsenIdealLimitSet H).Infinite := by
  intro hfin
  apply DiscreteGroups.mobiusLimitSet_not_countable H hH
  rw [←D.nielsenIdealLimitSet_image hD]
  exact (hfin.image _).countable

theorem FuchsianDisc.nielsenIdealLimitSet_isCompact
    {H : Subgroup Mobius.complexMobiusGroup}
    (D : FuchsianDisc H) (hD : D.carrier=Hyperbolic.extendedUnitDisc) : IsCompact (nielsenIdealLimitSet H):=
  (isCompact_sphere (0 : ℂ) 1).of_isClosed_subset (nielsenIdealLimitSet_isClosed H)
    (fun p hp=>mem_sphere_zero_iff_norm.mpr (D.nielsenIdealLimitSet_unitCircle hD p hp))

/-- The actual true ideal limit set lies in the Klein closure of every nonempty invariant native subset. -/
theorem FuchsianDisc.nielsenIdealLimitSet_subset_kleinClosure
    {H : Subgroup Mobius.complexMobiusGroup}
    (D : FuchsianDisc H)
    (hD : D.carrier=Hyperbolic.extendedUnitDisc)
    (hH : DiscreteGroups.IsNonElementary H)
    (S : Set 𝔻) (hne : S.Nonempty)
    (hi : ∀g : H,∀p∈Hyperbolic.extendedDiscPoint '' S,g • p∈Hyperbolic.extendedDiscPoint '' S) :
    nielsenIdealLimitSet H⊆closure (Hyperbolic.kleinCoordinate '' S) := by
  have hlim:=nielsen_limitSet_subset_closure H hH (Hyperbolic.extendedDiscPoint '' S) (hne.image _) hi
  intro p hp
  apply nielsen_klein_closure_ideal (D.nielsenIdealLimitSet_unitCircle hD p hp)
  have hpc:=hlim hp
  have himg : ((↑) : ℂ → Mobius.ExtendedComplex) '' (((↑) : 𝔻 → ℂ) '' S)=Hyperbolic.extendedDiscPoint '' S:=by
    rw [Set.image_image]
    rfl
  rw [←himg] at hpc
  change p∈((↑) : ℂ → Mobius.ExtendedComplex) ⁻¹' closure (((↑) : ℂ → Mobius.ExtendedComplex) '' (((↑) : 𝔻 → ℂ) ''
    S)) at hpc
  rw [Hyperbolic.onePoint_coe_preimage_closure_image] at hpc
  exact hpc

/-- The proved supporting-geodesic construction, pending its identification with complementary arcs. -/
def nielsenSupportingRegion (H : Subgroup Mobius.complexMobiusGroup) : Set 𝔻:=
  Hyperbolic.nielsenGeodesicHalfspaceIntersection (nielsenIdealLimitSet H)

theorem FuchsianDisc.nielsenSupportingRegion_eq_klein_hull
    {H : Subgroup Mobius.complexMobiusGroup}
    (D : FuchsianDisc H)
    (hD : D.carrier=Hyperbolic.extendedUnitDisc)
    (hH : DiscreteGroups.IsNonElementary H) :
    nielsenSupportingRegion H=Hyperbolic.kleinCoordinate ⁻¹' interior (closedConvexHull ℝ (nielsenIdealLimitSet H)):=
  Hyperbolic.nielsen_geodesicHalfspaces_eq_hullInterior _ (D.nielsenIdealLimitSet_infinite hD hH)
    (D.nielsenIdealLimitSet_unitCircle hD)

theorem FuchsianDisc.nielsenSupportingRegion_isOpen
    {H : Subgroup Mobius.complexMobiusGroup}
    (D : FuchsianDisc H)
    (hD : D.carrier=Hyperbolic.extendedUnitDisc)
    (hH : DiscreteGroups.IsNonElementary H) :
    IsOpen (nielsenSupportingRegion H):=
  Hyperbolic.nielsen_geodesicHalfspaces_isOpen _ (D.nielsenIdealLimitSet_infinite hD hH)
    (D.nielsenIdealLimitSet_unitCircle hD)

theorem FuchsianDisc.nielsenSupportingRegion_convex
    {H : Subgroup Mobius.complexMobiusGroup}
    (D : FuchsianDisc H)
    (hD : D.carrier=Hyperbolic.extendedUnitDisc)
    (hH : DiscreteGroups.IsNonElementary H) :
    Hyperbolic.DiscHConvex (nielsenSupportingRegion H):=
  Hyperbolic.nielsen_geodesicHalfspaces_convex _ (D.nielsenIdealLimitSet_infinite hD hH)
    (D.nielsenIdealLimitSet_unitCircle hD)

theorem FuchsianDisc.nielsenSupportingRegion_nonempty
    {H : Subgroup Mobius.complexMobiusGroup}
    (D : FuchsianDisc H)
    (hD : D.carrier=Hyperbolic.extendedUnitDisc)
    (hH : DiscreteGroups.IsNonElementary H) :
    (nielsenSupportingRegion H).Nonempty:=
  Hyperbolic.nielsen_geodesicHalfspaces_nonempty _ (D.nielsenIdealLimitSet_infinite hD hH)
    (D.nielsenIdealLimitSet_unitCircle hD)

/-- Proved minimality of the actual supporting-geodesic construction, not a least-set definition. -/
theorem FuchsianDisc.nielsenSupportingRegion_minimal
    {H : Subgroup Mobius.complexMobiusGroup}
    (D : FuchsianDisc H)
    (hD : D.carrier=Hyperbolic.extendedUnitDisc)
    (hH : DiscreteGroups.IsNonElementary H)
    (S : Set 𝔻)
    (hopen : IsOpen S)
    (hne : S.Nonempty)
    (hconv : Hyperbolic.DiscHConvex S)
    (hi : ∀g : H,∀p∈Hyperbolic.extendedDiscPoint '' S,g • p∈Hyperbolic.extendedDiscPoint '' S) : nielsenSupportingRegion H⊆S := by
  have hKconv:=(Hyperbolic.discHConvex_iff_klein_convex S).mp hconv
  have hKopen : IsOpen (Hyperbolic.kleinCoordinate '' S):=Hyperbolic.isOpenEmbedding_kleinCoordinate.isOpenMap S hopen
  have hKI : (interior (Hyperbolic.kleinCoordinate '' S)).Nonempty:=hKopen.interior_eq.symm ▸ hne.image _
  have hHull : closedConvexHull ℝ (nielsenIdealLimitSet H)⊆closure (Hyperbolic.kleinCoordinate '' S):=
    closedConvexHull_min (D.nielsenIdealLimitSet_subset_kleinClosure hD hH S hne hi) hKconv.closure isClosed_closure
  have hInt:=interior_mono hHull
  rw [hKconv.interior_closure_eq_interior_of_nonempty_interior hKI,hKopen.interior_eq] at hInt
  intro z hz
  have hzI : Hyperbolic.kleinCoordinate z∈interior (closedConvexHull ℝ (nielsenIdealLimitSet H)):=by
    rw [D.nielsenSupportingRegion_eq_klein_hull hD hH] at hz
    exact hz
  exact Hyperbolic.kleinCoordinate_injective.mem_set_image.mp (hInt hzI)


/-- The true hull interior in the plane is the inverse Klein image of the supporting region. -/
theorem FuchsianDisc.nielsenSupportingRegion_inverseKlein_image
    {H : Subgroup Mobius.complexMobiusGroup}
    (D : FuchsianDisc H)
    (hD : D.carrier=Hyperbolic.extendedUnitDisc)
    (hH : DiscreteGroups.IsNonElementary H) :
    Hyperbolic.inverseKleinFormula '' interior (closedConvexHull ℝ (nielsenIdealLimitSet H))=
      ((↑) : 𝔻 → ℂ) '' nielsenSupportingRegion H := by
  have hCB : closedConvexHull ℝ (nielsenIdealLimitSet H)⊆Metric.closedBall (0 : ℂ) 1:=
    closedConvexHull_min (fun p hp=>mem_closedBall_zero_iff.mpr (D.nielsenIdealLimitSet_unitCircle hD p hp).le)
      (convex_closedBall (0 : ℂ) 1) Metric.isClosed_closedBall
  apply subset_antisymm
  · rintro _ ⟨u,hu,rfl⟩
    have huB:=interior_mono hCB hu
    rw [interior_closedBall (0 : ℂ) (by norm_num : (1 : ℝ)≠0)] at huB
    let w : 𝔻:=Complex.UnitDisc.mk u (mem_ball_zero_iff.mp huB)
    refine ⟨Hyperbolic.kleinToPoincare w,?_,rfl⟩
    rw [D.nielsenSupportingRegion_eq_klein_hull hD hH,mem_preimage]
    change (Hyperbolic.poincareToKlein (Hyperbolic.kleinToPoincare w) : ℂ)∈interior (closedConvexHull ℝ
      (nielsenIdealLimitSet H))
    rw [Hyperbolic.poincareToKlein_kleinToPoincare]
    exact hu
  · rintro _ ⟨z,hz,rfl⟩
    rw [D.nielsenSupportingRegion_eq_klein_hull hD hH] at hz
    refine ⟨Hyperbolic.kleinCoordinate z,hz,?_⟩
    exact congrArg ((↑) : 𝔻 → ℂ) (Hyperbolic.kleinToPoincare_poincareToKlein z)

/-- The actual closure of the supporting region contains every genuine finite ideal limit point. -/
theorem FuchsianDisc.nielsenIdealLimitSet_subset_supportingClosure
    {H : Subgroup Mobius.complexMobiusGroup}
    (D : FuchsianDisc H)
    (hD : D.carrier=Hyperbolic.extendedUnitDisc)
    (hH : DiscreteGroups.IsNonElementary H) :
    nielsenIdealLimitSet H⊆closure (((↑) : 𝔻 → ℂ) '' nielsenSupportingRegion H) := by
  have hInt:=Hyperbolic.nielsen_infinite_unitCircle_hull_interior _ (D.nielsenIdealLimitSet_infinite hD hH)
    (D.nielsenIdealLimitSet_unitCircle hD)
  have hclosed : closure (interior (closedConvexHull ℝ (nielsenIdealLimitSet H)))=
      closedConvexHull ℝ (nielsenIdealLimitSet H):=by
    rw [convex_closedConvexHull.closure_interior_eq_closure_of_nonempty_interior hInt,
      isClosed_closedConvexHull.closure_eq]
  intro p hp
  have hpI : p∈closure (interior (closedConvexHull ℝ (nielsenIdealLimitSet H))):=by
    rw [hclosed]
    exact subset_closedConvexHull hp
  have hh:=image_closure_subset_closure_image Hyperbolic.continuous_inverseKleinFormula ⟨p,hpI,rfl⟩
  rw [Hyperbolic.inverseKleinFormula_norm_one (D.nielsenIdealLimitSet_unitCircle hD p hp),
    D.nielsenSupportingRegion_inverseKlein_image hD hH] at hh
  exact hh

/-- The entire spherical limit set is in the actual sphere closure of the supporting region. -/
theorem FuchsianDisc.nielsenLimitSet_subset_supportingSphereClosure
    {H : Subgroup Mobius.complexMobiusGroup}
    (D : FuchsianDisc H)
    (hD : D.carrier=Hyperbolic.extendedUnitDisc)
    (hH : DiscreteGroups.IsNonElementary H) :
    DiscreteGroups.mobiusLimitSet H⊆closure (Hyperbolic.extendedDiscPoint '' nielsenSupportingRegion H) := by
  rw [←D.nielsenIdealLimitSet_image hD]
  rintro _ ⟨p,hp,rfl⟩
  have hh:=image_closure_subset_closure_image OnePoint.continuous_coe
    ⟨p,D.nielsenIdealLimitSet_subset_supportingClosure hD hH hp,rfl⟩
  have himg : ((↑) : ℂ → Mobius.ExtendedComplex) '' (((↑) : 𝔻 → ℂ) '' nielsenSupportingRegion H)=
      Hyperbolic.extendedDiscPoint '' nielsenSupportingRegion H:=by
    rw [Set.image_image]
    rfl
  rw [himg] at hh
  exact hh


/-- Conjugating a genuine whole-disc preserver gives a genuine whole-half-plane preserver. -/
theorem nielsen_discPreserver_conjugate_halfPlane (g : Mobius.complexMobiusGroup)
    (hg : g.val '' Hyperbolic.extendedUnitDisc=Hyperbolic.extendedUnitDisc) :
    (Hyperbolic.cayleyMobius⁻¹*g*Hyperbolic.cayleyMobius).val '' Hyperbolic.openHalfPlaneSet=Hyperbolic.openHalfPlaneSet := by
  have hi : Hyperbolic.cayleyMobius⁻¹.val '' Hyperbolic.extendedUnitDisc=Hyperbolic.openHalfPlaneSet:=by
    rw [←cayleyMobius_image_openHalfPlane,Set.image_image]
    change (fun p : Mobius.ExtendedComplex=>Hyperbolic.cayleyMobius⁻¹ • (Hyperbolic.cayleyMobius •
      p)) '' Hyperbolic.openHalfPlaneSet=Hyperbolic.openHalfPlaneSet
    simp only [inv_smul_smul,Set.image_id']
  have he : (fun p : Mobius.ExtendedComplex=>(Hyperbolic.cayleyMobius⁻¹*g*Hyperbolic.cayleyMobius).val p)=
      (fun p=>Hyperbolic.cayleyMobius⁻¹.val (g.val (Hyperbolic.cayleyMobius.val p))):=rfl
  change (fun p : Mobius.ExtendedComplex=>(Hyperbolic.cayleyMobius⁻¹*g*Hyperbolic.cayleyMobius).val
    p) '' Hyperbolic.openHalfPlaneSet=Hyperbolic.openHalfPlaneSet
  rw [he,←Set.image_image Hyperbolic.cayleyMobius⁻¹.val (fun p=>g.val (Hyperbolic.cayleyMobius.val p))
    Hyperbolic.openHalfPlaneSet,
    ←Set.image_image g.val Hyperbolic.cayleyMobius.val Hyperbolic.openHalfPlaneSet,cayleyMobius_image_openHalfPlane,hg,hi]

/-- Every actual Mobius disc preserver restricts to a genuine native hyperbolic disc isometry and homeomorphism. -/
theorem nielsen_discPreserver_exists_nativeHomeomorph
    (g : Mobius.complexMobiusGroup)
    (hg : g.val '' Hyperbolic.extendedUnitDisc=Hyperbolic.extendedUnitDisc) :
    ∃φ : 𝔻 ≃ₜ 𝔻,(letI:=Hyperbolic.discHyperbolicMetric;Isometry φ) ∧
      ∀z : 𝔻,g.val (Hyperbolic.extendedDiscPoint z)=Hyperbolic.extendedDiscPoint (φ z) := by
  obtain ⟨A,hA⟩:=mobius_preserves_halfPlane_exists_SL (Hyperbolic.cayleyMobius⁻¹*g*Hyperbolic.cayleyMobius)
    (nielsen_discPreserver_conjugate_halfPlane g hg)
  refine ⟨Hyperbolic.discSL2Homeomorph A,?_,?_⟩
  · let :=Hyperbolic.discHyperbolicMetric
    exact Hyperbolic.cayley_isometry.comp ((isometry_smul ℍ A).comp Hyperbolic.inverse_cayley_isometry)
  · intro z
    have hq : Hyperbolic.cayleyMobius.val (Hyperbolic.extendedHalfPlanePoint (Hyperbolic.discToHalfPlane z))=Hyperbolic.extendedDiscPoint z:=by
      change Hyperbolic.extendedCayley (((Hyperbolic.discToHalfPlane z : ℍ) : ℂ) :
        Mobius.ExtendedComplex)=Hyperbolic.extendedDiscPoint z
      rw [Hyperbolic.extendedCayley_halfPlane,Hyperbolic.halfPlaneToDisc_discToHalfPlane]
      rfl
    have he:=congrArg (fun p : Mobius.ExtendedComplex=>Hyperbolic.cayleyMobius.val p) (Hyperbolic.realSLMobius_action A
      (Hyperbolic.discToHalfPlane z))
    rw [hA] at he
    change Hyperbolic.cayleyMobius.val (Hyperbolic.cayleyMobius⁻¹.val (g.val (Hyperbolic.cayleyMobius.val
      (Hyperbolic.extendedHalfPlanePoint (Hyperbolic.discToHalfPlane z)))))=
      Hyperbolic.cayleyMobius.val (Hyperbolic.extendedHalfPlanePoint (A • Hyperbolic.discToHalfPlane z)) at he
    change Hyperbolic.cayleyMobius • (Hyperbolic.cayleyMobius⁻¹ • (g • (Hyperbolic.cayleyMobius •
      Hyperbolic.extendedHalfPlanePoint (Hyperbolic.discToHalfPlane z))))=
      Hyperbolic.cayleyMobius • Hyperbolic.extendedHalfPlanePoint (A • Hyperbolic.discToHalfPlane z) at he
    rw [smul_inv_smul] at he
    change g.val (Hyperbolic.cayleyMobius.val (Hyperbolic.extendedHalfPlanePoint (Hyperbolic.discToHalfPlane z)))=
      Hyperbolic.cayleyMobius.val (Hyperbolic.extendedHalfPlanePoint (A • Hyperbolic.discToHalfPlane z)) at he
    rw [hq] at he
    exact he.trans (Hyperbolic.extendedCayley_halfPlane (A • Hyperbolic.discToHalfPlane z))


/-- Boundary-closure data alone imply the supporting-region inclusion. -/
theorem FuchsianDisc.nielsenSupportingRegion_minimal_from_sphericalClosure
    {H : Subgroup Mobius.complexMobiusGroup}
    (D : FuchsianDisc H)
    (hD : D.carrier=Hyperbolic.extendedUnitDisc)
    (hH : DiscreteGroups.IsNonElementary H)
    (S : Set 𝔻)
    (hopen : IsOpen S)
    (hne : S.Nonempty)
    (hconv : Hyperbolic.DiscHConvex S)
    (hcl : DiscreteGroups.mobiusLimitSet H⊆closure (Hyperbolic.extendedDiscPoint '' S)) : nielsenSupportingRegion H⊆S := by
  have hA : nielsenIdealLimitSet H⊆closure (Hyperbolic.kleinCoordinate '' S):=by
    intro p hp
    apply nielsen_klein_closure_ideal (D.nielsenIdealLimitSet_unitCircle hD p hp)
    have hpc:=hcl hp
    have himg : ((↑) : ℂ → Mobius.ExtendedComplex) '' (((↑) : 𝔻 → ℂ) '' S)=Hyperbolic.extendedDiscPoint '' S:=by
      rw [Set.image_image]
      rfl
    rw [←himg] at hpc
    change p∈((↑) : ℂ → Mobius.ExtendedComplex) ⁻¹' closure (((↑) : ℂ → Mobius.ExtendedComplex) '' (((↑) : 𝔻 → ℂ) ''
      S)) at hpc
    rw [Hyperbolic.onePoint_coe_preimage_closure_image] at hpc
    exact hpc
  have hKconv:=(Hyperbolic.discHConvex_iff_klein_convex S).mp hconv
  have hKopen : IsOpen (Hyperbolic.kleinCoordinate '' S):=Hyperbolic.isOpenEmbedding_kleinCoordinate.isOpenMap S hopen
  have hKI : (interior (Hyperbolic.kleinCoordinate '' S)).Nonempty:=hKopen.interior_eq.symm ▸ hne.image _
  have hHull : closedConvexHull ℝ (nielsenIdealLimitSet H)⊆closure (Hyperbolic.kleinCoordinate '' S):=
    closedConvexHull_min hA hKconv.closure isClosed_closure
  have hInt:=interior_mono hHull
  rw [hKconv.interior_closure_eq_interior_of_nonempty_interior hKI,hKopen.interior_eq] at hInt
  intro z hz
  rw [D.nielsenSupportingRegion_eq_klein_hull hD hH] at hz
  exact Hyperbolic.kleinCoordinate_injective.mem_set_image.mp (hInt hz)

/-- Genuine sphere actions and native isometries transport actual hull-boundary data. -/
theorem FuchsianDisc.nielsenSupportingRegion_subset_nativeImage
    {H : Subgroup Mobius.complexMobiusGroup}
    (D : FuchsianDisc H)
    (hD : D.carrier=Hyperbolic.extendedUnitDisc)
    (hH : DiscreteGroups.IsNonElementary H)
    (g : Mobius.complexMobiusGroup) (hL : g.val '' DiscreteGroups.mobiusLimitSet H=DiscreteGroups.mobiusLimitSet H)
    (φ : 𝔻 ≃ₜ 𝔻) (hφ : letI:=Hyperbolic.discHyperbolicMetric;Isometry φ)
    (hact : ∀z : 𝔻,g.val (Hyperbolic.extendedDiscPoint z)=Hyperbolic.extendedDiscPoint (φ z)) :
    nielsenSupportingRegion H⊆φ '' nielsenSupportingRegion H := by
  apply D.nielsenSupportingRegion_minimal_from_sphericalClosure hD hH _
    (φ.isOpenMap _ (D.nielsenSupportingRegion_isOpen hD hH))
    ((D.nielsenSupportingRegion_nonempty hD hH).image _)
    ((D.nielsenSupportingRegion_convex hD hH).isometry_image hφ)
  rw [←hL]
  rintro _ ⟨p,hp,rfl⟩
  have hh:=image_closure_subset_closure_image (Mobius.mobiusBoundaryHomeomorph g).continuous
    ⟨p,D.nielsenLimitSet_subset_supportingSphereClosure hD hH hp,rfl⟩
  have himg : g.val '' (Hyperbolic.extendedDiscPoint '' nielsenSupportingRegion H)=
      Hyperbolic.extendedDiscPoint '' (φ '' nielsenSupportingRegion H):=by
    rw [Set.image_image,Set.image_image]
    congr 1
    exact funext hact
  change g.val p∈closure (g.val '' (Hyperbolic.extendedDiscPoint '' nielsenSupportingRegion H)) at hh
  rw [himg] at hh
  exact hh

/-- The supporting region is preserved under each true group member's genuine native action. -/
theorem FuchsianDisc.nielsenSupportingRegion_nativeImage
    {H : Subgroup Mobius.complexMobiusGroup}
    (D : FuchsianDisc H)
    (hD : D.carrier=Hyperbolic.extendedUnitDisc)
    (hH : DiscreteGroups.IsNonElementary H)
    (g : H) (φ : 𝔻 ≃ₜ 𝔻) (hφ : letI:=Hyperbolic.discHyperbolicMetric;Isometry φ)
    (hact : ∀z : 𝔻,g.val.val (Hyperbolic.extendedDiscPoint z)=Hyperbolic.extendedDiscPoint (φ z)) :
    φ '' nielsenSupportingRegion H=nielsenSupportingRegion H := by
  have hsub:=D.nielsenSupportingRegion_subset_nativeImage hD hH g.val
    (DiscreteGroups.mobiusLimitSet_image H g) φ hφ hact
  have hInv : letI:=Hyperbolic.discHyperbolicMetric;Isometry φ.symm:=by
    let :=Hyperbolic.discHyperbolicMetric
    exact (⟨φ.toEquiv,hφ⟩ : 𝔻 ≃ᵢ 𝔻).symm.isometry
  have hInvAct (z : 𝔻) : g⁻¹.val.val (Hyperbolic.extendedDiscPoint z)=Hyperbolic.extendedDiscPoint (φ.symm z):=by
    apply g.val.val.injective
    change g • (g⁻¹ • Hyperbolic.extendedDiscPoint z)=g.val.val (Hyperbolic.extendedDiscPoint (φ.symm z))
    rw [smul_inv_smul,hact,φ.apply_symm_apply]
  have hsubInv:=D.nielsenSupportingRegion_subset_nativeImage hD hH g⁻¹.val
    (DiscreteGroups.mobiusLimitSet_image H g⁻¹) φ.symm hInv hInvAct
  apply subset_antisymm _ hsub
  rintro _ ⟨z,hz,rfl⟩
  obtain ⟨w,hw,he⟩:=hsubInv hz
  rw [←he,φ.apply_symm_apply]
  exact hw

/-- Invariance is proved for the actual original spherical group action. -/
theorem FuchsianDisc.nielsenSupportingRegion_invariant
    {H : Subgroup Mobius.complexMobiusGroup}
    (D : FuchsianDisc H)
    (hD : D.carrier=Hyperbolic.extendedUnitDisc)
    (hH : DiscreteGroups.IsNonElementary H) :
    ∀g : H,∀p∈Hyperbolic.extendedDiscPoint '' nielsenSupportingRegion H,
      g • p∈Hyperbolic.extendedDiscPoint '' nielsenSupportingRegion H := by
  intro g p hp
  have hg : g.val.val '' Hyperbolic.extendedUnitDisc=Hyperbolic.extendedUnitDisc:=hD ▸ D.image_eq g
  obtain ⟨φ,hφ,hact⟩:=nielsen_discPreserver_exists_nativeHomeomorph g.val hg
  obtain ⟨z,hz,rfl⟩:=hp
  change g.val.val (Hyperbolic.extendedDiscPoint z)∈Hyperbolic.extendedDiscPoint '' nielsenSupportingRegion H
  rw [hact]
  refine ⟨φ z,?_,rfl⟩
  rw [←D.nielsenSupportingRegion_nativeImage hD hH g φ hφ hact]
  exact mem_image_of_mem φ hz

end
end LowDimensionalTopology.Geometry.Fuchsian
