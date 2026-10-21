module
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.ConvexFundamentalPolygons
public import LowDimensionalTopology.Geometry.Polygon.Angle.PolygonStraightAngles
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped Topology OnePoint Complex.UnitDisc
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
  LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Polygon

/-- The actual ideal boundary is the Euclidean closure of the genuine polygon,
restricted to the unit circle. -/
def fuchsianPolygonIdealBoundary {H : Subgroup Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (D : Set P.domain.carrier) : Set ℂ :=
  closure ((fun x => (P.finiteCoordinate x : ℂ)) '' D) ∩ Metric.sphere 0 1

theorem mem_fuchsianPolygonIdealBoundary {H : Subgroup Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (D : Set P.domain.carrier) (ξ : ℂ) :
    ξ ∈ fuchsianPolygonIdealBoundary P D ↔
      ξ ∈ closure ((fun x => (P.finiteCoordinate x : ℂ)) '' D) ∧ ‖ξ‖ = 1 := by
  simp only [fuchsianPolygonIdealBoundary, mem_inter_iff, Metric.mem_sphere, dist_zero_right]

theorem fuchsianPolygonIdealBoundary_isCompact
    {H : Subgroup Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (D : Set P.domain.carrier) :
    IsCompact (fuchsianPolygonIdealBoundary P D) :=
  (isCompact_sphere 0 1).inter_left isClosed_closure

/-- A true ideal Euclidean accumulation point remains an accumulation point in Klein coordinates. -/
theorem disc_ideal_closure_klein {S : Set 𝔻} (ξ : ℂ) (hξ : ‖ξ‖ = 1)
    (hcl : ξ ∈ closure ((fun z : 𝔻 => (z : ℂ)) '' S)) :
    ξ ∈ closure (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate '' S) := by
  have hext : (ξ : OnePoint ℂ) ∈ closure (_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedDiscPoint '' S) := by
    have h := mem_closure_image
      (OnePoint.continuous_coe : Continuous (OnePoint.some : ℂ → OnePoint ℂ)).continuousAt hcl
    simpa only [image_image, Function.comp_def,
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedDiscPoint] using h
  change (ξ : OnePoint ℂ) ∈ closure ((fun z : 𝔻 => ((z : ℂ) : OnePoint ℂ)) '' S) at hext
  rw [← _root_.LowDimensionalTopology.Geometry.Hyperbolic.discClosedModelClosure_ambient] at hext
  obtain ⟨p, hp, he⟩ := hext
  let q := Complex.UnitClosedDisc.mk ξ hξ.le
  have hpq : p = q := _root_.LowDimensionalTopology.Geometry.Hyperbolic.isEmbedding_closedDiscToExtended.injective he
  have hqK : _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate q = ξ :=
    congrArg (fun z : 𝕔𝔻 => (z : ℂ)) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedPoincareToKlein_ideal_fixed q hξ)
  rw [← _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKlein_image_discClosedModelClosure]
  exact ⟨p, hp, by rw [hpq, hqK]⟩

/-- Every genuine ending half-ray from an interior point stays in an open geodesically
convex disc set; the ideal endpoint is an actual Euclidean accumulation point. -/
theorem open_discHConvex_ideal_ray_subset
    {S : Set 𝔻}
    (ho : IsOpen S)
    (hc : _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscHConvex S)
    {z : 𝔻} (hz : z ∈ S) (R : _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscRayAt z) (ξ : ℂ) (hξ : ‖ξ‖ = 1)
    (hEnd : R.idealEndpoint = (ξ : OnePoint ℂ))
    (hcl : ξ ∈ closure ((fun w : 𝔻 => (w : ℂ)) '' S)) : R.val ⊆ S := by
  have hcK := (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discHConvex_iff_klein_convex S).mp hc
  have hoK := _root_.LowDimensionalTopology.Geometry.Hyperbolic.isOpenEmbedding_kleinCoordinate.isOpenMap S ho
  have hzK : _root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate z ∈ interior (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate '' S) := by
    rw [hoK.interior_eq]
    exact mem_image_of_mem _ hz
  have hξK := disc_ideal_closure_klein ξ hξ hcl
  let p := Complex.UnitClosedDisc.mk ξ hξ.le
  have hp : ‖(p : ℂ)‖ = 1 := hξ
  have hRay : _root_.LowDimensionalTopology.Geometry.Hyperbolic.IsDiscHLineRay z (ξ : OnePoint ℂ) R.val := by
    simpa only [hEnd] using R.isRay
  have hR : _root_.LowDimensionalTopology.Geometry.Hyperbolic.discClosedModelClosure R.val = _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelDiscHSegment (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z) p := by
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.discClosedModelClosure,
      ← _root_.LowDimensionalTopology.Geometry.Hyperbolic.discHRay_eq_of_isDiscHLineRay hRay]
    exact (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelDiscHSegment_ray z p hp).symm
  have hpK : _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate p = ξ :=
    congrArg (fun q : 𝕔𝔻 => (q : ℂ)) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedPoincareToKlein_ideal_fixed p hp)
  intro x hx
  have hxseg : _root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate x ∈ segment ℝ (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate z) ξ := by
    have him := _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKlein_image_closedModelDiscHSegment (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z) p
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate_disc_inclusion, hpK] at him
    rw [← him]
    exact ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel x, hR ▸ subset_closure (mem_image_of_mem _ hx), rfl⟩
  rw [segment_eq_image'] at hxseg
  obtain ⟨t, ht, he⟩ := hxseg
  by_cases ht0 : t = 0
  · have hxz : x = z := _root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate_injective (by simpa only [ht0, zero_smul, add_zero] using he.symm)
    exact hxz ▸ hz
  have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
  have ht1 : t < 1 := lt_of_le_of_ne ht.2 (by
    intro ht1
    have he' : _root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate x = ξ := by simpa only [ht1, one_smul, add_sub_cancel] using he.symm
    have hn := (_root_.LowDimensionalTopology.Geometry.Hyperbolic.poincareToKlein x).norm_lt_one
    change ‖_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate x‖ < 1 at hn
    rw [he', hξ] at hn
    exact lt_irrefl _ hn)
  have hxopen : _root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate x ∈ openSegment ℝ (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate z) ξ := by
    rw [openSegment_eq_image']
    exact ⟨t, ⟨htpos, ht1⟩, he⟩
  have hxK := hcK.openSegment_interior_closure_subset_interior hzK hξK hxopen
  rw [hoK.interior_eq] at hxK
  obtain ⟨y, hy, he⟩ := hxK
  exact _root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate_injective he ▸ hy

theorem IsConvexFuchsianPolygon.ideal_ray_subset
    {H : Subgroup Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} {D : Set P.domain.carrier} (hD : IsConvexFuchsianPolygon P D)
    (z : P.domain.carrier)
    (hz : z ∈ D)
    (R : _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscRayAt (P.finiteCoordinate z))
    (ξ : ℂ)
    (hξ : ξ ∈ fuchsianPolygonIdealBoundary P D) (hEnd : R.idealEndpoint = (ξ : OnePoint ℂ)) :
    R.val ⊆ P.finiteCoordinate '' D := by
  obtain ⟨hcl, hnorm⟩ := (mem_fuchsianPolygonIdealBoundary P D ξ).mp hξ
  have ho := ((isFuchsianFundamentalDomain_iff P D).mp hD.locallyFinite.fundamental).1
  apply open_discHConvex_ideal_ray_subset (P.finiteCoordinate.isOpenMap D ho) hD.convex
    (mem_image_of_mem _ hz) R ξ hnorm hEnd
  simpa only [image_image, Function.comp_def] using hcl

theorem IsConvexFuchsianPolygon.ideal_canonical_ray_subset
    {H : Subgroup Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} {D : Set P.domain.carrier} (hD : IsConvexFuchsianPolygon P D)
    (z : P.domain.carrier) (hz : z ∈ D) (ξ : ℂ)
    (hξ : ξ ∈ fuchsianPolygonIdealBoundary P D) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.discHRay (P.finiteCoordinate z) (ξ : OnePoint ℂ) ⊆ P.finiteCoordinate '' D := by
  have hnorm := ((mem_fuchsianPolygonIdealBoundary P D ξ).mp hξ).2
  have hb := (_root_.LowDimensionalTopology.Geometry.Hyperbolic.coe_mem_extendedDiscIdealBoundary ξ).mpr hnorm
  let R : _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscRayAt (P.finiteCoordinate z) := ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.discHRay _ (ξ : OnePoint ℂ), ξ, hb,
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.isDiscHLineRay_discHRay _ _ hb⟩
  have he : R.idealEndpoint = (ξ : OnePoint ℂ) := by
    obtain ⟨_, _, _, _, _, ht⟩ := R.isRay
    exact singleton_injective (ht.symm.trans (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discHRay_idealEndpoints _ _ hb))
  exact hD.ideal_ray_subset z hz R ξ hξ he

theorem UnitDiscFuchsianGroup.finiteCoordinate_extended
    {H : Subgroup Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (x : P.domain.carrier) :
    (((P.finiteCoordinate x : 𝔻) : ℂ) : OnePoint ℂ) = x.val := by
  have h := _root_.LowDimensionalTopology.Geometry.Surfaces.discFiniteHomeomorph_symm_coe (P.finiteCoordinate x)
  change (P.finiteCoordinate.symm (P.finiteCoordinate x)).val = _ at h
  rw [P.finiteCoordinate.symm_apply_apply] at h
  exact h.symm

theorem fuchsianPolygon_finite_image_extended
    {H : Subgroup Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (D : Set P.domain.carrier) :
    OnePoint.some '' ((fun x => (P.finiteCoordinate x : ℂ)) '' D) =
      (Subtype.val : P.domain.carrier → OnePoint ℂ) '' D := by
  rw [image_image]
  congr 1
  funext x
  exact P.finiteCoordinate_extended x

theorem mem_fuchsianPolygonIdealBoundary_iff_extendedClosure
    {H : Subgroup Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (D : Set P.domain.carrier) (ξ : ℂ) :
    ξ ∈ fuchsianPolygonIdealBoundary P D ↔ ‖ξ‖ = 1 ∧
      (ξ : OnePoint ℂ) ∈ closure ((Subtype.val : P.domain.carrier → OnePoint ℂ) '' D) := by
  rw [mem_fuchsianPolygonIdealBoundary]
  have h := OnePoint.isOpenEmbedding_coe.isEmbedding.closure_eq_preimage_closure_image
    ((fun x => (P.finiteCoordinate x : ℂ)) '' D)
  rw [h, fuchsianPolygon_finite_image_extended P D]
  exact and_comm

theorem IsConvexFuchsianPolygon.ideal_extended_ray_subset
    {H : Subgroup Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} {D : Set P.domain.carrier} (hD : IsConvexFuchsianPolygon P D)
    (z : P.domain.carrier)
    (hz : z ∈ D)
    (R : _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscRayAt (P.finiteCoordinate z))
    (ξ : ℂ)
    (hξ : ‖ξ‖ = 1) (hEnd : R.idealEndpoint = (ξ : OnePoint ℂ))
    (hcl : (ξ : OnePoint ℂ) ∈ closure ((Subtype.val : P.domain.carrier → OnePoint ℂ) '' D)) :
    R.val ⊆ P.finiteCoordinate '' D :=
  hD.ideal_ray_subset z hz R ξ
    ((mem_fuchsianPolygonIdealBoundary_iff_extendedClosure P D ξ).mpr ⟨hξ, hcl⟩) hEnd

end LowDimensionalTopology.Geometry.Fuchsian
