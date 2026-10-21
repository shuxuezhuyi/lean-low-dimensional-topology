module
public import LowDimensionalTopology.Geometry.Hyperbolic.Models.Disc.ExtendedCarrier
public import LowDimensionalTopology.Geometry.Fuchsian.Axis.SimpleAxisNormalizers
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.Side.ParabolicSidePairing
@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter MeasureTheory
open scoped OnePoint Pointwise UpperHalfPlane Topology
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
local instance hyperbolicSideSphereMeasurable : MeasurableSpace _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex := borel _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex
local instance hyperbolicSideSphereBorel : BorelSpace _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex := ⟨rfl⟩

/-- An actual small circular arc through the positive imaginary point, with no ideal point substituted for a native point. -/
def axisCircleProbe (r : ℝ) (hr : 0 < r) (t : Ioo (-1:ℝ) 1) : ℍ :=
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe (r*t.val) (r*Real.sqrt (1-t.val^2)) (by
    have ht : 0 < 1-t.val^2 := by nlinarith [t.property.1,t.property.2]
    exact mul_pos hr (Real.sqrt_pos.mpr ht))

theorem axisCircleProbe_continuous (r : ℝ) (hr : 0 < r) : Continuous (axisCircleProbe r hr) := by
  apply UpperHalfPlane.isEmbedding_coe.continuous_iff.mpr
  change Continuous (fun t : Ioo (-1:ℝ) 1 => (⟨r*t.val,r*Real.sqrt (1-t.val^2)⟩ : ℂ))
  simp_rw [Complex.mk_eq_add_mul_I]
  fun_prop

theorem axisCircleProbe_norm (r : ℝ) (hr : 0 < r) (t : Ioo (-1:ℝ) 1) :
    ‖(axisCircleProbe r hr t:ℂ)‖ = r := by
  apply (sq_eq_sq₀ (norm_nonneg _) hr.le).mp
  rw [←Complex.normSq_eq_norm_sq,Complex.normSq_apply]
  change (r*t.val)*(r*t.val)+(r*Real.sqrt (1-t.val^2))*(r*Real.sqrt (1-t.val^2)) = r^2
  simp only [←pow_two]
  rw [mul_pow,mul_pow,Real.sq_sqrt (by nlinarith [t.property.1,t.property.2] : 0 ≤ 1-t.val^2)]
  ring

theorem axisCircleProbe_zero (r : ℝ) (hr : 0 < r) :
    axisCircleProbe r hr ⟨0,by norm_num⟩ = _root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe 0 r hr := by
  apply UpperHalfPlane.ext
  apply Complex.ext <;> norm_num [axisCircleProbe,_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe]

/-- Every genuine open neighborhood of an imaginary point meets the same circle strictly on its right. -/
theorem exists_right_circle_point_mem_open (r : ℝ) (hr : 0 < r) (U : Set ℍ)
    (hU : IsOpen U) (hp : _root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe 0 r hr ∈ U) :
    ∃ q ∈ U, 0 < q.re ∧ ‖(q:ℂ)‖ = r := by
  let zero : Ioo (-1:ℝ) 1 := ⟨0,by norm_num⟩
  have hcl : closure {t : Ioo (-1:ℝ) 1 | 0 < t.val} = {t | 0 ≤ t.val} := by
    change closure (Subtype.val ⁻¹' Ioi (0:ℝ)) = Subtype.val ⁻¹' Ici (0:ℝ)
    rw [←(show IsOpen (Ioo (-1:ℝ) 1) from isOpen_Ioo).isOpenMap_subtype_val.preimage_closure_eq_closure_preimage
      continuous_subtype_val,closure_Ioi]
  have hz : zero ∈ closure {t : Ioo (-1:ℝ) 1 | 0 < t.val} := by rw [hcl];change (0:ℝ) ≤ 0;exact le_rfl
  have hzero : zero ∈ axisCircleProbe r hr ⁻¹' U := by
    change axisCircleProbe r hr ⟨0,by norm_num⟩ ∈ U
    rwa [axisCircleProbe_zero]
  have hpre : IsOpen (axisCircleProbe r hr ⁻¹' U) := hU.preimage (axisCircleProbe_continuous r hr)
  obtain ⟨t,htU,htpos⟩ := (mem_closure_iff_nhds.mp hz) _ (hpre.mem_nhds hzero)
  refine ⟨axisCircleProbe r hr t,htU,?_,axisCircleProbe_norm r hr t⟩
  change 0 < r*t.val
  exact mul_pos hr htpos

/-- The genuine nearest-axis region for a simple dilation is open, convex and contains its entire actual axis. -/
theorem HalfPlaneFuchsianGroup.simple_dilation_nearest_geometry {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : HalfPlaneFuchsianGroup H) (l : ℝ) (hl : 0 < l) (hs : IsSimple H
      (_root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation l)) :
    letI := P.nativeAction
    let S := _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.axisVoronoiRegion (G :=
      H) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical 0).carrier
    IsOpen S ∧ _root_.LowDimensionalTopology.Geometry.Hyperbolic.HConvex S ∧ (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical 0).carrier ⊆ S := by
  let nativeDilationNearestGeometryAction := P.nativeAction
  obtain ⟨A,hA⟩ := mobius_preserves_halfPlane_exists_SL (_root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation l) (P.preserves ⟨_,hs.1⟩)
  have hh : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A) := by rw [hA];exact _root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation_hyperbolic l hl
  have hf : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A ≠ 1 := hh.1.1
  have ht : 4 < (Matrix.trace A.val)^2 := (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_hyperbolic_iff
    A hf).mp hh
  have hsA : IsSimple H (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A) := by rw [hA];exact hs
  have hL := dilation_hyperbolic_axis_eq_vertical A hf ht l hA
  refine ⟨?_,?_,?_⟩
  · simpa only [hL] using P.hyperbolic_axisVoronoi_isOpen A hsA.1 hf ht
  · simpa only [hL] using P.simple_axisVoronoi_hConvex A hf ht hsA
  · simpa only [hL] using P.simple_axis_subset_Voronoi A hf ht hsA

/-- The original dilation preserves the actual nearest-axis region through the full set stabilizer. -/
theorem HalfPlaneFuchsianGroup.dilation_nearest_invariant {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : HalfPlaneFuchsianGroup H) (l : ℝ) (hfH : _root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation l ∈
      H) :
    letI := P.nativeAction
    (⟨_root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation l,hfH⟩ :
      H) • _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.axisVoronoiRegion (G :=
      H) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical 0).carrier =
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.axisVoronoiRegion (G := H) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical 0).carrier := by
  let nativeDilationNearestInvariantAction := P.nativeAction
  let nativeDilationNearestInvariantMetric : IsIsometricSMul H ℍ := ⟨fun g => (P.nativeHom g).isometry⟩
  let g : H := ⟨_root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation l,hfH⟩
  have hgK : g ∈ nativeAxisStabilizer H := ⟨hfH,stableAxisDilation_image_axis l⟩
  rw [P.nativeAxisStabilizer_eq] at hgK
  exact (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.axisVoronoiRegion_coset_stable (G := H)
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical 0).carrier).invariant ⟨g,hgK⟩

/-- Every actual right circular boundary point in the nearest region belongs to both true closed intersection tiles. -/
theorem HalfPlaneFuchsianGroup.dilation_circle_closed_tile_intersection
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P : HalfPlaneFuchsianGroup H)
    (l : ℝ) (hl : 0 < l) (hfH : _root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation l ∈ H) (D : Set ℍ)
    (hcases : D = dilationAxisAnnulus l ∨ D = dihedralAxisRightAnnulus l)
    (hcl : letI := P.nativeAction
      closure (D ∩ _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.axisVoronoiRegion (G := H)
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical 0).carrier) =
        closure D ∩ closure (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.axisVoronoiRegion (G := H)
          (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical 0).carrier))
    (z : ℍ) (hz : letI := P.nativeAction
      z ∈ _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.axisVoronoiRegion (G :=
        H) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical 0).carrier)
    (hnorm : ‖(z:ℂ)‖ = Real.exp l) (hre : 0 ≤ z.re) :
    letI := P.nativeAction
    z ∈ closure (D ∩ _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.axisVoronoiRegion (G := H)
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical 0).carrier) ∩
      ((⟨_root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation l,hfH⟩ : H) • closure (D ∩ _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.axisVoronoiRegion (G := H) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical 0).carrier)) := by
  let nativeDilationCircleIntersectionAction := P.nativeAction
  let g : H := ⟨_root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation l,hfH⟩
  let S := _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.axisVoronoiRegion (G :=
    H) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical 0).carrier
  have hel : 1 ≤ Real.exp l := (Real.one_lt_exp_iff.mpr hl).le
  have hInv : g⁻¹.val = _root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation l^(-1:ℤ) := by simp [g]
  have hbacknorm : ‖((g⁻¹ • z : ℍ):ℂ)‖ = 1 := by
    rw [P.dilation_element_coe l g⁻¹ (-1) hInv z,norm_mul,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _),hnorm]
    norm_num only [Int.cast_neg,Int.cast_one,neg_one_mul]
    rw [Real.exp_neg,inv_mul_cancel₀ (Real.exp_ne_zero l)]
  have hbackre : 0 ≤ (g⁻¹ • z).re := by
    rw [P.dilation_element_re l g⁻¹ (-1) hInv]
    exact mul_nonneg (Real.exp_pos _).le hre
  have hbackS : g⁻¹ • z ∈ S := by
    have hh : g • S = S := P.dilation_nearest_invariant l hfH
    change z ∈ S at hz
    rw [←hh] at hz
    obtain ⟨w,hw,he⟩ := hz
    rw [←he,inv_smul_smul]
    exact hw
  have hDC (w : ℍ) (hw : 1 ≤ ‖(w:ℂ)‖ ∧ ‖(w:ℂ)‖ ≤ Real.exp l ∧ 0 ≤ w.re) :
      w ∈ closure D := by
    rcases hcases with rfl | rfl
    · rw [closure_dilationAxisAnnulus l hl]
      exact ⟨hw.1,hw.2.1⟩
    · rw [closure_dihedralAxisRightAnnulus l hl]
      exact hw
  refine ⟨?_,?_⟩
  · rw [hcl]
    exact ⟨hDC z ⟨hnorm ▸ hel,hnorm.le,hre⟩,subset_closure hz⟩
  · refine ⟨g⁻¹ • z,?_,smul_inv_smul g z⟩
    rw [hcl]
    exact ⟨hDC _ ⟨hbacknorm ▸ le_rfl,hbacknorm.symm ▸ hel,hbackre⟩,subset_closure hbackS⟩

/-- Every prescribed primitive simple positive dilation genuinely pairs a side of the constructed original whole-group polygon. -/
theorem primitive_simple_dilation_side_pairing {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : HalfPlaneFuchsianGroup H) (l : ℝ) (hl : 0 < l)
    (hp : IsPrimitive H (_root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation l)) (hs : IsSimple H
      (_root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation l)) :
    ∃ D : Set P.cayleyData.domain.carrier, ∃ hD : IsConvexFuchsianPolygon P.cayleyData D,
      ∃ s : FuchsianPolygonSides P.cayleyData D,
        (fuchsianSideElement hD s).val = _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius*_root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation l*_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius⁻¹ := by
  let nativePrimitiveDilationSideAction := P.nativeAction
  let S := _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.axisVoronoiRegion (G :=
    H) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical 0).carrier
  obtain ⟨E,hcases,hPoly⟩ := P.primitive_simple_dilation_intersection_polygon l hl hp hs
  have hGeom := P.simple_dilation_nearest_geometry l hl hs
  have hSo : IsOpen S := hGeom.1
  have hSc : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HConvex S := hGeom.2.1
  have haxis : (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical 0).carrier ⊆ S := hGeom.2.2
  have hEc : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HConvex E := by
    rcases hcases with rfl | rfl
    · exact dilationAxisAnnulus_hConvex l
    · exact dihedralAxisRightAnnulus_hConvex l
  have hEo : IsOpen E := by
    rcases hcases with rfl | rfl
    · exact dilationAxisAnnulus_isOpen l
    · exact dihedralAxisRightAnnulus_isOpen l
  have hne : (E ∩ S).Nonempty := by
    obtain ⟨x,z,hz,_hzx⟩ := hPoly.locallyFinite.fundamental.isConnected.nonempty
    exact ⟨z,hz⟩
  have hcl : closure (E ∩ S) = closure E ∩ closure S := hConvex_open_closure_inter hEc hSc hEo hSo hne
  let p := _root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe 0 (Real.exp l) (Real.exp_pos l)
  have hpS : p ∈ S := haxis (by change (0:ℝ)=0;exact rfl)
  obtain ⟨q,hqS,hqr,hqn⟩ := exists_right_circle_point_mem_open (Real.exp l) (Real.exp_pos l) S hSo hpS
  have hpn : ‖(p:ℂ)‖ = Real.exp l := by
    change ‖(_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe 0 (Real.exp l) (Real.exp_pos
      l):ℂ)‖ = Real.exp l
    rw [←axisCircleProbe_zero (Real.exp l) (Real.exp_pos l)]
    exact axisCircleProbe_norm _ _ _
  let g : H := ⟨_root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation l,hp.mem⟩
  have hn : (closure (E ∩ S) ∩ (g • closure (E ∩ S))).Nontrivial := by
    refine ⟨p,P.dilation_circle_closed_tile_intersection l hl hp.mem E hcases hcl p hpS hpn le_rfl,
      q,P.dilation_circle_closed_tile_intersection l hl hp.mem E hcases hcl q hqS hqn hqr.le,?_⟩
    intro he
    have hre := congrArg UpperHalfPlane.re he
    change 0 = q.re at hre
    exact hqr.ne' hre.symm
  let e := _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugateEquivalence _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius H
  have hg : g ≠ 1 := by
    intro he
    exact hp.ne_one (congrArg Subtype.val he)
  have heg : e g ≠ 1 := by
    intro he
    exact hg (e.injective (he.trans (map_one e).symm))
  have hn' := P.cayley_intersection_nontrivial (E ∩ S) g hn
  let side : FuchsianPolygonSides P.cayleyData (P.cayleyCoordinate '' (E ∩ S)) :=
    ⟨_,hPoly.side_of_nontrivial_intersection heg hn'⟩
  have hside : fuchsianSideElement hPoly side = e g :=
    ((hPoly.existsUnique_side_element side.property).choose_spec.2 (e g) ⟨heg,rfl⟩).symm
  exact ⟨_,hPoly,side,congrArg (fun a => a.val) hside⟩

/-- Both travel directions of a primitive simple dilation genuinely occur as original side-pairing elements. -/
theorem primitive_signed_dilation_side_pairing {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : HalfPlaneFuchsianGroup H) (l : ℝ) (hl : l ≠ 0)
    (hp : IsPrimitive H (_root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation l)) (hs : IsSimple H
      (_root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation l)) :
    ∃ D : Set P.cayleyData.domain.carrier, ∃ hD : IsConvexFuchsianPolygon P.cayleyData D,
      ∃ s : FuchsianPolygonSides P.cayleyData D,
        (fuchsianSideElement hD s).val = _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius*_root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation l*_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius⁻¹ := by
  rcases lt_or_gt_of_ne hl with hneg | hpos
  · have hpinv : IsPrimitive H (_root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation (-l)) := by
      apply (primitive_iff_of_hyperbolic (_root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation_hyperbolic
        (-l) (neg_pos.mpr hneg))).mpr
      rw [_root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation_neg]
      refine ⟨H.inv_mem hp.mem,?_⟩
      intro z hz
      have hfix : (_root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation l).val z = z := by
        simpa only [inv_inv] using _root_.LowDimensionalTopology.Geometry.Mobius.mobius_inv_fixed hz
      simpa only [Subgroup.zpowers_inv] using hp.generates z hfix
    have hsinv : IsSimple H (_root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation (-l)) := by
      refine ⟨hpinv.mem,_root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation_hyperbolic (-l) (neg_pos.mpr
        hneg),?_⟩
      intro g hg
      rw [stableAxisDilation_geodesicAxis (-l) (neg_pos.mpr hneg),
        ←stableAxisDilation_geodesicAxis_of_ne_zero l hl]
      exact hs.2.2 g hg
    obtain ⟨D,hD,s,hsI⟩ := primitive_simple_dilation_side_pairing P (-l) (neg_pos.mpr hneg) hpinv hsinv
    refine ⟨D,hD,fuchsianPairedSide hD s,?_⟩
    rw [fuchsianSideElement_paired]
    change (fuchsianSideElement hD s).val⁻¹ = _
    rw [hsI,_root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation_neg]
    group
  · exact primitive_simple_dilation_side_pairing P l hpos hp hs

/-- Sufficiency: every actual original primitive simple hyperbolic element pairs sides of a genuine convex fundamental polygon. -/
theorem primitive_simple_hyperbolic_side_pairing {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup G) (f : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hp : IsPrimitive G f) (hs : IsSimple G f) :
    ∃ D : Set P.domain.carrier, ∃ hD : IsConvexFuchsianPolygon P D,
      ∃ s : FuchsianPolygonSides P D, (fuchsianSideElement hD s).val = f := by
  obtain ⟨q,hq,l,hl,he⟩ := P.hyperbolic_halfPlane_normalizer f hs.2.1 hs.1
  let K := _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q G
  let N := P.normalizedHalfPlaneData q hq
  let Q := N.cayleyData
  have hpk : IsPrimitive K (_root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation l) := by
    rw [←he]
    exact (isPrimitive_conjugation_iff G f q).mpr hp
  have hsk : IsSimple K (_root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation l) := by
    rw [←he]
    exact (_root_.LowDimensionalTopology.Geometry.Hyperbolic.isSimple_conjugation G f q).mpr hs
  obtain ⟨D,hD,s,hsD⟩ := primitive_signed_dilation_side_pairing N l hl hpk hsk
  let r := _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius*q
  have hr : r.val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc = _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc := by
    change (fun z => _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius.val (q.val
      z)) '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc = _
    rw [←image_image,hq,cayleyMobius_image_openHalfPlane]
  let e : G ≃* _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius K :=
    MulEquiv.trans (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugateEquivalence q
      G)
      (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugateEquivalence
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius K)
  let F : P.domain.carrier ≃ₜ Q.domain.carrier := P.conjugateCoordinate r hr
  have hEquiv (g : G) (x : P.domain.carrier) : F (g • x) = e g • F x := by
    apply Subtype.ext
    change _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius.val (q.val (g.val.val x.val)) =
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius.val (q.val (g.val.val (q.val.symm
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius.val.symm
          (_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius.val (q.val x.val))))))
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius.val.symm_apply_apply,q.val.symm_apply_apply]
  have harea : Measure.map F P.area = Q.area := P.conjugateCoordinate_area_map r hr
  have hiso : letI := _root_.LowDimensionalTopology.Geometry.Hyperbolic.discHyperbolicMetric
      Isometry (fun z : Complex.UnitDisc => Q.finiteCoordinate (F (P.finiteCoordinate.symm z))) :=
    P.conjugateCoordinate_isometry r hr
  obtain ⟨hP,t,ht⟩ := equivariant_fuchsian_side_element_preimage P Q e F hEquiv harea hiso hD s
  have hse : fuchsianSideElement hD s = e ⟨f,hp.mem⟩ := by
    apply Subtype.ext
    change (fuchsianSideElement hD s).val = _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius*(q*f*q⁻¹)*_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius⁻¹
    rw [he]
    exact hsD
  rw [hse,e.symm_apply_apply] at ht
  exact ⟨_,hP,t,congrArg (fun a : G => a.val) ht⟩

end LowDimensionalTopology.Geometry.Fuchsian
