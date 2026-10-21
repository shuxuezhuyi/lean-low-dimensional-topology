module
public import LowDimensionalTopology.Geometry.Mobius.Circle.GeometricDisc
public import LowDimensionalTopology.Geometry.Hyperbolic.Models.Disc.ExtendedCarrier
public import LowDimensionalTopology.Geometry.Fuchsian.Nielsen.NielsenCoreArea
public import LowDimensionalTopology.Geometry.Fuchsian.Dirichlet.FinitelySidedDirichlet
public import LowDimensionalTopology.Geometry.DiscreteGroups.Packing.ElementaryPacking
public import Mathlib.Analysis.Convex.Strict.Extreme
public import LowDimensionalTopology.Geometry.Hyperbolic.Area.TriangleAreaIntegrals
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Set Filter Topology MeasureTheory
open scoped OnePoint Complex.UnitDisc RealInnerProductSpace UpperHalfPlane
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
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
local instance nielsenCoreSphereMeasurableSpace : MeasurableSpace Mobius.ExtendedComplex := borel Mobius.ExtendedComplex
local instance nielsenCoreSphereBorelSpace : BorelSpace Mobius.ExtendedComplex := ⟨rfl⟩

/-- A compact subset of the unit circle acquires no new unit-circle points
when its genuine closed Euclidean convex hull is taken. -/
theorem compact_unitCircle_closedConvexHull_contact
    {A : Set ℂ} (hA : IsCompact A) (hAs : ∀ z ∈ A, ‖z‖=1) :
    closedConvexHull ℝ A ∩ Metric.sphere (0:ℂ) 1 ⊆ A := by
  rintro ξ ⟨hξH,hξs⟩
  have hξN : ‖ξ‖=1 := mem_sphere_zero_iff_norm.mp hξs
  by_contra hξA
  by_cases hne : A.Nonempty
  · obtain ⟨p,hp,hmax⟩ := hA.exists_isMaxOn hne
      ((continuous_id.inner continuous_const).continuousOn : ContinuousOn (fun z : ℂ => inner ℝ z ξ) A)
    have hpξ : p≠ξ := fun he => hξA (he ▸ hp)
    have hd : 0<‖p-ξ‖^2 := sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hpξ))
    have hs := norm_sub_sq_real p ξ
    rw [hAs p hp,hξN] at hs
    have hb : inner ℝ p ξ < 1 := by nlinarith
    have hlin : IsLinearMap ℝ (fun z : ℂ => inner ℝ z ξ) :=
      ⟨fun x y => inner_add_left x y ξ,fun t x => by simp only [real_inner_smul_left,smul_eq_mul]⟩
    have hHull : closedConvexHull ℝ A ⊆ {z : ℂ | inner ℝ z ξ ≤ inner ℝ p ξ} :=
      closedConvexHull_min (fun z hz => hmax hz) (convex_halfSpace_le hlin _)
        (isClosed_le (continuous_id.inner continuous_const) continuous_const)
    have hh := hHull hξH
    change inner ℝ ξ ξ ≤ inner ℝ p ξ at hh
    rw [real_inner_self_eq_norm_sq,hξN] at hh
    norm_num only [one_pow] at hh
    linarith
  · have he : A=∅ := Set.not_nonempty_iff_eq_empty.mp hne
    rw [he] at hξH
    exact (closedConvexHull_min (Set.Subset.refl (∅:Set ℂ)) convex_empty isClosed_empty) hξH

/-- The actual Klein closure of the supporting-geodesic Nielsen region has
no ideal points outside the true original spherical limit set. -/
theorem nielsenSupportingRegion_klein_closure_contact
    {H : Subgroup Mobius.complexMobiusGroup}
    (D : FuchsianDisc H)
    (hD : D.carrier=Hyperbolic.extendedUnitDisc)
    (hNE : DiscreteGroups.IsNonElementary H) :
    closure (Hyperbolic.kleinCoordinate '' nielsenSupportingRegion H) ∩ Metric.sphere (0:ℂ) 1 ⊆
      nielsenIdealLimitSet H := by
  have hHull : Hyperbolic.kleinCoordinate '' nielsenSupportingRegion H ⊆
      closedConvexHull ℝ (nielsenIdealLimitSet H) := by
    rintro _ ⟨z,hz,rfl⟩
    rw [D.nielsenSupportingRegion_eq_klein_hull hD hNE] at hz
    exact interior_subset hz
  exact fun ξ hξ => compact_unitCircle_closedConvexHull_contact
    (D.nielsenIdealLimitSet_isCompact hD)
    (D.nielsenIdealLimitSet_unitCircle hD)
    ⟨closure_minimal hHull isClosed_closedConvexHull hξ.1,hξ.2⟩

/-- The actual supporting-region sphere closure meets the original ideal
boundary only in the true original spherical limit set. -/
theorem nielsenSupportingRegion_sphere_closure_contact
    {H : Subgroup Mobius.complexMobiusGroup}
    (D : FuchsianDisc H)
    (hD : D.carrier=Hyperbolic.extendedUnitDisc)
    (hNE : DiscreteGroups.IsNonElementary H) :
    closure (Hyperbolic.extendedDiscPoint '' nielsenSupportingRegion H) ∩ Hyperbolic.extendedDiscIdealBoundary ⊆
      DiscreteGroups.mobiusLimitSet H := by
  rintro _ ⟨hcl,ξ,hξ,rfl⟩
  have himage : ((↑):ℂ→Mobius.ExtendedComplex) '' (((↑):𝔻→ℂ) '' nielsenSupportingRegion H)=
      Hyperbolic.extendedDiscPoint '' nielsenSupportingRegion H := by rw [Set.image_image]; rfl
  have hξcl : ξ∈closure (((↑):𝔻→ℂ) '' nielsenSupportingRegion H) := by
    change ξ∈((↑):ℂ→Mobius.ExtendedComplex) ⁻¹' closure (Hyperbolic.extendedDiscPoint '' nielsenSupportingRegion
      H) at hcl
    rw [←himage,Hyperbolic.onePoint_coe_preimage_closure_image] at hcl
    exact hcl
  exact nielsenSupportingRegion_klein_closure_contact D hD hNE
    ⟨nielsen_klein_closure_ideal (mem_sphere_zero_iff_norm.mp hξ) hξcl,hξ⟩

/-- The original source-defined Nielsen region has no ordinary ideal closure
points. Both the whole original group and the original geometric disc are
retained; its supporting-hull chart is derived from the proved arc normalizer. -/
theorem nielsenRegion_closure_frontier_subset_limit
    {H : Subgroup Mobius.complexMobiusGroup}
    (D : FuchsianDisc H)
    (hNE : DiscreteGroups.IsNonElementary H) :
    closure (D.nielsenRegion hNE) ∩ frontier D.carrier ⊆ DiscreteGroups.mobiusLimitSet H := by
  let q := D.nielsenArcNormalizer hNE
  let E := D.nielsenConjugate q
  let F := E.nielsenConjugate Hyperbolic.cayleyMobius
  have hq : q.val '' D.carrier=Hyperbolic.openHalfPlaneSet := D.nielsenArcNormalizer_image hNE
  have hE : E.carrier=Hyperbolic.openHalfPlaneSet := hq
  have hF : F.carrier=Hyperbolic.extendedUnitDisc := by
    change Hyperbolic.cayleyMobius.val '' E.carrier=Hyperbolic.extendedUnitDisc
    rw [hE,cayleyMobius_image_openHalfPlane]
  have hNEq : DiscreteGroups.IsNonElementary (DiscreteGroups.Action.Actions.subgroupConjugate q H) := hNE.conjugation q
  have hinf : (∞:Mobius.ExtendedComplex)∈DiscreteGroups.mobiusLimitSet (DiscreteGroups.Action.Actions.subgroupConjugate
    q H) :=
    D.nielsenArcNormalizer_limit hNE
  have hqN : q.val '' D.nielsenRegion hNE =
      Hyperbolic.extendedHalfPlanePoint '' Hyperbolic.nielsenHalfPlaneArcRegion (DiscreteGroups.mobiusLimitSet (DiscreteGroups.Action.Actions.subgroupConjugate q H)) := by
    change q.val '' (q.val.symm '' _) = _
    exact q.val.image_symm_image _
  let u := Hyperbolic.cayleyMobius*q
  have huD : u.val '' D.carrier=Hyperbolic.extendedUnitDisc := by
    rw [nielsen_mobius_image_mul,hq,cayleyMobius_image_openHalfPlane]
  have huN : u.val '' D.nielsenRegion hNE = Hyperbolic.extendedDiscPoint ''
      nielsenSupportingRegion (DiscreteGroups.Action.Actions.subgroupConjugate Hyperbolic.cayleyMobius (DiscreteGroups.Action.Actions.subgroupConjugate q H)) := by
    rw [nielsen_mobius_image_mul,hqN]
    exact E.nielsenHalfPlaneArcRegion_cayley_image hE hNEq hinf
  rintro ξ ⟨hξcl,hξB⟩
  have huc : u.val ξ ∈ closure (u.val '' D.nielsenRegion hNE) := by
    change (Mobius.mobiusBoundaryHomeomorph u) ξ ∈ closure ((Mobius.mobiusBoundaryHomeomorph u) '' D.nielsenRegion hNE)
    rw [←(Mobius.mobiusBoundaryHomeomorph u).image_closure]
    exact ⟨ξ,hξcl,rfl⟩
  have hub : u.val ξ ∈ Hyperbolic.extendedDiscIdealBoundary := by
    rw [←nielsen_unitDisc_frontier,←huD]
    change (Mobius.mobiusBoundaryHomeomorph u) ξ ∈ frontier ((Mobius.mobiusBoundaryHomeomorph u) '' D.carrier)
    rw [←(Mobius.mobiusBoundaryHomeomorph u).image_frontier]
    exact ⟨ξ,hξB,rfl⟩
  rw [huN] at huc
  have hL := nielsenSupportingRegion_sphere_closure_contact F hF (hNEq.conjugation Hyperbolic.cayleyMobius)
    ⟨huc,hub⟩
  rw [DiscreteGroups.dilation_subgroupConjugate_compose] at hL
  change u.val ξ∈DiscreteGroups.mobiusLimitSet (DiscreteGroups.Action.Actions.subgroupConjugate u H) at hL
  rw [←nielsen_mobiusLimitSet_conjugation H u] at hL
  obtain ⟨p,hp,he⟩ := hL
  exact u.val.injective he ▸ hp

/-- A sphere-closed set disjoint from the true limit set meets the actual
closed Nielsen region in a genuine compact subset of the original open disc. -/
theorem nielsenCore_ordinary_closed_inter_compact
    {H : Subgroup Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H)
    (hNE : DiscreteGroups.IsNonElementary H)
    (K : Set Mobius.ExtendedComplex)
    (hK : IsClosed K)
    (hKL : Disjoint K (DiscreteGroups.mobiusLimitSet H)) :
    IsCompact ((Subtype.val : P.domain.carrier→Mobius.ExtendedComplex) ⁻¹'
      (K ∩ closure (P.asFuchsianDisc.nielsenRegion hNE))) := by
  let L := K ∩ closure (P.asFuchsianDisc.nielsenRegion hNE)
  have hLc : IsCompact L := (hK.inter isClosed_closure).isCompact
  have hLrange : L ⊆ range (Subtype.val : P.domain.carrier→Mobius.ExtendedComplex) := by
    intro z hz
    by_cases hzD : z∈P.domain.carrier
    · exact ⟨⟨z,hzD⟩,rfl⟩
    · have hzcl : z∈closure P.domain.carrier :=
        closure_mono (P.asFuchsianDisc.nielsenRegion_properties hNE).1 hz.2
      have hzB : z∈frontier P.asFuchsianDisc.carrier := by
        refine ⟨hzcl,?_⟩
        change z∉interior P.domain.carrier
        rwa [P.domain.isOpen.interior_eq]
      have hzL := nielsenRegion_closure_frontier_subset_limit P.asFuchsianDisc hNE ⟨hz.2,hzB⟩
      exact False.elim (Set.disjoint_left.mp hKL hz.1 hzL)
  exact P.domain.isOpen.isOpenEmbedding_subtypeVal.isEmbedding.isInducing.isCompact_preimage' hLc hLrange

/-- A genuine compact set in the original disc has finite actual density area;
the proof uses its true native half-plane image and the existing area measure. -/
theorem unitDisc_compact_area_ne_top
    {H : Subgroup Mobius.complexMobiusGroup} (P : UnitDiscFuchsianGroup H)
    {K : Set P.domain.carrier} (hK : IsCompact K) : P.area K≠⊤ := by
  rw [P.area_eq_halfPlane_volume K hK.isClosed.measurableSet]
  exact (hK.image P.halfPlaneCoordinate.continuous).measure_lt_top.ne

/-- The actual Nielsen portion lying in a sphere-closed ordinary set has finite
true hyperbolic density area, with no assumed compact-core conclusion. -/
theorem nielsenCore_ordinary_closed_inter_area_ne_top
    {H : Subgroup Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H)
    (hNE : DiscreteGroups.IsNonElementary H)
    (K : Set Mobius.ExtendedComplex)
    (hK : IsClosed K)
    (hKL : Disjoint K (DiscreteGroups.mobiusLimitSet H)) :
    P.area ((Subtype.val : P.domain.carrier→Mobius.ExtendedComplex) ⁻¹' K ∩
      fuchsianNielsenCore P hNE)≠⊤ := by
  have hCompact := nielsenCore_ordinary_closed_inter_compact P hNE K hK hKL
  apply ne_top_of_le_ne_top (unitDisc_compact_area_ne_top P hCompact)
  apply MeasureTheory.measure_mono
  rintro x ⟨hxK,hxN⟩
  exact ⟨hxK,subset_closure hxN⟩

/-- A true hyperbolic crosscut end has finite actual Nielsen-core area.
The ordinary-contact conclusion is derived from the original orbit and fixed
endpoints, rather than assumed as an extra end condition. -/
theorem unitDisc_hyperbolic_crosscut_region_core_area_ne_top
    {H : Subgroup Mobius.complexMobiusGroup} (P : UnitDiscFuchsianGroup H)
    (hNE : DiscreteGroups.IsNonElementary H)
    (w : P.domain.carrier)
    (hw : IsDirichletCenter P w)
    (k : H) (hk : Mobius.MobiusHyperbolic k.val)
    (a b : Circle)
    (hka : k.val.val ((a:ℂ):Mobius.ExtendedComplex) = ((a:ℂ):Mobius.ExtendedComplex))
    (hkb : k.val.val ((b:ℂ):Mobius.ExtendedComplex) = ((b:ℂ):Mobius.ExtendedComplex))
    (γ : Path (b:ℂ) (a:ℂ))
    (hInterior : range γ \ {(a:ℂ),(b:ℂ)} ⊆ Metric.ball (0:ℂ) 1)
    (δ : Path (a:ℂ) (b:ℂ)) (hδnorm : ∀ z ∈ range δ, ‖z‖ = 1)
    {C : Set ℂ} (hC : C = range γ ∪ range δ)
    (hCJ : Polygon.IsComplexJordanCurve C) (hCB : C ⊆ Metric.closedBall (0:ℂ) 1)
    (hOutside : ∀ g : H, (P.finiteCoordinate (g • w):ℂ) ∈ Polygon.complexJordanOutside C) :
    let region := (fun z : P.domain.carrier => (P.finiteCoordinate z:ℂ)) ⁻¹' Polygon.complexJordanInside C
    P.area ((region ∩ dirichletDomain P w) ∩ fuchsianNielsenCore P hNE)≠⊤ := by
  let region := (fun z : P.domain.carrier => (P.finiteCoordinate z:ℂ)) ⁻¹' Polygon.complexJordanInside C
  let D := dirichletDomain P w
  let K := closure ((Subtype.val : P.domain.carrier → Mobius.ExtendedComplex) '' region) ∩
    closure ((Subtype.val : P.domain.carrier → Mobius.ExtendedComplex) '' D)
  have hD := dirichletDomain_isConvexFuchsianPolygon P w hw
  have haNot : ((a:ℂ):Mobius.ExtendedComplex) ∉
      closure ((Subtype.val : P.domain.carrier → Mobius.ExtendedComplex) '' D) := by
    intro hh
    exact hD.hyperbolic_fixed_not_idealBoundary k hk (a:ℂ) hka
      ((mem_fuchsianPolygonIdealBoundary_iff_extendedClosure P D (a:ℂ)).mpr ⟨Circle.norm_coe a,hh⟩)
  have hbNot : ((b:ℂ):Mobius.ExtendedComplex) ∉
      closure ((Subtype.val : P.domain.carrier → Mobius.ExtendedComplex) '' D) := by
    intro hh
    exact hD.hyperbolic_fixed_not_idealBoundary k hk (b:ℂ) hkb
      ((mem_fuchsianPolygonIdealBoundary_iff_extendedClosure P D (b:ℂ)).mpr ⟨Circle.norm_coe b,hh⟩)
  have hregImage : (Subtype.val : P.domain.carrier → Mobius.ExtendedComplex) '' region ⊆
      (fun z : ℂ => (z:Mobius.ExtendedComplex)) '' Polygon.complexJordanInside C := by
    rintro z ⟨x,hx,rfl⟩
    exact ⟨P.finiteCoordinate x,hx,Surfaces.discFiniteChart_coe x⟩
  have hKL : Disjoint K (fuchsianLimitSet H) := by
    apply Set.disjoint_left.mpr
    rintro z ⟨hzReg,hzD⟩ hzL
    have hzFront := P.asFuchsianDisc.limitSet_subset_frontier hzL
    have hzNot : z ∉ P.domain.carrier := fun hh =>
      Set.disjoint_left.mp (disjoint_frontier_iff_isOpen.mpr P.domain.isOpen) hzFront hh
    obtain ⟨ξ,⟨hξcl,hξsphere⟩,hξz⟩ := unitDisc_inside_ambient_closure_contact hCB
      ⟨closure_mono hregImage hzReg,hzNot⟩
    change (ξ:Mobius.ExtendedComplex) = z at hξz
    have hξL : (ξ:Mobius.ExtendedComplex) ∈ fuchsianLimitSet H := by
      rw [hξz]
      exact hzL
    have hPair := unitDisc_crosscut_inside_limit_contact_endpoints
      P hNE w a b γ hInterior δ hδnorm hC hCJ hCB hOutside ⟨hξcl,hξsphere,hξL⟩
    rcases hPair with he | he
    · apply haNot
      rw [←hξz,he] at hzD
      exact hzD
    · apply hbNot
      have he' : ξ = (b:ℂ) := mem_singleton_iff.mp he
      rw [←hξz,he'] at hzD
      exact hzD
  have hfinite := nielsenCore_ordinary_closed_inter_area_ne_top P hNE K
    (isClosed_closure.inter isClosed_closure) (by rwa [←fuchsianLimitSet_eq_nonElementary H hNE])
  apply ne_top_of_le_ne_top hfinite
  apply measure_mono
  rintro z ⟨⟨hzR,hzD⟩,hzN⟩
  exact ⟨⟨subset_closure ⟨z,hzR,rfl⟩,subset_closure ⟨z,hzD,rfl⟩⟩,hzN⟩

/-- Any specified genuine determinant-one half-plane normalization preserves
the original actual density area of a measurable disc subset. -/
theorem normalizedPolygonHalfPlaneChart_area
    {H : Subgroup Mobius.complexMobiusGroup} (P : UnitDiscFuchsianGroup H)
    (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (S : Set P.domain.carrier) (hS : MeasurableSet S) :
    P.area S=volume (normalizedPolygonHalfPlaneChart P A '' S) := by
  rw [P.area_eq_halfPlane_volume S hS,normalizedPolygonHalfPlaneChart_image]
  have hh := measure_smul (volume : Measure ℍ) (Matrix.SpecialLinearGroup.mapGL ℝ A)
    (P.halfPlaneCoordinate '' S)
  change volume (fordSLNativeHom A '' (P.halfPlaneCoordinate '' S))=
    volume (P.halfPlaneCoordinate '' S) at hh
  exact hh.symm

/-- A positive-height portion of a bounded-width genuine half-plane strip
has finite actual hyperbolic density area. -/
theorem halfPlane_bounded_high_strip_volume_ne_top (b k : ℝ) (hk : 0<k) :
    volume {z : ℍ | |z.re|≤b ∧ k<z.im}≠⊤ := by
  have hv : volume (Hyperbolic.halfPlaneAboveGraph (fun _=>k) (Ioo (-b-1) (b+1)))≠⊤ := by
    rw [Hyperbolic.halfPlaneAboveGraph_volume _ _ measurable_const measurableSet_Ioo (fun _ _=>hk),
      lintegral_const,Measure.restrict_apply_univ,Real.volume_Ioo]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  apply ne_top_of_le_ne_top hv
  apply measure_mono
  rintro z ⟨hz,hzk⟩
  exact ⟨⟨by linarith [(abs_le.mp hz).1],by linarith [(abs_le.mp hz).2]⟩,hzk⟩

/-- Bounded width above positive height remains a finite true area region
in the original disc under its actual specified normalization. -/
theorem unitDisc_bounded_high_strip_area_ne_top
    {H : Subgroup Mobius.complexMobiusGroup} (P : UnitDiscFuchsianGroup H)
    (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (b k : ℝ) (hk : 0<k) :
    P.area {z | |(normalizedPolygonHalfPlaneChart P A z).re|≤b ∧
      k<(normalizedPolygonHalfPlaneChart P A z).im}≠⊤ := by
  let ψ := normalizedPolygonHalfPlaneChart P A
  have hS : MeasurableSet {z | |(ψ z).re|≤b ∧ k<(ψ z).im} :=
    (isClosed_le (UpperHalfPlane.continuous_re.comp ψ.continuous).abs continuous_const).measurableSet.inter
      (isOpen_lt continuous_const (UpperHalfPlane.continuous_im.comp ψ.continuous)).measurableSet
  rw [normalizedPolygonHalfPlaneChart_area P A _ hS]
  apply ne_top_of_le_ne_top (halfPlane_bounded_high_strip_volume_ne_top b k hk)
  apply measure_mono
  rintro z ⟨x,hx,rfl⟩
  exact hx

/-- A true normalized parabolic one-ended region has finite area in the
original polygon. Its low part is genuinely compact and its high part lies
in the proved finite-width positive-height strip. -/
theorem IsConvexFuchsianPolygon.parabolic_one_end_area_ne_top
    {H : Subgroup Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H}
    {D : Set P.domain.carrier}
    (hD : IsConvexFuchsianPolygon P D)
    (η : ℂ) (hη : η ∈ fuchsianPolygonIdealBoundary P D)
    (q : Mobius.complexMobiusGroup) (_hq : q.val '' Hyperbolic.extendedUnitDisc = Hyperbolic.openHalfPlaneSet)
    (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hA : Hyperbolic.realSLMobius A = q*Hyperbolic.cayleyMobius)
    (hqη : q.val (η : OnePoint ℂ) = ∞)
    (hT : DiscreteGroups.mobiusTranslation 1 ∈DiscreteGroups.Action.Actions.subgroupConjugate q H)
    (I : Set P.domain.carrier)
    (hI : closure ((Subtype.val : P.domain.carrier → Mobius.ExtendedComplex) '' I) \ P.domain.carrier ⊆ {(η :
      Mobius.ExtendedComplex)}) :
    P.area (D ∩ I)≠⊤ := by
  let ψ := normalizedPolygonHalfPlaneChart P A
  let S := ψ '' D
  obtain ⟨x,hx⟩ :=
    ((isFuchsianFundamentalDomain_iff P D).mp hD.locallyFinite.fundamental).2.1.nonempty
  let b := |(ψ x).re|+1
  have hwidth : ∀ z ∈ S, ∀ w ∈ S, w.re < z.re+1 := by
    intro z hz w hw
    exact hD.normalized_horizontal_width η hη q A hA hqη hT
      ((normalizedPolygonHalfPlaneChart_image P A D) ▸ hz)
      ((normalizedPolygonHalfPlaneChart_image P A D) ▸ hw)
  have hbound : ∀ z∈S, |z.re|≤b := by
    intro z hz
    have h₁ := hwidth (ψ x) ⟨x,hx,rfl⟩ z hz
    have h₂ := hwidth z hz (ψ x) ⟨x,hx,rfl⟩
    apply abs_le.mpr
    constructor
    · dsimp [b]
      linarith [neg_abs_le (ψ x).re]
    · dsimp [b]
      linarith [le_abs_self (ψ x).re]
  obtain ⟨K,hK,hIK⟩ :=
    unitDisc_one_endpoint_low_strip_precompact P I (η : Mobius.ExtendedComplex) hI q A hA hqη b 1
  let T := {z : P.domain.carrier | |(ψ z).re|≤b ∧ 1<(ψ z).im}
  have hKT : P.area (K∪T)≠⊤ := ne_top_of_le_ne_top
    (ENNReal.add_ne_top.mpr ⟨unitDisc_compact_area_ne_top P hK,
      unitDisc_bounded_high_strip_area_ne_top P A b 1 zero_lt_one⟩) (measure_union_le _ _)
  apply ne_top_of_le_ne_top hKT
  apply measure_mono
  rintro z ⟨hzD,hzI⟩
  by_cases hzHigh : 1<(ψ z).im
  · exact Or.inr ⟨hbound (ψ z) ⟨z,hzD,rfl⟩,hzHigh⟩
  · exact Or.inl (hIK z (subset_closure hzI) (hbound (ψ z) ⟨z,hzD,rfl⟩) (le_of_not_gt hzHigh))

/-- A genuine single-parabolic-limit region in any original convex polygon
has finite actual hyperbolic area. The actual fixed endpoint need not be an
ideal point of the polygon; that alternative is proved compact separately. -/
theorem IsConvexFuchsianPolygon.one_parabolic_limit_area_ne_top
    {H : Subgroup Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H}
    {D : Set P.domain.carrier}
    (hD : IsConvexFuchsianPolygon P D)
    (f : H)
    (hf : Mobius.MobiusParabolic f.val)
    (a : Mobius.ExtendedComplex)
    (ha : a ∈ frontier P.domain.carrier)
    (hfix : f.val.val a = a)
    (I : Set P.domain.carrier)
    (hI : closure ((Subtype.val : P.domain.carrier → Mobius.ExtendedComplex) '' I) \ P.domain.carrier ⊆ {a}) : P.area (D∩I)≠⊤ := by
  by_cases haD : a ∈ closure ((Subtype.val : P.domain.carrier → Mobius.ExtendedComplex) '' D)
  · have haC : a ∈ Mobius.complexCircle 0 1 := by
      change a ∈ frontier Hyperbolic.extendedUnitDisc at ha
      rwa [Mobius.frontier_extendedUnitDisc_eq_circle] at ha
    have han : a≠∞ := fun he => Mobius.complexCircle_infty 0 1 (he ▸ haC)
    obtain ⟨η,rfl⟩ := OnePoint.ne_infty_iff_exists.mp han
    have hn : ‖η‖=1 := by simpa only [Mobius.complexCircle_coe,sub_zero] using haC
    have hη : η∈fuchsianPolygonIdealBoundary P D :=
      (mem_fuchsianPolygonIdealBoundary_iff_extendedClosure P D η).mpr ⟨hn,haD⟩
    obtain ⟨q,hq,hT,hqη⟩ := parabolic_unit_halfPlane_normalizer P f hf (η:Mobius.ExtendedComplex) hfix
    obtain ⟨A,hA⟩ := halfPlane_chart_real_lift q hq
    exact Fuchsian.IsConvexFuchsianPolygon.parabolic_one_end_area_ne_top hD η hη q hq A hA hqη hT I hI
  · have hc := unitDisc_one_endpoint_closed_inter_compact P D I a hI haD
    apply ne_top_of_le_ne_top (unitDisc_compact_area_ne_top P hc)
    exact measure_mono (fun z hz => ⟨subset_closure hz.1,subset_closure hz.2⟩)

namespace RegularDirichletCircleData
variable {H : Subgroup Mobius.complexMobiusGroup} {P : Fuchsian.UnitDiscFuchsianGroup H}
  {w : P.domain.carrier} (d : Fuchsian.RegularDirichletCircleData P w)

/-- An actual finite-return radial end has finite true Nielsen-core area,
since its whole end is contained in the proved compact Jordan side. -/
theorem finite_period_radial_end_core_area_ne_top
    (hNE : DiscreteGroups.IsNonElementary H)
    (hw : Fuchsian.IsDirichletCenter P w)
    (x : Fuchsian.dirichletCircleCuts P w d.radius)
    (hpos : 0<d.endpointPeriod hw x) :
    P.area (d.radialEnd hw x ∩ Fuchsian.fuchsianNielsenCore P hNE)≠⊤ := by
  obtain ⟨region,_ho,hc,hQ⟩ := d.finite_period_radial_end_precompact hNE hw x hpos
  apply ne_top_of_le_ne_top (Fuchsian.unitDisc_compact_area_ne_top P hc)
  exact measure_mono (fun z hz => subset_closure (hQ hz.1))

/-- The actual developed hyperbolic component supplies finite Nielsen-core
area on the entire original radial end. No model crosscut is assumed. -/
theorem compactification_hyperbolic_radial_end_core_area_ne_top
    (hNE : DiscreteGroups.IsNonElementary H)
    (hw : Fuchsian.IsDirichletCenter P w)
    (x : Fuchsian.dirichletCircleCuts P w d.radius)
    {k : H} {F : ℝ → P.domain.carrier}
    (hArc : d.originalArc hw x ⊆ range F)
    (hF : range F ⊆ frontier (Fuchsian.fuchsianOrbitBallUnion P w d.radius))
    (hShape : Fuchsian.DiscFrontierCurveCompactification P k F)
    (hhyp : Mobius.MobiusHyperbolic k.val) :
    P.area (d.radialEnd hw x ∩ Fuchsian.fuchsianNielsenCore P hNE)≠⊤ := by
  rcases hShape with hp | hh
  · exact False.elim (hhyp.1.not_parabolic hp.1)
  · obtain ⟨A,B,_hAB,hAf,hBf,ha,hb,ψ,hψ,_hψcl,hψrange,_hψdisc⟩ := hh.2
    obtain ⟨a,b,haA,hbB,γ,hγ,hγRange,hInterior⟩ :=
      Fuchsian.unitDisc_two_endpoint_path_finite_data P F A B ha hb ψ hψ hψrange
    obtain ⟨ζ,hζL,hζa,hζb⟩ := Fuchsian.exists_disc_limit_circle_point_ne_pair P hNE a b
    let N := Fuchsian.fuchsianOrbitBallUnion P w d.radius
    have hOrbit (g : H) : g • w ∈ N := by
      apply mem_iUnion.mpr
      refine ⟨g,?_⟩
      change dist (P.halfPlaneCoordinate (g • w)) (P.halfPlaneCoordinate (g • w)) < d.radius
      simpa only [dist_self] using d.radius_pos
    have hγFront : range γ \ {(a:ℂ),(b:ℂ)} ⊆
        (fun z : P.domain.carrier => (P.finiteCoordinate z:ℂ)) '' frontier N := by
      intro z hz
      have hh := hγRange ▸ hz.1
      rcases hh with hza | hh
      · exact False.elim (hz.2 (Or.inl hza))
      · rcases hh with hzb | hh
        · exact False.elim (hz.2 (Or.inr (mem_singleton_iff.mpr hzb)))
        · obtain ⟨t,rfl⟩ := hh
          exact ⟨F t,hF (mem_range_self t),rfl⟩
    obtain ⟨δ,_hδ,hδnorm,J,_hJ,_hJi,hJRange,hJB,hCJ,hNout⟩ :=
      Fuchsian.unitDisc_crosscut_frontier_neighborhood_outside P hNE w
        d.orbit_neighborhood_open d.orbit_neighborhood_connected.isPreconnected hOrbit
        a b ζ hζa hζb hζL γ hγ hInterior hγFront
    let C := range J
    let region := (fun z : P.domain.carrier => (P.finiteCoordinate z:ℂ)) ⁻¹' Polygon.complexJordanInside C
    obtain ⟨hRo,hRfr⟩ := Fuchsian.unitDisc_crosscut_inside_preimage_properties P F a b γ hγRange δ hδnorm hJRange hCJ
    have hOutside (g : H) : (P.finiteCoordinate (g • w):ℂ) ∈ Polygon.complexJordanOutside C :=
      hNout ⟨g • w,hOrbit g,rfl⟩
    have hka : k.val.val ((a:ℂ):Mobius.ExtendedComplex) = ((a:ℂ):Mobius.ExtendedComplex) := by
      rw [haA]
      exact hAf
    have hkb : k.val.val ((b:ℂ):Mobius.ExtendedComplex) = ((b:ℂ):Mobius.ExtendedComplex) := by
      rw [hbB]
      exact hBf
    have hArea := Fuchsian.unitDisc_hyperbolic_crosscut_region_core_area_ne_top
      P hNE w hw k hhyp a b hka hkb γ hInterior δ hδnorm hJRange hCJ hJB hOutside
    have hRN : Disjoint region N := Fuchsian.unitDisc_inside_preimage_disjoint_of_outside P hCJ hNout
    have hRfront : frontier region ⊆ frontier N := by rw [hRfr]; exact hF
    have hcontact :
        ((Fuchsian.normalizedPolygonKleinCoordinate P w '' d.originalArc hw x) ∩
          closure (Fuchsian.normalizedPolygonKleinCoordinate P w '' region)).Nonempty := by
      obtain ⟨z,hz⟩ := d.originalArc_nonempty hw x
      refine ⟨Fuchsian.normalizedPolygonKleinCoordinate P w z,⟨z,hz,rfl⟩,?_⟩
      have hzR : z ∈ closure region := frontier_subset_closure (hRfr.symm ▸ hArc hz)
      exact mem_closure_image (Fuchsian.normalizedPolygonKleinCoordinate_isOpenEmbedding P
        w).continuous.continuousAt hzR
    have hQR := Fuchsian.dirichlet_Klein_strict_end_subset_region P w hw d.radius d.radius_pos
      (d.klein_originalArc_isPreconnected hw x) (d.klein_originalArc_subset_spherical_slice hw x)
      (d.klein_originalArc_isOpen_sphere hw x) hRo hRN hRfront hcontact
    apply ne_top_of_le_ne_top hArea
    apply measure_mono
    rintro z ⟨hzQ,hzN⟩
    exact ⟨⟨hQR hzQ,hzQ.1⟩,hzN⟩

/-- An actual parabolic developed component has finite true area on its whole
original radial end, hence on its actual Nielsen portion. -/
theorem compactification_parabolic_radial_end_core_area_ne_top
    (hNE : DiscreteGroups.IsNonElementary H)
    (hw : Fuchsian.IsDirichletCenter P w)
    (x : Fuchsian.dirichletCircleCuts P w d.radius)
    {k : H} {F : ℝ → P.domain.carrier}
    (hArc : d.originalArc hw x ⊆ range F)
    (hF : range F ⊆ frontier (Fuchsian.fuchsianOrbitBallUnion P w d.radius))
    (hShape : Fuchsian.DiscFrontierCurveCompactification P k F)
    (hpar : Mobius.MobiusParabolic k.val) :
    P.area (d.radialEnd hw x ∩ Fuchsian.fuchsianNielsenCore P hNE)≠⊤ := by
  obtain ⟨a,hfix,ha,region,_hIo,_hIfr,hQI,hIideal⟩ :=
    d.compactification_parabolic_radial_end_region hNE hw x hArc hF hShape hpar
  have hArea := Fuchsian.IsConvexFuchsianPolygon.one_parabolic_limit_area_ne_top
    (Fuchsian.dirichletDomain_isConvexFuchsianPolygon P w hw) k hpar a ha hfix region hIideal
  apply ne_top_of_le_ne_top hArea
  exact measure_mono (fun z hz => ⟨hz.1.1,hQI hz.1⟩)

/-- Every actual regular-circle component has finite true Nielsen-core area
on its whole radial end. All finite-return, parabolic and hyperbolic cases
are derived from the original developed curve. -/
theorem radial_end_core_area_ne_top
    (hNE : DiscreteGroups.IsNonElementary H)
    (hw : Fuchsian.IsDirichletCenter P w)
    (x : Fuchsian.dirichletCircleCuts P w d.radius) :
    P.area (d.radialEnd hw x ∩ Fuchsian.fuchsianNielsenCore P hNE)≠⊤ := by
  by_cases hzero : d.endpointPeriod hw x=0
  · obtain ⟨k,F,_hk,_hproper,_hembed,hArc,hF,hShape⟩ :=
      d.aperiodic_compactification_contains_originalArc hw x hzero
    have hOrig := hShape
    rcases hShape with hpar | hhyp
    · exact d.compactification_parabolic_radial_end_core_area_ne_top hNE hw x hArc hF hOrig hpar.1
    · exact d.compactification_hyperbolic_radial_end_core_area_ne_top hNE hw x hArc hF hOrig hhyp.1
  · exact d.finite_period_radial_end_core_area_ne_top hNE hw x (Nat.pos_of_ne_zero hzero)

include d in
/-- The genuine finite regular-circle data prove finite actual Nielsen-core
area of the whole original Dirichlet polygon. The finite index and each
end-area bound are derived, rather than assumed as finite ends or finite area. -/
theorem dirichlet_nielsenCoreArea_ne_top
    (hNE : DiscreteGroups.IsNonElementary H)
    (hw : Fuchsian.IsDirichletCenter P w) :
    Fuchsian.fuchsianNielsenCoreArea P hNE (Fuchsian.dirichletDomain P w)≠⊤ := by
  let : Finite (Fuchsian.dirichletCircleCuts P w d.radius) :=
    (Fuchsian.dirichletCircleCuts_finite P w hw d.radius).to_subtype
  let B : Set P.domain.carrier := {z | P.hyperbolicDist w z ≤ d.radius}
  have hBc : IsCompact B := by
    have hh := P.halfPlaneCoordinate.isCompact_preimage.mpr
      (isCompact_closedBall (P.halfPlaneCoordinate w) d.radius)
    convert hh using 1
    ext z
    change P.hyperbolicDist w z ≤ d.radius ↔ dist (P.halfPlaneCoordinate z) (P.halfPlaneCoordinate w) ≤ d.radius
    rw [dist_comm]
    rfl
  have hUnion : P.area (⋃ x : Fuchsian.dirichletCircleCuts P w d.radius,
      d.radialEnd hw x ∩ Fuchsian.fuchsianNielsenCore P hNE)≠⊤ := by
    have hh := measure_biUnion_lt_top (Set.finite_univ : (univ : Set (Fuchsian.dirichletCircleCuts P w
      d.radius)).Finite)
      (fun x _ => lt_top_iff_ne_top.mpr (d.radial_end_core_area_ne_top hNE hw x))
    simpa only [biUnion_univ] using hh.ne
  have hFinite : P.area (B ∪ ⋃ x : Fuchsian.dirichletCircleCuts P w d.radius,
      d.radialEnd hw x ∩ Fuchsian.fuchsianNielsenCore P hNE)≠⊤ :=
    measure_union_ne_top (Fuchsian.unitDisc_compact_area_ne_top P hBc) hUnion
  apply ne_top_of_le_ne_top hFinite
  apply measure_mono
  rintro z ⟨hzD,hzN⟩
  by_cases hzB : P.hyperbolicDist w z ≤ d.radius
  · exact Or.inl hzB
  · obtain ⟨x,hx⟩ := mem_iUnion.mp (d.radial_ends_cover_strict_exterior hw ⟨hzD,lt_of_not_ge hzB⟩)
    exact Or.inr (mem_iUnion.mpr ⟨x,hx,hzN⟩)

end RegularDirichletCircleData

/-- Finite generation gives finite true Nielsen-core area for every original
fundamental domain, using one constructed regular Dirichlet polygon and the
proved original invariant-area theorem. -/
theorem finitelyGenerated_nielsenCoreArea_ne_top
    {H : Subgroup Mobius.complexMobiusGroup} (P : UnitDiscFuchsianGroup H)
    (hNE : DiscreteGroups.IsNonElementary H)
    (hFG : H.FG)
    {D : Set P.domain.carrier}
    (hD : IsFuchsianFundamentalDomain P D) : fuchsianNielsenCoreArea P hNE D≠⊤ := by
  obtain ⟨z,hz,hfree⟩ := DiscreteGroups.discreteMobius_open_free_point H P.discrete P.domain.carrier
    P.domain.isOpen P.domain.isConnected.nonempty
  let w : P.domain.carrier := ⟨z,hz⟩
  have hw : IsDirichletCenter P w := by
    intro g hg
    exact hfree g (congrArg Subtype.val hg)
  let : Infinite H := DiscreteGroups.nonElementary_infinite H hNE
  obtain ⟨g,hg⟩ := exists_ne (1:H)
  obtain ⟨d,_hd⟩ := finitelyGenerated_regular_dirichlet_circle_data P hFG w hw g hg 1
  rw [fuchsianNielsenCoreArea_independent P hNE hD (dirichletDomain_fundamental P w hw)]
  exact d.dirichlet_nielsenCoreArea_ne_top hNE hw


end LowDimensionalTopology.Geometry.Fuchsian
