module
public import LowDimensionalTopology.Geometry.Polygon.Hyperbolic.Poincare.NativeMultiplicityPunctures
public import LowDimensionalTopology.Geometry.Hyperbolic.Angle.Measure.RadialLocalAngularMeasure
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter Topology MeasureTheory
open scoped UpperHalfPlane Complex.UnitDisc Pointwise ENNReal
namespace LowDimensionalTopology.Geometry.Polygon
open LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces
/-- A compact original polygon and actual local finiteness force finitely many
original nonempty sides; finite sidedness is derived rather than assumed. -/
theorem NativeGeodesicPolygonGeometry.finite_sides_of_compact
    {P : PoincarePolygon ℍ} {V : Set ℍ} (G : NativeGeodesicPolygonGeometry P V)
    (hP : IsCompact P.carrier) : Finite P.Side := by
  have hf:=G.locallyFinite.finite_nonempty_inter_compact hP
  have he : {s : P.Side | (s.val∩P.carrier).Nonempty}=univ := by
    apply eq_univ_of_forall
    intro s
    obtain ⟨x,hx⟩:=P.side_nonempty s.val s.property
    exact ⟨x,hx,P.side_subset_carrier s hx⟩
  exact Set.finite_univ_iff.mp (he ▸ hf)
/-- A genuine native isometric coordinate sending the specified physical point to
zero in the conformal disc. -/
def nativeAngularOriginChart (z : ℍ) : ℍ≃ₜComplex.UnitDisc:=
  (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry
    z.toSL2R⁻¹).toHomeomorph.trans _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyHomeomorph

theorem nativeAngularOriginChart_image (z : ℍ) (A : Set ℍ) :
    nativeAngularOriginChart z '' A=_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc '' ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry z.toSL2R⁻¹) '' A) := by
  rw [image_image]
  rfl

theorem nativeAngularOriginChart_apply_self (z : ℍ) :
    nativeAngularOriginChart z z=0 := by
  have hf : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry z.toSL2R⁻¹ z=UpperHalfPlane.I := by
    change z.toSL2R⁻¹ • z=UpperHalfPlane.I
    calc
      z.toSL2R⁻¹ • z=z.toSL2R⁻¹ • (z.toSL2R • UpperHalfPlane.I):=
        congrArg (fun w : ℍ=>z.toSL2R⁻¹ • w) (UpperHalfPlane.toSL2R_smul_I z).symm
      _=UpperHalfPlane.I:=inv_smul_smul _ _
  change _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry z.toSL2R⁻¹ z)=0
  rw [hf]
  simpa only [_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane_zero] using _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc_discToHalfPlane (0 : Complex.UnitDisc)

/-- This actual normalization preserves the genuine original local angular fraction. -/
theorem nativeLocalAngularFraction_originChart (A : Set ℍ) (z : ℍ) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.discLocalAngularFraction (nativeAngularOriginChart z '' A) 0=nativeLocalAngularFraction A z := by
  have hh:=nativeLocalAngularFraction_isometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry
    z.toSL2R⁻¹) A z
  have h0 : _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry z.toSL2R⁻¹ z)=0:=nativeAngularOriginChart_apply_self z
  rw [nativeAngularOriginChart_image]
  simpa only [nativeLocalAngularFraction,h0] using hh

/-- Every actual original supporting geodesic becomes an actual disc supporting
geodesic in the same physical origin chart. -/
theorem nativeAngularOriginChart_image_line (z : ℍ) (L :
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine) :
    ∃M : _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscLine,nativeAngularOriginChart z '' L.carrier=M.carrier := by
  obtain ⟨M,hM⟩:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.Isometry.halfPlane_image_hLine (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry z.toSL2R⁻¹).isometry L
  refine ⟨M.toDiscLine,?_⟩
  rw [nativeAngularOriginChart_image,hM,M.toDiscLine_carrier,M.discCarrier_eq_cayley_image]

/-- The genuine original side family supplies all actual normalized translated
frontiers, including nonconvex and reflex original polygon corners. -/
theorem NativeGeodesicPolygonGeometry.normalized_frontier_lines
    {P : PoincarePolygon ℍ} {V : Set ℍ} (G : NativeGeodesicPolygonGeometry P V)
    (H : Subgroup (ℍ≃ᵢℍ)) (I : Finset H) (z : ℍ) :
    ∃L : (I×P.Side)→_root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscLine,∀i : I,
      frontier (nativeAngularOriginChart z '' (i.val • P.carrier))⊆⋃j,(L j).carrier := by
  have hL (j : I×P.Side) : ∃M : _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscLine,
      nativeAngularOriginChart z '' (j.1.val • (G.line j.2).carrier)=M.carrier := by
    obtain ⟨K,hK⟩:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.Isometry.halfPlane_image_hLine j.1.val.val.isometry (G.line j.2)
    change ∃M : _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscLine,nativeAngularOriginChart z '' (j.1.val.val ''
      (G.line j.2).carrier)=M.carrier
    rw [hK]
    exact nativeAngularOriginChart_image_line z K
  choose L hL using hL
  refine ⟨L,?_⟩
  intro i q hq
  rw [←(nativeAngularOriginChart z).image_frontier] at hq
  obtain ⟨p,hp,rfl⟩:=hq
  change p∈frontier (i.val.val.toHomeomorph '' P.carrier) at hp
  rw [←i.val.val.toHomeomorph.image_frontier] at hp
  obtain ⟨w,hw,hwp⟩:=hp
  have hwB : w∈P.boundary:=by
    rw [←G.frontier_boundary]
    rw [G.carrier_closure] at hw
    exact frontier_closure_subset hw
  obtain ⟨s,hs,hws⟩:=mem_sUnion.mp hwB
  let t : P.Side:=⟨s,hs⟩
  apply mem_iUnion.mpr
  refine ⟨(i,t),?_⟩
  rw [←hL (i,t)]
  exact ⟨p,⟨w,G.side_subset_line t hws,hwp⟩,rfl⟩

/-- Compactness and local finiteness derive the finite actual supporting family.
Consequently one genuine origin ball makes every actual normalized translate's
frontier directions null, without assuming a sector model or prescribed corner angle. -/
theorem NativeGeodesicPolygonGeometry.normalized_frontier_radial_null
    {P : PoincarePolygon ℍ} {V : Set ℍ} (G : NativeGeodesicPolygonGeometry P V)
    (hP : IsCompact P.carrier) (H : Subgroup (ℍ≃ᵢℍ)) (I : Finset H) (z : ℍ) :
    ∃R : Ioo (0 : ℝ) 1,∀i : I,_root_.LowDimensionalTopology.Geometry.Hyperbolic.polygonDirectionMeasure
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discRadialDirections (frontier (nativeAngularOriginChart z ''
        (i.val • P.carrier))∩
        {p : Complex.UnitDisc | ‖(p : ℂ)‖<R.val}))=0 := by
  classical
  let : Finite P.Side:=G.finite_sides_of_compact hP
  obtain ⟨L,hL⟩:=G.normalized_frontier_lines H I z
  exact _root_.LowDimensionalTopology.Geometry.Hyperbolic.finite_discLine_frontier_radial_null _ L hL

/-- A positive actual radial scale preserves every genuine direction label. -/
theorem angularRadialPoint_injective (r : Ioo (0 : ℝ) 1) :
    Function.Injective (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discRadialPoint r) := by
  intro u v huv
  apply Subtype.ext
  have he:=congrArg ((↑) : Complex.UnitDisc→ℂ) huv
  exact mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr r.property.1.ne') he

/-- An arbitrary finite superset of the actual incident labels gives the genuine
extended angular sum, counted with the original group labels. -/
theorem nativePolygonAngularMultiplicity_eq_sum_translated_superset
    (H : Subgroup (ℍ≃ᵢℍ)) (P : Set ℍ) (hP : IsCompact P) (z : ℍ)
    (I : Finset H) (hI : ∀g : H,z∈g • P →g∈I) :
    nativePolygonAngularMultiplicity H P z=∑g∈I,nativeLocalAngularFraction (g • P) z := by
  classical
  rw [nativePolygonAngularMultiplicity_eq_translated]
  apply tsum_eq_sum
  intro g hg
  apply nativeLocalAngularFraction_of_not_mem_closure
  change z∉closure (g.val '' P)
  rw [(hP.image g.val.continuous).isClosed.closure_eq]
  exact fun hz=>hg (hI g hz)

/-- The original angular sum at every physical point, including original translated
vertices, equals the actual positive integer established on the punctured plane.
The proof uses the genuine finite radial membership count and angular Haar integration. -/
theorem NativeGeodesicPolygonGeometry.angularMultiplicity_at_all_points
    {P : PoincarePolygon ℍ} {V : Set ℍ} (G : NativeGeodesicPolygonGeometry P V)
    (H : Subgroup (ℍ≃ᵢℍ)) [DiscreteTopology H] (hP : IsCompact P.carrier)
    (k : ℕ) (hk : ∀y : ℍ,(∀g : H,y∉g • V) →
      nativePolygonAngularMultiplicityRadians H P.carrier y=2*Real.pi*(k : ℝ))
    (z : ℍ) : nativePolygonAngularMultiplicity H P.carrier z=k := by
  classical
  let : T2Space Complex.UnitDisc:=Complex.UnitDisc.isEmbedding_coe.t2Space
  let e:=nativeAngularOriginChart z
  obtain ⟨N,hN,hf⟩:=_root_.LowDimensionalTopology.Geometry.Fuchsian.native_compact_translates_locallyFinite H hP z
  let I:=hf.toFinset
  let F (i : I) : Set Complex.UnitDisc:=e '' (i.val • P.carrier)
  have hCover (y : ℍ) (hy : y∈N) (g : H) (hg : y∈g • P.carrier) : g∈I :=
    hf.mem_toFinset.mpr ⟨y,hg,hy⟩
  have hM (y : ℍ) (hy : ∀g : H,y∉g • V) :
      nativePolygonAngularMultiplicity H P.carrier y=k := by
    have hh:=hk y hy
    unfold nativePolygonAngularMultiplicityRadians at hh
    apply (ENNReal.toReal_eq_toReal_iff' (ne_of_lt
      (nativePolygonAngularMultiplicity_lt_top H P.carrier hP y)) (by simp)).mp
    have he : (nativePolygonAngularMultiplicity H P.carrier y).toReal=(k : ℝ):=
      mul_left_cancel₀ (by positivity : 2*Real.pi≠0) hh
    simpa only [ENNReal.toReal_natCast] using he
  obtain ⟨R₀,hR₀⟩:=G.normalized_frontier_radial_null hP H I z
  have he0 : e z=0:=nativeAngularOriginChart_apply_self z
  have hEN : e '' N∈𝓝 (0 : Complex.UnitDisc) := by
    simpa only [he0] using e.isOpenMap.image_mem_nhds hN
  have hENc:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.disc_coe_isOpenEmbedding.image_mem_nhds.mpr hEN
  obtain ⟨δ,hδ,hδN⟩:=Metric.mem_nhds_iff.mp hENc
  have hR₀pos:=R₀.property.1
  let R : Ioo (0 : ℝ) 1:=⟨min (R₀.val/2) (δ/2),⟨by positivity,by
    have hh:=min_le_left (R₀.val/2) (δ/2);nlinarith [R₀.property.2]⟩⟩
  have hRR₀ : R.val≤R₀.val:=by
    have hh:=min_le_left (R₀.val/2) (δ/2);dsimp [R];linarith
  have hRδ : R.val≤δ:=by
    have hh:=min_le_right (R₀.val/2) (δ/2);dsimp [R];linarith
  have hNull (i : I) : _root_.LowDimensionalTopology.Geometry.Hyperbolic.polygonDirectionMeasure
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discRadialDirections (frontier (F i)∩{p : Complex.UnitDisc | ‖(p : ℂ)‖<R.val}))=0 := by
    apply measure_mono_null _ (hR₀ i)
    apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.discRadialDirections_mono
    rintro p ⟨hp,hpR⟩
    exact ⟨hp,lt_of_lt_of_le hpR hRR₀⟩
  let r : Ioo (0 : ℝ) 1:=⟨R.val/2,⟨div_pos R.property.1 (by norm_num),by nlinarith [R.property.2]⟩⟩
  have hrR : r.val<R.val:=by dsimp [r];linarith [R.property.1]
  have hSampleN (u : Circle) : e.symm (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discRadialPoint r u)∈N := by
    have himg : (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discRadialPoint r u : ℂ)∈((↑) : Complex.UnitDisc→ℂ) '' (e '' N):=hδN (by
      change dist (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discRadialPoint r u : ℂ) (0 : ℂ)<δ
      rw [dist_zero_right,_root_.LowDimensionalTopology.Geometry.Hyperbolic.discRadialPoint_norm]
      exact lt_of_lt_of_le hrR hRδ)
    have hin : _root_.LowDimensionalTopology.Geometry.Hyperbolic.discRadialPoint r u∈e '' N:=Complex.UnitDisc.coe_injective.mem_set_image.mp himg
    obtain ⟨p,hp,heq⟩:=hin
    have hh : e.symm (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discRadialPoint r u)=p := by rw [←heq,e.symm_apply_apply]
    rwa [hh]
  have hBad : _root_.LowDimensionalTopology.Geometry.Hyperbolic.polygonDirectionMeasure
      {u : Circle | e.symm (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discRadialPoint r u)∈⋃g : H,g • V}=0 :=
    ((G.translated_vertices_countable H).preimage
      (e.symm.injective.comp (angularRadialPoint_injective
        r))).measure_zero _root_.LowDimensionalTopology.Geometry.Hyperbolic.polygonDirectionMeasure
  have hFrontier (i : I) : ∀ᵐu ∂_root_.LowDimensionalTopology.Geometry.Hyperbolic.polygonDirectionMeasure,
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.discRadialPoint r u∉frontier (F i) := by
    apply measure_eq_zero_iff_ae_notMem.mp
    apply measure_mono_null _ (hNull i)
    intro u hu
    refine ⟨r,hu,?_⟩
    change ‖(_root_.LowDimensionalTopology.Geometry.Hyperbolic.discRadialPoint r u : ℂ)‖<R.val
    rwa [_root_.LowDimensionalTopology.Geometry.Hyperbolic.discRadialPoint_norm]
  have hCount : ∀ᵐu ∂_root_.LowDimensionalTopology.Geometry.Hyperbolic.polygonDirectionMeasure,
      (∑i : I,(_root_.LowDimensionalTopology.Geometry.Hyperbolic.discRadialPoint r ⁻¹' F i).indicator (fun _ : Circle=>(1 : ℝ≥0∞)) u)=(k : ℝ≥0∞) := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hBad,Filter.eventually_all.mpr hFrontier] with u hu hFu
    let p:=e.symm (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discRadialPoint r u)
    have hpV : ∀g : H,p∉g • V:=fun g hg=>hu (mem_iUnion.mpr ⟨g,hg⟩)
    have hSum : nativePolygonAngularMultiplicity H P.carrier p=
        ∑i : I,nativeLocalAngularFraction (i.val • P.carrier) p := by
      rw [nativePolygonAngularMultiplicity_eq_sum_translated_superset H P.carrier hP p I
        (hCover p (hSampleN u))]
      exact (Finset.sum_coe_sort I _).symm
    calc
      (∑i : I,(_root_.LowDimensionalTopology.Geometry.Hyperbolic.discRadialPoint r ⁻¹' F i).indicator (fun _ :
        Circle=>(1 : ℝ≥0∞)) u)=
          ∑i : I,nativeLocalAngularFraction (i.val • P.carrier) p := by
        apply Finset.sum_congr rfl
        intro i _
        have hpF : p∉frontier (i.val • P.carrier) := by
          intro hpF
          apply hFu i
          change _root_.LowDimensionalTopology.Geometry.Hyperbolic.discRadialPoint r u∈frontier (e '' (i.val •
            P.carrier))
          rw [←e.image_frontier]
          exact ⟨p,hpF,e.apply_symm_apply _⟩
        rw [nativeLocalAngularFraction_eq_indicator_off_frontier _ _ hpF]
        have hmem : u∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.discRadialPoint r ⁻¹' F i ↔p∈i.val • P.carrier := by
          change _root_.LowDimensionalTopology.Geometry.Hyperbolic.discRadialPoint r u∈e '' (i.val •
            P.carrier) ↔p∈i.val • P.carrier
          constructor
          · rintro ⟨q,hq,heq⟩
            have hh : p=q := by dsimp [p];rw [←heq,e.symm_apply_apply]
            rwa [hh]
          · intro hp
            exact ⟨p,hp,e.apply_symm_apply _⟩
        by_cases hm : p∈i.val • P.carrier
        · rw [indicator_of_mem (hmem.mpr hm),indicator_of_mem hm]
        · rw [indicator_of_notMem (fun h=>hm (hmem.mp h)),indicator_of_notMem hm]
      _=nativePolygonAngularMultiplicity H P.carrier p:=hSum.symm
      _=k:=hM p hpV
  have hFMeas (i : I) : MeasurableSet (F i):=
    ((hP.image i.val.val.continuous).image e.continuous).isClosed.measurableSet
  have hAngles : (∑i : I,_root_.LowDimensionalTopology.Geometry.Hyperbolic.discLocalAngularFraction (F i) 0)=(k :
    ℝ≥0∞):=
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.finite_local_angular_sum_of_radial_count F R hFMeas hNull k hCount
  calc
    nativePolygonAngularMultiplicity H P.carrier z=
        ∑g∈I,nativeLocalAngularFraction (g • P.carrier) z :=
      nativePolygonAngularMultiplicity_eq_sum_translated_superset H P.carrier hP z I
        (hCover z (mem_of_mem_nhds hN))
    _=∑i : I,nativeLocalAngularFraction (i.val • P.carrier) z :=(Finset.sum_coe_sort I _).symm
    _=∑i : I,_root_.LowDimensionalTopology.Geometry.Hyperbolic.discLocalAngularFraction (F i) 0 :=Finset.sum_congr rfl
      (fun i _=>(nativeLocalAngularFraction_originChart (i.val • P.carrier) z).symm)
    _=k :=hAngles

/-- The original opposite-side pairing and actual native discreteness force one
positive integer angular multiplicity at every physical point, with no vertex exception. -/
theorem NativeGeodesicPolygonGeometry.angularMultiplicity_positive_integer
    {P : PoincarePolygon ℍ} {V : Set ℍ} (G : NativeGeodesicPolygonGeometry P V)
    (S : PoincareSidePairing (ℍ≃ᵢℍ) P) [DiscreteTopology S.Generated]
    (hP : IsCompact P.carrier)
    (hV : ∀x∈V,∀s : P.Side,x∈s.val →S.element s x∈V)
    (hOpp : ∀s : P.Side,∀x∈s.val,x∉V →S.OppositeSideNeighborhoods s x) :
    ∃k : ℕ,0<k ∧∀z : ℍ,nativePolygonAngularMultiplicity S.Generated P.carrier z=k := by
  obtain ⟨k,hk,hAway⟩:=G.angularMultiplicity_positive_integer_away_vertices S hP hV hOpp
  exact ⟨k,hk,fun z=>G.angularMultiplicity_at_all_points S.Generated hP k hAway z⟩

/-- The actual original inside and actual full polygon have identical local angles
at every physical point, including reflex and translated vertex germs. -/
theorem NativeGeodesicPolygonGeometry.localAngularFraction_interior_eq
    {P : PoincarePolygon ℍ} {V : Set ℍ} (G : NativeGeodesicPolygonGeometry P V)
    (hP : IsCompact P.carrier) (z : ℍ) :
    nativeLocalAngularFraction P.interior z=nativeLocalAngularFraction P.carrier z := by
  classical
  let H : Subgroup (ℍ≃ᵢℍ):=⊥
  let I : Finset H:={1}
  let i : I:=⟨1,by simp [I]⟩
  obtain ⟨R,hR⟩:=G.normalized_frontier_radial_null hP H I z
  have hn : _root_.LowDimensionalTopology.Geometry.Hyperbolic.polygonDirectionMeasure
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discRadialDirections (frontier (nativeAngularOriginChart z ''
        P.carrier)∩
        {p : Complex.UnitDisc | ‖(p : ℂ)‖<R.val}))=0 := by
    simpa only [i,one_smul] using hR i
  have hh:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discLocalAngularFraction_interior_eq_of_frontier_radial_null
    (nativeAngularOriginChart z '' P.carrier) R hn
  have hi : interior P.carrier=P.interior:=by rw [G.carrier_closure,G.regular_open]
  rw [←(nativeAngularOriginChart z).image_interior,hi,
    nativeLocalAngularFraction_originChart,nativeLocalAngularFraction_originChart] at hh
  exact hh

/-- The original open polygon and its literal closure give the same entire angular
sum, with all original group labels retained. -/
theorem NativeGeodesicPolygonGeometry.angularMultiplicity_interior_eq
    {P : PoincarePolygon ℍ} {V : Set ℍ} (G : NativeGeodesicPolygonGeometry P V)
    (hP : IsCompact P.carrier) (H : Subgroup (ℍ≃ᵢℍ)) (z : ℍ) :
    nativePolygonAngularMultiplicity H P.interior z=nativePolygonAngularMultiplicity H P.carrier z := by
  unfold nativePolygonAngularMultiplicity
  exact tsum_congr (fun g=>G.localAngularFraction_interior_eq hP (g⁻¹ • z))

/--
The angular-multiplicity clause for the original open
Jordan polygon, original side intervals and original side pairing: one positive integer
counts the genuine entire angular sum at every point, including every translated vertex.
The quotient-area and branched-cover clauses are separate obligations.
-/
theorem nativeJordan_angularMultiplicity_positive_integer
    {P : PoincarePolygon ℍ}
    (C : Set ℂ) (hC : IsComplexJordanCurve C) (hbound : C⊆Metric.closedBall (0 : ℂ) 1)
    (hInside : P.interior=nativeJordanInside C)
    (hBoundary : P.boundary=(fun z : ℍ=>(_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z : ℂ)) ⁻¹'
      C)
    (D : NativeGeodesicSideIntervals P) (S : PoincareSidePairing (ℍ≃ᵢℍ) P)
    [DiscreteTopology S.Generated] (hP : IsCompact P.carrier)
    (hOpp : ∀s : P.Side,∀x∈s.val,x∉D.vertices →S.OppositeSideNeighborhoods s x) :
    ∃k : ℕ,0<k ∧∀z : ℍ,
      nativePolygonAngularMultiplicity S.Generated P.interior z=k ∧
      nativePolygonAngularMultiplicityRadians S.Generated P.interior z=2*Real.pi*(k : ℝ) := by
  let G:=nativeJordan_sideIntervals_geometry C hC hbound hInside hBoundary D
  obtain ⟨k,hk,hAll⟩:=G.angularMultiplicity_positive_integer S hP (D.pairing_preserves_vertices S) hOpp
  refine ⟨k,hk,fun z=>?_⟩
  have hh : nativePolygonAngularMultiplicity S.Generated P.interior z=k:=
    (G.angularMultiplicity_interior_eq hP S.Generated z).trans (hAll z)
  refine ⟨hh,?_⟩
  rw [nativePolygonAngularMultiplicityRadians,hh,ENNReal.toReal_natCast]

end LowDimensionalTopology.Geometry.Polygon
