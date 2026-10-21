/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Mobius.Circle.GeometricDisc
public import LowDimensionalTopology.Geometry.Hyperbolic.Models.Disc.ExtendedCarrier
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.GeneralizedCircleSides
public import LowDimensionalTopology.Geometry.Fuchsian.Dirichlet.GeneralizedDirichletPolygons
@[expose] public section
open Set
open scoped Topology OnePoint Pointwise UpperHalfPlane MatrixGroups ComplexConjugate
namespace LowDimensionalTopology.Geometry.Hyperbolic
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Surfaces LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Inversive LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
noncomputable section

/-- A real-centred circle's interior cut in H is genuinely preconnected. -/
theorem halfPlaneCircleInside_isPreconnected (c r : ℝ) :
    IsPreconnected {z : ℍ | ‖(z : ℂ)-(c : ℂ)‖<r}:=by
  apply UpperHalfPlane.isEmbedding_coe.isInducing.isPreconnected_image.mp
  have he : ((↑) : ℍ→ℂ) '' {z : ℍ | ‖(z : ℂ)-(c : ℂ)‖<r}=
      {z : ℂ | 0<z.im}∩Metric.ball (c : ℂ) r:=by
    ext z
    constructor
    · rintro ⟨w,hw,rfl⟩
      exact ⟨w.im_pos,by simpa only [Metric.mem_ball,dist_eq_norm,Set.mem_ofPred_eq] using hw⟩
    · rintro ⟨hz,hr⟩
      exact ⟨⟨z,hz⟩,by simpa only [Metric.mem_ball,dist_eq_norm,Set.mem_ofPred_eq] using hr,rfl⟩
  rw [he]
  exact ((convex_halfSpace_gt Complex.imCLM.toLinearMap.isLinear 0).inter (convex_ball (c : ℂ) r)).isPreconnected

/-- The genuine interior of a semicircle is the native component of its geodesic complement. -/
theorem openHHalfPlane_circle_inside (c r : ℝ) (hr : 0<r) (w : ℍ)
    (hw : ‖(w : ℂ)-(c : ℂ)‖<r) :
    openHHalfPlane (.circle c r hr) w={z : ℍ | ‖(z : ℂ)-(c : ℂ)‖<r}:=by
  let L:=HalfPlaneLine.circle c r hr
  let f : ℍ→ℝ:=fun z=>‖(z : ℂ)-(c : ℂ)‖
  have hf : Continuous f:=(UpperHalfPlane.continuous_coe.sub continuous_const).norm
  have hwN : w∈L.carrierᶜ:=ne_of_lt hw
  apply subset_antisymm
  · intro z hz
    have hpre:=(isPreconnected_connectedComponentIn (F:=L.carrierᶜ) (x:=w)).image f hf.continuousOn
    have hwI:=mem_image_of_mem f (mem_connectedComponentIn hwN)
    have hzI:=mem_image_of_mem f hz
    by_contra hn
    have hge : r≤f z:=not_lt.mp hn
    obtain ⟨u,hu,he⟩:=hpre.ordConnected.out hwI hzI (show r∈Icc (f w) (f z) from ⟨hw.le,hge⟩)
    exact connectedComponentIn_subset L.carrierᶜ w hu he
  · apply (halfPlaneCircleInside_isPreconnected c r).subset_connectedComponentIn hw
    exact fun z hz=>ne_of_lt hz

/-- The actual component at a finite interior point of a Euclidean circle normalizes to the unit disc. -/
theorem circle_complement_component_inside_image (c w : ℂ) (r : ℝ) (hr : 0<r)
    (hw : ‖w-c‖<r) :
    (Fuchsian.circleNormalizingMobius c r hr).val '' connectedComponentIn (Mobius.complexCircle c r)ᶜ (w :
      Mobius.ExtendedComplex)=extendedUnitDisc:=by
  have hwN : (w : Mobius.ExtendedComplex)∈(Mobius.complexCircle c r)ᶜ:=by
    simp only [mem_compl_iff,Mobius.complexCircle_coe]
    exact ne_of_lt hw
  have hwq : (Fuchsian.circleNormalizingMobius c r hr).val w∈extendedUnitDisc:=by
    rw [Fuchsian.circleNormalizingMobius_coe,coe_mem_extendedUnitDisc,norm_div,
      Complex.norm_real,Real.norm_eq_abs,abs_of_pos hr,div_lt_iff₀ hr,one_mul]
    exact hw
  have he:=(Mobius.mobiusBoundaryHomeomorph (Fuchsian.circleNormalizingMobius c r hr)).image_connectedComponentIn hwN
  change (Fuchsian.circleNormalizingMobius c r hr).val '' connectedComponentIn (Mobius.complexCircle c r)ᶜ (w :
    Mobius.ExtendedComplex)=
    connectedComponentIn ((Fuchsian.circleNormalizingMobius c r hr).val '' (Mobius.complexCircle c r)ᶜ)
      ((Fuchsian.circleNormalizingMobius c r hr).val w) at he
  rw [(Fuchsian.circleNormalizingMobius c r hr).val.image_compl,Fuchsian.circleNormalizingMobius_image_circle,
    Mobius.connectedComponentIn_unitCircle_compl_of_mem_disc hwq] at he
  exact he

/-- The finite-center interior component has exactly the expected strict Euclidean ball points. -/
theorem mem_circle_complement_component_inside (c w z : ℂ) (r : ℝ) (hr : 0<r)
    (hw : ‖w-c‖<r) :
    (z : Mobius.ExtendedComplex)∈connectedComponentIn (Mobius.complexCircle c r)ᶜ (w : Mobius.ExtendedComplex) ↔
      ‖z-c‖<r:=by
  have he:=circle_complement_component_inside_image c w r hr hw
  have hm : (z : Mobius.ExtendedComplex)∈connectedComponentIn (Mobius.complexCircle c r)ᶜ (w : Mobius.ExtendedComplex) ↔
      (Fuchsian.circleNormalizingMobius c r hr).val z∈extendedUnitDisc:=by
    rw [←he]
    constructor
    · exact fun hz=>⟨z,hz,rfl⟩
    · rintro ⟨u,hu,he⟩
      exact (Fuchsian.circleNormalizingMobius c r hr).val.injective he ▸ hu
  rw [hm,Fuchsian.circleNormalizingMobius_coe,coe_mem_extendedUnitDisc,norm_div,
    Complex.norm_real,Real.norm_eq_abs,abs_of_pos hr,div_lt_iff₀ hr,one_mul]

/-- Every exterior finite center belongs to the same actual spherical component as infinity. -/
theorem circle_complement_component_outside_eq_infty (c w : ℂ) (r : ℝ) (hr : 0<r)
    (hw : r<‖w-c‖) :
    connectedComponentIn (Mobius.complexCircle c r)ᶜ (w : Mobius.ExtendedComplex)=
      connectedComponentIn (Mobius.complexCircle c r)ᶜ ∞:=by
  exact (connectedComponentIn_eq ((Fuchsian.mem_circle_complement_component_infty c w r hr).mpr hw)).symm

/-- A real-centred complete circle's spherical side intersects H in precisely the native hyperbolic half-plane. -/
theorem halfPlaneCircle_sphere_component_eq (c r : ℝ) (hr : 0<r) (w : ℍ)
    (hw : w∉(HalfPlaneLine.circle c r hr).carrier) :
    {z : ℍ | ((z : ℂ) : Mobius.ExtendedComplex)∈connectedComponentIn (Mobius.complexCircle (c : ℂ) r)ᶜ ((w : ℂ) :
      Mobius.ExtendedComplex)}=
      openHHalfPlane (.circle c r hr) w:=by
  have hwN : ‖(w : ℂ)-(c : ℂ)‖≠r:=hw
  rcases lt_or_gt_of_ne hwN with hi|ho
  · rw [openHHalfPlane_circle_inside c r hr w hi]
    ext z
    change (((z : ℂ) : Mobius.ExtendedComplex)∈connectedComponentIn (Mobius.complexCircle (c : ℂ) r)ᶜ ((w : ℂ) :
      Mobius.ExtendedComplex)) ↔ ‖(z : ℂ)-(c : ℂ)‖<r
    exact mem_circle_complement_component_inside _ _ _ _ hr hi
  · rw [circle_complement_component_outside_eq_infty _ _ _ hr ho,openHHalfPlane_circle_outside c r hr w ho]
    ext z
    change (((z : ℂ) : Mobius.ExtendedComplex)∈connectedComponentIn (Mobius.complexCircle (c : ℂ) r)ᶜ ∞) ↔ r<‖(z : ℂ)-(c
      : ℂ)‖
    exact Fuchsian.mem_circle_complement_component_infty _ _ _ hr

/-- The actual finite left side of a vertical complete mirror. -/
def mirrorLeftSide (x : ℝ) : Set Mobius.ExtendedComplex:=
  ((↑) : ℂ→Mobius.ExtendedComplex) '' {z : ℂ | z.re<x}

/-- The actual finite right side of a vertical complete mirror. -/
def mirrorRightSide (x : ℝ) : Set Mobius.ExtendedComplex:=
  ((↑) : ℂ→Mobius.ExtendedComplex) '' {z : ℂ | x<z.re}

theorem mirrorLeftSide_coe (x : ℝ) (z : ℂ) : (z : Mobius.ExtendedComplex)∈mirrorLeftSide x ↔ z.re<x:=by
  constructor
  · rintro ⟨w,hw,he⟩
    exact OnePoint.coe_injective he ▸ hw
  · exact fun hz=>⟨z,hz,rfl⟩

theorem mirrorRightSide_coe (x : ℝ) (z : ℂ) : (z : Mobius.ExtendedComplex)∈mirrorRightSide x ↔ x<z.re:=by
  constructor
  · rintro ⟨w,hw,he⟩
    exact OnePoint.coe_injective he ▸ hw
  · exact fun hz=>⟨z,hz,rfl⟩

theorem mirrorLeftSide_isOpen (x : ℝ) : IsOpen (mirrorLeftSide x):=
  OnePoint.isOpenEmbedding_coe.isOpenMap _ (isOpen_lt Complex.continuous_re continuous_const)

theorem mirrorRightSide_isOpen (x : ℝ) : IsOpen (mirrorRightSide x):=
  OnePoint.isOpenEmbedding_coe.isOpenMap _ (isOpen_lt continuous_const Complex.continuous_re)

theorem mirrorLeftSide_isPreconnected (x : ℝ) : IsPreconnected (mirrorLeftSide x):=
  (convex_halfSpace_lt Complex.reCLM.toLinearMap.isLinear x).isPreconnected.image _
    OnePoint.continuous_coe.continuousOn

theorem mirrorRightSide_isPreconnected (x : ℝ) : IsPreconnected (mirrorRightSide x):=
  (convex_halfSpace_gt Complex.reCLM.toLinearMap.isLinear x).isPreconnected.image _
    OnePoint.continuous_coe.continuousOn

theorem mirrorLeftRight_disjoint (x : ℝ) : Disjoint (mirrorLeftSide x) (mirrorRightSide x):=by
  apply Set.disjoint_left.mpr
  rintro ξ ⟨z,hz,rfl⟩ hzR
  have hr:=(mirrorRightSide_coe x z).mp hzR
  exact lt_asymm hz hr

theorem verticalCircle_compl (x : ℝ) : (Mobius.complexLine 1 x)ᶜ=mirrorLeftSide x∪mirrorRightSide x:=by
  ext ξ
  induction ξ using OnePoint.rec with
  | infty => simp [mirrorLeftSide,mirrorRightSide]
  | coe z =>
    simp only [mem_compl_iff,Mobius.complexLine_coe,mem_union,mirrorLeftSide_coe,mirrorRightSide_coe]
    have he : inner ℝ z (1 : ℂ)=z.re:=by simp [Complex.inner]
    rw [he]
    exact ne_iff_lt_or_gt

theorem verticalCircle_component_left (x : ℝ) (ξ : Mobius.ExtendedComplex) (hξ : ξ∈mirrorLeftSide x) :
    connectedComponentIn (Mobius.complexLine 1 x)ᶜ ξ=mirrorLeftSide x:=by
  have hsub : mirrorLeftSide x⊆(Mobius.complexLine 1 x)ᶜ:=by rw [verticalCircle_compl];exact subset_union_left
  apply subset_antisymm
  · apply IsPreconnected.subset_left_of_subset_union (mirrorLeftSide_isOpen x)
      (mirrorRightSide_isOpen x) (mirrorLeftRight_disjoint x)
    · rw [←verticalCircle_compl];exact connectedComponentIn_subset _ _
    · exact ⟨ξ,mem_connectedComponentIn (hsub hξ),hξ⟩
    · exact isPreconnected_connectedComponentIn
  · exact (mirrorLeftSide_isPreconnected x).subset_connectedComponentIn hξ hsub

theorem verticalCircle_component_right (x : ℝ) (ξ : Mobius.ExtendedComplex) (hξ : ξ∈mirrorRightSide x) :
    connectedComponentIn (Mobius.complexLine 1 x)ᶜ ξ=mirrorRightSide x:=by
  have hsub : mirrorRightSide x⊆(Mobius.complexLine 1 x)ᶜ:=by rw [verticalCircle_compl];exact subset_union_right
  apply subset_antisymm
  · apply IsPreconnected.subset_right_of_subset_union (mirrorLeftSide_isOpen x)
      (mirrorRightSide_isOpen x) (mirrorLeftRight_disjoint x)
    · rw [←verticalCircle_compl];exact connectedComponentIn_subset _ _
    · exact ⟨ξ,mem_connectedComponentIn (hsub hξ),hξ⟩
    · exact isPreconnected_connectedComponentIn
  · exact (mirrorRightSide_isPreconnected x).subset_connectedComponentIn hξ hsub

theorem halfPlaneVerticalRight_isPreconnected (x : ℝ) : IsPreconnected {z : ℍ | x<z.re}:=by
  apply UpperHalfPlane.isEmbedding_coe.isInducing.isPreconnected_image.mp
  have he : ((↑) : ℍ→ℂ) '' {z : ℍ | x<z.re}={z : ℂ | 0<z.im}∩{z : ℂ | x<z.re}:=by
    ext z
    constructor
    · rintro ⟨w,hw,rfl⟩;exact ⟨w.im_pos,hw⟩
    · rintro ⟨hz,hr⟩;exact ⟨⟨z,hz⟩,hr,rfl⟩
  rw [he]
  exact ((convex_halfSpace_gt Complex.imCLM.toLinearMap.isLinear 0).inter
    (convex_halfSpace_gt Complex.reCLM.toLinearMap.isLinear x)).isPreconnected

theorem openHHalfPlane_vertical_right (x : ℝ) (w : ℍ) (hw : x<w.re) :
    openHHalfPlane (.vertical x) w={z : ℍ | x<z.re}:=by
  have hwN : w∈(HalfPlaneLine.vertical x).carrierᶜ:=ne_of_gt hw
  apply subset_antisymm
  · intro z hz
    have hp:=(isPreconnected_connectedComponentIn (F:=(HalfPlaneLine.vertical x).carrierᶜ)
      (x:=w)).image UpperHalfPlane.re UpperHalfPlane.continuous_re.continuousOn
    have hwI:=mem_image_of_mem UpperHalfPlane.re (mem_connectedComponentIn hwN)
    have hzI:=mem_image_of_mem UpperHalfPlane.re hz
    by_contra hn
    have hle : z.re≤x:=not_lt.mp hn
    obtain ⟨v,hv,he⟩:=hp.ordConnected.out hzI hwI (show x∈Icc z.re w.re from ⟨hle,hw.le⟩)
    exact connectedComponentIn_subset (HalfPlaneLine.vertical x).carrierᶜ w hv he
  · apply (halfPlaneVerticalRight_isPreconnected x).subset_connectedComponentIn hw
    exact fun z hz=>ne_of_gt hz

/-- Every complete vertical mirror's spherical side has exactly the native H component as its finite cut. -/
theorem halfPlaneVertical_sphere_component_eq (x : ℝ) (w : ℍ)
    (hw : w∉(HalfPlaneLine.vertical x).carrier) :
    {z : ℍ | ((z : ℂ) : Mobius.ExtendedComplex)∈connectedComponentIn (Mobius.complexLine 1 x)ᶜ ((w : ℂ) :
      Mobius.ExtendedComplex)}=
      openHHalfPlane (.vertical x) w:=by
  have hne : w.re≠x:=hw
  rcases lt_or_gt_of_ne hne with hi|ho
  · rw [verticalCircle_component_left x _ ((mirrorLeftSide_coe x _).mpr hi),hReCutLt_eq_openHalfPlane x w hi]
    ext z
    exact mirrorLeftSide_coe x z
  · rw [verticalCircle_component_right x _ ((mirrorRightSide_coe x _).mpr ho),openHHalfPlane_vertical_right x w ho]
    ext z
    exact mirrorRightSide_coe x z

/-- Intersecting the actual spherical containing component with H gives the actual hyperbolic half-plane component. -/
theorem halfPlaneLine_sphere_component_eq (L : HalfPlaneLine) (w : ℍ) (hw : w∉L.carrier) :
    {z : ℍ | ((z : ℂ) : Mobius.ExtendedComplex)∈connectedComponentIn L.extendedCircle.valᶜ ((w : ℂ) :
      Mobius.ExtendedComplex)}=
      openHHalfPlane L w:=by
  cases L with
  | vertical x => exact halfPlaneVertical_sphere_component_eq x w hw
  | circle c r hr => exact halfPlaneCircle_sphere_component_eq c r hr w hw

/-- At a native interior center, the original geometric normalized half-plane is the actual closer-distance half-plane. -/
theorem normalizedDirichletHalfPlane_interior_formula
    {H : Subgroup Mobius.complexMobiusGroup} (D : Fuchsian.FuchsianDisc H) (hD : D.carrier=openHalfPlaneSet)
    (g : H) (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hA : realSLMobius A=g.val)
    (w : ℍ) (hmoved : g.val.val ((w : ℂ) : Mobius.ExtendedComplex)≠((w : ℂ) : Mobius.ExtendedComplex)) :
    {z : ℍ | ((z : ℂ) : Mobius.ExtendedComplex)∈Fuchsian.normalizedDirichletHalfPlane D.carrier D.isDisc g.val
      (D.image_eq g) ((w : ℂ) : Mobius.ExtendedComplex) hmoved}={z : ℍ | dist z w<dist z (A⁻¹ • w)}:=by
  have hw : A • w≠w:=by
    intro he
    apply hmoved
    rw [←hA,realSLMobius_action,he]
  have hwv : w≠A⁻¹ • w:=by
    intro he
    have hh:=congrArg (fun z : ℍ=>A • z) he
    rw [smul_inv_smul] at hh
    exact hw hh
  obtain ⟨L,M,hLM,hcar⟩:=exists_hNormalizedReflectionFactor_interior A w hw
  have hb : Mobius.geometricModelBoundary D.carrier D.isDisc=halfPlaneBoundaryCircle:=by
    apply Subtype.ext
    change frontier D.carrier=Mobius.complexRealAxis
    rw [hD,Fuchsian.nielsen_openHalfPlane_frontier,halfPlaneIdealBoundary_eq_realAxis]
  have hspec : Mobius.IsGeometricNormalizedReflectionFactor (Mobius.geometricModelBoundary D.carrier D.isDisc)
      g.val ((w : ℂ) : Mobius.ExtendedComplex) L.extendedCircle M.extendedCircle:=by
    rw [hb,←hA]
    exact (Mobius.isHNormalizedReflectionFactor_iff_geometric A _ L M).mp hLM
  have he:=Mobius.geometricNormalizedMirrors_eq_of_spec D.carrier D.isDisc g.val (D.image_eq g)
    ((w : ℂ) : Mobius.ExtendedComplex) hmoved L.extendedCircle M.extendedCircle hspec
  have hwL : w∉L.carrier:=by
    intro hwL
    apply hLM.first_mirror_avoids_center
    · intro he
      apply hw
      apply UpperHalfPlane.coe_injective
      apply OnePoint.coe_injective
      rw [realSLMobius_action] at he
      exact he
    · exact (L.mem_extendedCircle w).mpr hwL
  have hcut : {z : ℍ | ((z : ℂ) : Mobius.ExtendedComplex)∈Fuchsian.normalizedDirichletHalfPlane D.carrier D.isDisc g.val
      (D.image_eq g) ((w : ℂ) : Mobius.ExtendedComplex) hmoved}=openHHalfPlane L w:=by
    unfold Fuchsian.normalizedDirichletHalfPlane
    rw [←he]
    have hside:=halfPlaneLine_sphere_component_eq L w hwL
    ext z
    change ((((z : ℂ) : Mobius.ExtendedComplex)∈D.carrier) ∧
      ((z : ℂ) : Mobius.ExtendedComplex)∈connectedComponentIn L.extendedCircle.valᶜ ((w : ℂ) :
        Mobius.ExtendedComplex)) ↔ z∈openHHalfPlane L w
    rw [hD]
    have hz : ((z : ℂ) : Mobius.ExtendedComplex)∈openHalfPlaneSet:=Mobius.halfPlaneBoundaryPoint_mem z
    simp only [hz,true_and]
    exact Set.ext_iff.mp hside z
  obtain ⟨N,hN,hcloser⟩:=hyperbolic_closer_halfPlane hwv
  have hLN : L=N:=HalfPlaneLine.carrier_injective (hcar.trans hN.symm)
  rw [hLN] at hcut
  exact hcut.trans hcloser.symm

/-- The interior half-plane comparison uses the exact original subgroup action, with no supplied coordinate-action assumption. -/
theorem normalizedDirichletHalfPlane_interior_action_formula
    {H : Subgroup Mobius.complexMobiusGroup} (D : Fuchsian.FuchsianDisc H) (hD : D.carrier=openHalfPlaneSet)
    (g : H) (w : ℍ) (hmoved : g.val.val ((w : ℂ) : Mobius.ExtendedComplex)≠((w : ℂ) : Mobius.ExtendedComplex)) :
    letI :=(Fuchsian.HalfPlaneFuchsianGroup.ofFuchsianDisc D hD).nativeAction
    {z : ℍ | ((z : ℂ) : Mobius.ExtendedComplex)∈Fuchsian.normalizedDirichletHalfPlane D.carrier D.isDisc g.val
      (D.image_eq g) ((w : ℂ) : Mobius.ExtendedComplex) hmoved}={z : ℍ | dist z w<dist z (g⁻¹ • w)}:=by
  let P:=Fuchsian.HalfPlaneFuchsianGroup.ofFuchsianDisc D hD
  let :=P.nativeAction
  have hpres : g.val.val '' openHalfPlaneSet=openHalfPlaneSet:=by rw [←hD];exact D.image_eq g
  obtain ⟨A,hA⟩:=Fuchsian.mobius_preserves_halfPlane_exists_SL g.val hpres
  have hAi : realSLMobius A⁻¹=(g⁻¹).val:=by rw [map_inv,hA];rfl
  rw [P.nativeAction_realSL g⁻¹ A⁻¹ hAi]
  exact normalizedDirichletHalfPlane_interior_formula D hD g A hA w hmoved

/-- The original generalized polygon at an actual interior center is exactly the original metric Dirichlet intersection. -/
theorem generalizedDirichletPolygon_halfPlane_interior_eq_dirichlet
    {H : Subgroup Mobius.complexMobiusGroup} (D : Fuchsian.FuchsianDisc H) (hD : D.carrier=openHalfPlaneSet)
    (w : ℍ) (hfree : ∀g : H,g • ((w : ℂ) : Mobius.ExtendedComplex)=((w : ℂ) : Mobius.ExtendedComplex)→g=1) :
    letI :=(Fuchsian.HalfPlaneFuchsianGroup.ofFuchsianDisc D hD).nativeAction
    {z : ℍ | ((z : ℂ) : Mobius.ExtendedComplex)∈Fuchsian.generalizedDirichletPolygon D ((w : ℂ) :
      Mobius.ExtendedComplex) hfree}=
      {z : ℍ | ∀g : H,g≠1→dist z w<dist z (g • w)}:=by
  let P:=Fuchsian.HalfPlaneFuchsianGroup.ofFuchsianDisc D hD
  let :=P.nativeAction
  ext z
  constructor
  · intro hz g hg
    have hinv:=hz.2 g⁻¹ (inv_ne_one.mpr hg)
    have he:=normalizedDirichletHalfPlane_interior_action_formula D hD g⁻¹ w
      (Fuchsian.freeMobiusCenter_moved ((w : ℂ) : Mobius.ExtendedComplex) hfree g⁻¹ (inv_ne_one.mpr hg))
    have hm:=Set.ext_iff.mp he z
    simp only [inv_inv] at hm
    exact hm.mp hinv
  · intro hz
    have hzD : ((z : ℂ) : Mobius.ExtendedComplex)∈D.carrier:=by rw [hD];exact Mobius.halfPlaneBoundaryPoint_mem z
    refine ⟨hzD,?_⟩
    intro g hg
    have he:=normalizedDirichletHalfPlane_interior_action_formula D hD g w
      (Fuchsian.freeMobiusCenter_moved ((w : ℂ) : Mobius.ExtendedComplex) hfree g hg)
    exact (Set.ext_iff.mp he z).mpr (hz g⁻¹ (inv_ne_one.mpr hg))

/-- A convenient actual point on the vertical through a real circle center has exactly its stated Euclidean height. -/
theorem metricProbe_norm_sub_center (c y : ℝ) (hy : 0<y) :
    ‖(metricProbe c y hy : ℂ)-(c : ℂ)‖=y:=by
  have he : (metricProbe c y hy : ℂ)-(c : ℂ)=(y : ℂ)*Complex.I:=by
    apply Complex.ext <;> simp [metricProbe]
  rw [he,norm_mul,Complex.norm_I,mul_one,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hy]

/-- Each actual spherical side of every native mirror genuinely meets H, even if its chosen center is ideal or outside H. -/
theorem exists_halfPlane_point_in_mirror_side (L : HalfPlaneLine) (ξ : Mobius.ExtendedComplex)
    (hξ : ξ∉L.extendedCircle.val) :
    ∃w : ℍ,((w : ℂ) : Mobius.ExtendedComplex)∈connectedComponentIn L.extendedCircle.valᶜ ξ:=by
  cases L with
  | vertical x =>
    have hinf : ξ≠∞:=by intro he;subst ξ;exact hξ (Mobius.complexLine_infty 1 x)
    obtain ⟨z,rfl⟩:=OnePoint.ne_infty_iff_exists.mp hinf
    have hne : z.re≠x:=by
      intro he
      apply hξ
      change (z : Mobius.ExtendedComplex)∈Mobius.complexLine 1 x
      rw [Mobius.complexLine_coe]
      simpa only [Complex.inner,one_mul,Complex.conj_re] using he
    let w:=metricProbe z.re 1 (by norm_num)
    refine ⟨w,?_⟩
    change ((w : ℂ) : Mobius.ExtendedComplex)∈connectedComponentIn (Mobius.complexLine 1 x)ᶜ (z :
      Mobius.ExtendedComplex)
    rcases lt_or_gt_of_ne hne with hi|ho
    · rw [verticalCircle_component_left x _ ((mirrorLeftSide_coe x z).mpr hi)]
      exact (mirrorLeftSide_coe x w).mpr hi
    · rw [verticalCircle_component_right x _ ((mirrorRightSide_coe x z).mpr ho)]
      exact (mirrorRightSide_coe x w).mpr ho
  | circle c r hr =>
    induction ξ using OnePoint.rec with
    | infty =>
      let w:=metricProbe c (r+1) (by linarith)
      refine ⟨w,?_⟩
      apply (Fuchsian.mem_circle_complement_component_infty _ _ _ hr).mpr
      rw [metricProbe_norm_sub_center]
      linarith
    | coe z =>
      have hne : ‖z-(c : ℂ)‖≠r:=by
        intro he
        exact hξ ((Mobius.complexCircle_coe c z r).mpr he)
      rcases lt_or_gt_of_ne hne with hi|ho
      · let w:=metricProbe c (r/2) (by positivity)
        refine ⟨w,?_⟩
        apply (mem_circle_complement_component_inside _ _ _ _ hr hi).mpr
        rw [metricProbe_norm_sub_center]
        linarith
      · let w:=metricProbe c (r+1) (by linarith)
        refine ⟨w,?_⟩
        change ((w : ℂ) : Mobius.ExtendedComplex)∈connectedComponentIn (Mobius.complexCircle (c : ℂ) r)ᶜ (z :
          Mobius.ExtendedComplex)
        rw [circle_complement_component_outside_eq_infty _ _ _ hr ho]
        apply (Fuchsian.mem_circle_complement_component_infty _ _ _ hr).mpr
        rw [metricProbe_norm_sub_center]
        linarith

/-- Every spherical containing-side cut in H is a genuine native hyperbolic half-plane, for the entire center sphere. -/
theorem halfPlaneLine_sphere_side_isHalfPlane (L : HalfPlaneLine) (ξ : Mobius.ExtendedComplex)
    (hξ : ξ∉L.extendedCircle.val) :
    ∃w : ℍ,w∉L.carrier ∧
      {z : ℍ | ((z : ℂ) : Mobius.ExtendedComplex)∈connectedComponentIn L.extendedCircle.valᶜ ξ}=openHHalfPlane L w:=by
  obtain ⟨w,hw⟩:=exists_halfPlane_point_in_mirror_side L ξ hξ
  have hwN : w∉L.carrier:=by
    intro hwL
    exact connectedComponentIn_subset L.extendedCircle.valᶜ ξ hw ((L.mem_extendedCircle w).mpr hwL)
  refine ⟨w,hwN,?_⟩
  rw [connectedComponentIn_eq hw]
  exact halfPlaneLine_sphere_component_eq L w hwN

/-- Every true orthogonal-mirror cut in an arbitrary original model is carried to an actual native hyperbolic half-plane. -/
theorem geometricModel_side_halfPlane_normalization
    (P : Set Mobius.ExtendedComplex) (hP : Mobius.IsComplexOpenDisc P)
    (S : Mobius.ComplexGeneralizedCircle) (hS : Mobius.ComplexCirclesOrthogonal S (Mobius.geometricModelBoundary P hP))
    (ξ : Mobius.ExtendedComplex) (hξ : ξ∉S.val) :
    ∃q : Mobius.complexMobiusGroup,q.val '' P=openHalfPlaneSet ∧
      ∃(L : HalfPlaneLine) (w : ℍ),L.extendedCircle=S.image q ∧ w∉L.carrier ∧
        q.val '' (P∩Fuchsian.geometricContainingSide S ξ)=
          (fun z : ℍ=>((z : ℂ) : Mobius.ExtendedComplex)) '' openHHalfPlane L w:=by
  obtain ⟨q,hq⟩:=Fuchsian.IsComplexOpenDisc.halfPlane_normalizer hP
  have hb : (Mobius.geometricModelBoundary P hP).image q=halfPlaneBoundaryCircle:=by
    apply Subtype.ext
    change q.val '' frontier P=Mobius.complexRealAxis
    calc
      q.val '' frontier P=frontier (q.val '' P):=(Mobius.mobiusBoundaryHomeomorph q).image_frontier P
      _=Mobius.complexRealAxis:=by rw [hq,Fuchsian.nielsen_openHalfPlane_frontier,halfPlaneIdealBoundary_eq_realAxis]
  have hSq:=hS.image _ _ q
  rw [hb] at hSq
  obtain ⟨L,hL⟩:=exists_halfPlaneLine_of_orthogonal_boundary (S.image q) hSq
  have hξq : q.val ξ∉L.extendedCircle.val:=by
    intro he
    rw [hL] at he
    obtain ⟨η,hη,he⟩:=he
    exact hξ (q.val.injective he ▸ hη)
  obtain ⟨w,hw,hcut⟩:=halfPlaneLine_sphere_side_isHalfPlane L (q.val ξ) hξq
  refine ⟨q,hq,L,w,hL,hw,?_⟩
  rw [image_inter q.val.injective,hq,Fuchsian.geometricContainingSide_image S ξ hξ q,←hL]
  ext η
  constructor
  · rintro ⟨hηP,hηSide⟩
    obtain ⟨z,hz,rfl⟩:=hηP
    let u : ℍ:=⟨z,hz⟩
    exact ⟨u,(Set.ext_iff.mp hcut u).mp hηSide,rfl⟩
  · rintro ⟨z,hz,rfl⟩
    exact ⟨Mobius.halfPlaneBoundaryPoint_mem z,(Set.ext_iff.mp hcut z).mpr hz⟩

/-- All half-planes in the generalized Dirichlet construction are genuine hyperbolic half-planes, for every extended center. -/
theorem normalizedDirichletHalfPlane_is_actual_halfPlane
    (P : Set Mobius.ExtendedComplex) (hP : Mobius.IsComplexOpenDisc P)
    (g : Mobius.complexMobiusGroup) (hpres : g.val '' P=P)
    (ξ : Mobius.ExtendedComplex) (hmoved : g.val ξ≠ξ) :
    ∃q : Mobius.complexMobiusGroup,q.val '' P=openHalfPlaneSet ∧
      ∃(L : HalfPlaneLine) (w : ℍ),w∉L.carrier ∧
        q.val '' Fuchsian.normalizedDirichletHalfPlane P hP g hpres ξ hmoved=
          (fun z : ℍ=>((z : ℂ) : Mobius.ExtendedComplex)) '' openHHalfPlane L w:=by
  have hspec:=Mobius.geometricNormalizedMirrors_spec P hP g hpres ξ hmoved
  obtain ⟨q,hq,L,w,_hL,hw,he⟩:=geometricModel_side_halfPlane_normalization P hP _ hspec.1 ξ
    (Mobius.geometricNormalizedMirrors_first_avoids P hP g hpres ξ hmoved)
  exact ⟨q,hq,L,w,hw,he⟩

end
end LowDimensionalTopology.Geometry.Hyperbolic
