/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Hyperbolic.Area.TriangleAreaIntegrals
public import LowDimensionalTopology.Geometry.Fuchsian.TriangleGroup.Hecke.UnitHeckeCuspStabilizer
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.Area
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory
open scoped UpperHalfPlane OnePoint MatrixGroups
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
local instance parabolicAreaSphereMeasurable : MeasurableSpace _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex:=borel _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex
local instance parabolicAreaSphereBorel : BorelSpace _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex:=⟨rfl⟩

/-- A literal positive-height part of a true vertical strip has its density-defined area. -/
theorem parabolic_vertical_strip_above_volume (a b c : ℝ) (hc : 0<c) :
    volume (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneAboveGraph (fun _=>c) (Ioo a b))=ENNReal.ofReal ((b-a)/c) := by
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneAboveGraph_volume _ _ measurable_const
    measurableSet_Ioo (fun _ _=>hc)]
  rw [lintegral_const,Measure.restrict_apply_univ,Real.volume_Ioo]
  rw [←ENNReal.ofReal_mul (one_div_nonneg.mpr hc.le)]
  congr 1
  ring

/-- The true upper-half-plane density gives every nonempty finite-width vertical strip infinite area. -/
theorem parabolic_vertical_strip_volume_top (a b : ℝ) (hab : a<b) :
    volume {z : ℍ | a<z.re ∧ z.re<b}=⊤ := by
  apply ENNReal.eq_top_of_forall_nnreal_le
  intro R
  let c:ℝ:=(b-a)/((R:ℝ)+1)
  have hc : 0<c:=div_pos (sub_pos.mpr hab) (by positivity)
  have he : (b-a)/c=(R:ℝ)+1 := by
    dsimp only [c]
    field_simp
  have hs : _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneAboveGraph (fun _=>c) (Ioo a b)⊆{z : ℍ | a<z.re ∧
    z.re<b} :=
    fun _ hz=>hz.1
  have hv : volume (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneAboveGraph (fun _=>c) (Ioo a b))≤
      volume {z : ℍ | a<z.re ∧ z.re<b}:=measure_mono hs
  rw [parabolic_vertical_strip_above_volume a b c hc,he] at hv
  apply le_trans _ hv
  rw [←ENNReal.ofReal_coe_nnreal]
  exact ENNReal.ofReal_le_ofReal (by linarith only [R.coe_nonneg])

/-- In an actual elementary group containing the unit parabolic, every original element fixes infinity. -/
theorem elementary_unitTranslation_fix_infty (H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hH : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsElementary H) (hT :
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1∈H) :
    ∀g : H,g.val.val (∞:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)=∞ := by
  obtain ⟨a,ha,hall⟩:=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.elementary_parabolic_common_fixedPoint H hH (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1) hT
    ((_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation_parabolic_iff 1).mpr one_ne_zero)
  have he : (∞:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)=a:=(ha (∞:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)).mp (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation_infty 1)
  simpa only [←he] using hall

/-- The actual elementary invariant-half-plane group containing a unit parabolic is genuinely cyclic. -/
theorem elementary_unitTranslation_isCyclic (H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (P : HalfPlaneFuchsianGroup H) (hH : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsElementary H) (hT :
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1∈H) :
    IsCyclic H := by
  have he : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusBoundaryStabilizer H (∞:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)=H := by
    ext f
    constructor
    · exact fun h=>((_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mem_mobiusBoundaryStabilizer H
      (∞:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) f).mp h).1
    · exact fun h=>(_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mem_mobiusBoundaryStabilizer H
      (∞:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) f).mpr
        ⟨h,elementary_unitTranslation_fix_infty H hH hT ⟨f,h⟩⟩
  rw [←he]
  exact P.asFuchsianDisc.stabilizer_isCyclic (∞:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)

/-- A genuine nonzero real-translation generator is constructed for the entire elementary normalized group. -/
theorem elementary_unitTranslation_generator (H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (P : HalfPlaneFuchsianGroup H) (hH : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsElementary H) (hT :
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1∈H) :
    ∃t : ℝ,t≠0 ∧ H=Subgroup.zpowers (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t)) := by
  obtain ⟨f,hf⟩:=(Subgroup.isCyclic_iff_exists_zpowers_eq_top H).mp
    (elementary_unitTranslation_isCyclic H P hH hT)
  have hfH : f∈H := by rw [←hf];exact Subgroup.mem_zpowers f
  obtain ⟨A,hA⟩:=mobius_preserves_halfPlane_exists_SL f (P.preserves ⟨f,hfH⟩)
  have hAH : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A∈H:=hA.symm ▸ hfH
  have hfix : (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A).val (∞:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)=∞ := by
    rw [hA]
    exact elementary_unitTranslation_fix_infty H hH hT ⟨f,hfH⟩
  obtain ⟨t,ht⟩:=primitive_affine_translation H P.discrete hT A hAH hfix
  have hproj : f=_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t):=hA.symm.trans ht
  have ht0 : t≠0 := by
    intro he
    subst t
    have h0 : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 0)=1 := by
      change _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (hTranslationSLHom 1)=1
      rw [map_one,map_one]
    rw [h0] at hproj
    have hm : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1∈Subgroup.zpowers f := by rw [hf];exact hT
    obtain ⟨k,hk⟩:=Subgroup.mem_zpowers_iff.mp hm
    rw [hproj,one_zpow] at hk
    exact ((_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation_eq_one_iff 1).not.mpr
      one_ne_zero) hk.symm
  exact ⟨t,ht0,by rw [←hf,hproj]⟩

/-- The literal closed finite-width strip has the expected true topological interior. -/
theorem parabolic_closedStrip_interior (t : ℝ) :
    interior {z : ℍ | 0≤z.re ∧ z.re≤t}={z : ℍ | 0<z.re ∧ z.re<t} := by
  change interior (UpperHalfPlane.re ⁻¹' Icc 0 t)=UpperHalfPlane.re ⁻¹' Ioo 0 t
  rw [←UpperHalfPlane.isOpenMap_re.preimage_interior_eq_interior_preimage UpperHalfPlane.continuous_re,
    interior_Icc]

/-- The literal closed strip is genuinely hyperbolically convex. -/
theorem parabolic_closedStrip_hConvex (t : ℝ) : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HConvex {z : ℍ | 0≤z.re ∧ z.re≤t} := by
  intro x hx y hy z hz
  exact ⟨parabolicFord_hConvex_re_ge 0 x hx.1 y hy.1 hz,
    parabolicFord_hConvex_re_le t x hx.2 y hy.2 hz⟩

/-- The actual open vertical strip has the literal closed strip as its closure. -/
theorem parabolic_openStrip_closure (t : ℝ) (ht : 0<t) :
    closure {z : ℍ | 0<z.re ∧ z.re<t}={z : ℍ | 0≤z.re ∧ z.re≤t} := by
  rw [←parabolic_closedStrip_interior]
  apply parabolicFord_closure_interior_of_hConvex
  · exact parabolic_closedStrip_hConvex t
  · exact (isClosed_le continuous_const UpperHalfPlane.continuous_re).inter
      (isClosed_le UpperHalfPlane.continuous_re continuous_const)
  · rw [parabolic_closedStrip_interior]
    refine ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe (t/2) 1 (by norm_num),?_⟩
    change 0<t/2 ∧ t/2<t
    constructor <;> linarith only [ht]

/-- Every actual orbit of a genuine translation group meets the literal closed period strip. -/
theorem parabolic_translation_strip_cover (H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (P : HalfPlaneFuchsianGroup H) (t : ℝ) (ht : 0<t)
    (hH : H=Subgroup.zpowers (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t))) :
    letI:=P.nativeAction
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.MeetsEveryOrbit H ℍ {z : ℍ | 0≤z.re ∧ z.re≤t} := by
  let parabolicOriginalNativeAction:=P.nativeAction
  intro z
  let k:ℤ:= -Int.floor (z.re/t)
  let A:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL ((k:ℝ)*t)
  have hproj : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A=(_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t))^k := by
    rw [←map_zpow,hTranslationSL_zpow]
  have hA : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A∈H := by
    rw [hH,hproj]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) _
  refine ⟨⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,hA⟩,?_⟩
  rw [P.nativeAction_realSL _ A rfl]
  have hre : (A•z).re=z.re-(Int.floor (z.re/t):ℝ)*t := by
    change ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL ((k:ℝ)*t)•z:ℍ):ℂ).re=_
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL_coe]
    simp only [Complex.add_re,UpperHalfPlane.coe_re,Complex.ofReal_re]
    dsimp only [k]
    push_cast
    ring
  change 0≤(A•z).re ∧ (A•z).re≤t
  rw [hre]
  have hlo : (Int.floor (z.re/t):ℝ)*t≤z.re := (le_div_iff₀ ht).mp (Int.floor_le _)
  have hhi : z.re<((Int.floor (z.re/t):ℝ)+1)*t := (div_lt_iff₀ ht).mp (Int.lt_floor_add_one _)
  constructor <;> linarith only [hlo,hhi]

/-- Distinct literal open-strip points cannot lie in the same orbit of the original period group. -/
theorem parabolic_translation_strip_orbit_unique (H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (P : HalfPlaneFuchsianGroup H) (t : ℝ) (ht : 0<t)
    (hH : H=Subgroup.zpowers (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t)))
    (x y : ℍ) (hx : 0<x.re ∧ x.re<t) (hy : 0<y.re ∧ y.re<t) :
    letI:=P.nativeAction
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitProjection H ℍ x=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitProjection H ℍ y → x=y := by
  let parabolicOriginalNativeAction:=P.nativeAction
  intro hxy
  obtain ⟨g,hgy⟩:=(Quotient.exact hxy : MulAction.orbitRel H ℍ x y)
  change g•y=x at hgy
  have hg : g.val∈Subgroup.zpowers (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t)):=hH ▸ g.property
  obtain ⟨k,hk⟩:=Subgroup.mem_zpowers_iff.mp hg
  have hA : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL ((k:ℝ)*t))=g.val := by
    rw [←hTranslationSL_zpow,map_zpow]
    exact hk
  have hshift : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL ((k:ℝ)*t)•y=x := by
    rwa [←P.nativeAction_realSL g _ hA y]
  have hre : x.re=y.re+(k:ℝ)*t := by
    rw [←hshift]
    change ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL ((k:ℝ)*t)•y:ℍ):ℂ).re=_
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL_coe]
    simp only [Complex.add_re,UpperHalfPlane.coe_re,Complex.ofReal_re]
  have hklo : (-1:ℝ)<k := (mul_lt_mul_iff_of_pos_right ht).mp (by linarith only [hre,hx.1,hy.2])
  have hkhi : (k:ℝ)<1 := (mul_lt_mul_iff_of_pos_right ht).mp (by linarith only [hre,hx.2,hy.1])
  have hk0 : k=0 := by
    have hl : (-1:ℤ)<k:=by exact_mod_cast hklo
    have hh : k<1:=by exact_mod_cast hkhi
    omega
  have hg1 : g=1 := by
    apply Subtype.ext
    rw [←hk,hk0,zpow_zero]
    rfl
  simpa only [hg1,one_smul] using hgy.symm

/-- A literal period strip is a genuine fundamental domain for the whole original translation group. -/
theorem parabolic_translation_strip_fundamental (H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (P : HalfPlaneFuchsianGroup H) (t : ℝ) (ht : 0<t)
    (hH : H=Subgroup.zpowers (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t))) :
    letI:=P.nativeAction
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain H ℍ volume {z : ℍ | 0<z.re ∧ z.re<t} := by
  let parabolicOriginalNativeAction:=P.nativeAction
  have hc : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HConvex {z : ℍ | 0<z.re ∧ z.re<t} := by
    rw [←parabolic_closedStrip_interior]
    exact (parabolic_closedStrip_hConvex t).interior
  have hn : ({z : ℍ | 0<z.re ∧ z.re<t}).Nonempty := by
    refine ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe (t/2) 1 (by norm_num),?_⟩
    change 0<t/2 ∧ t/2<t
    constructor <;> linarith only [ht]
  refine ⟨(isOpen_lt continuous_const UpperHalfPlane.continuous_re).inter
    (isOpen_lt UpperHalfPlane.continuous_re continuous_const),⟨hn,hc.isPreconnected⟩,?_,
    parabolicFord_hConvex_frontier_volume_zero hc⟩
  apply exists_fundamentalSet_between _ _ subset_closure
  · rw [parabolic_openStrip_closure t ht]
    exact parabolic_translation_strip_cover H P t ht hH
  · exact fun x hx y hy hxy=>parabolic_translation_strip_orbit_unique H P t ht hH x y hx hy hxy

/-- Every genuine native fundamental domain for the same original group has the same actual hyperbolic area. -/
theorem parabolic_nativeFundamentalDomain_area_eq (H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (P : HalfPlaneFuchsianGroup H) {D E : Set ℍ} :
    letI:=P.nativeAction
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain H ℍ volume D → _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain H ℍ volume E → volume D=volume E := by
  let parabolicOriginalNativeAction:=P.nativeAction
  intro hD hE
  have hD':=P.cayley_fundamental hD
  have hE':=P.cayley_fundamental hE
  have he:=fuchsianFundamentalDomain_area_eq hD' hE'
  have hm (S : Set ℍ) (hS : IsOpen S) : P.cayleyData.area (P.cayleyCoordinate '' S)=volume S := by
    rw [←P.cayleyCoordinate_area_map,Measure.map_apply P.cayleyCoordinate.continuous.measurable
      (P.cayleyCoordinate.isOpenMap S hS).measurableSet,Set.preimage_image_eq _ P.cayleyCoordinate.injective]
  rw [hm D hD.isOpen,hm E hE.isOpen] at he
  exact he

/-- Every true fundamental domain of the actual nonzero period group has infinite density area. -/
theorem parabolic_translation_fundamental_area_top (H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (P : HalfPlaneFuchsianGroup H) (t : ℝ) (ht : 0<t)
    (hH : H=Subgroup.zpowers (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t))) (D : Set ℍ) :
    letI:=P.nativeAction
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain H ℍ volume D → volume D=⊤ := by
  let parabolicOriginalNativeAction:=P.nativeAction
  intro hD
  rw [parabolic_nativeFundamentalDomain_area_eq H P hD (parabolic_translation_strip_fundamental H P t ht hH)]
  exact parabolic_vertical_strip_volume_top 0 t ht

/-- An actual elementary group containing a unit parabolic has infinite area in every genuine fundamental domain. -/
theorem elementary_unitTranslation_fundamental_area_top (H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (P : HalfPlaneFuchsianGroup H) (hH : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsElementary H) (hT :
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1∈H)
    (D : Set ℍ) :
    letI:=P.nativeAction
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain H ℍ volume D → volume D=⊤ := by
  let parabolicOriginalNativeAction:=P.nativeAction
  intro hD
  obtain ⟨t,ht,hgen⟩:=elementary_unitTranslation_generator H P hH hT
  rcases lt_or_gt_of_ne ht with hn|hp
  · have hgen' : H=Subgroup.zpowers (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL (-t))) := by
      rw [primitive_translation_neg,Subgroup.zpowers_inv]
      exact hgen
    exact parabolic_translation_fundamental_area_top H P (-t) (neg_pos.mpr hn) hgen' D hD
  · exact parabolic_translation_fundamental_area_top H P t hp hgen D hD

/-- Finite genuine quotient area forces a normalized original group containing a unit parabolic to be non-elementary. -/
theorem unitTranslation_finite_area_nonElementary (H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (P : HalfPlaneFuchsianGroup H) (hT : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1∈H) (D
      : Set ℍ) :
    letI:=P.nativeAction
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain H ℍ volume D → volume D≠⊤ → _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary H := by
  let parabolicOriginalNativeAction:=P.nativeAction
  intro hD hfinite he
  exact hfinite (elementary_unitTranslation_fundamental_area_top H P he hT D hD)

end LowDimensionalTopology.Geometry.Fuchsian
