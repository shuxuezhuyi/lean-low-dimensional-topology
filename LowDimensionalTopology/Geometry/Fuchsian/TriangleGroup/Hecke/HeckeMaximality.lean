/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Mobius.Circle.GeometricDisc
public import LowDimensionalTopology.Geometry.Hyperbolic.Models.Disc.ExtendedCarrier
public import LowDimensionalTopology.Geometry.Fuchsian.TriangleGroup.Hecke.HeckeSupergroupFord
public import LowDimensionalTopology.Geometry.Mobius.InvariantDisc.InvariantDiscConverse
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set
open scoped UpperHalfPlane OnePoint MatrixGroups Pointwise Topology
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
  LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- The actual two generating Hecke maps exclude an elementary original group for every source parameter. -/
theorem unitHeckeMobiusGroup_nonElementary (q : ℕ∞) (hq : 3≤q) :
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (unitHeckeMobiusGroup q hq) := by
  intro he
  obtain ⟨a,ha,hall⟩:=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.elementary_parabolic_common_fixedPoint
    (unitHeckeMobiusGroup q hq) he (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1)
    (unitHeckeMobiusGroup_translation_mem q hq)
    ((_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation_parabolic_iff 1).mpr one_ne_zero)
  have hai : (∞:Mobius.ExtendedComplex)=a := (ha ∞).mp (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation_infty 1)
  have hfix:=hall ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (unitHeckeInversionSL q hq),unitHeckeInversionSL_mem q hq⟩
  rw [←hai] at hfix
  have hc:=(_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_fixed_infty_iff (unitHeckeInversionSL q hq)).mp hfix
  rw [unitHeckeInversionSL_lowerLeft] at hc
  exact (hecke_width_pos q hq).ne' hc

/-- The actual extended unit disc is the interior of its own literal closure. -/
theorem hecke_unitDisc_interior_closure : interior (closure _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc)=_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc := by
  rw [_root_.LowDimensionalTopology.Geometry.Mobius.invariantDisc_closure_unitDisc]
  ext z
  cases z using OnePoint.rec with
  | infty =>
      constructor
      · intro h
        exact False.elim (by simpa [_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedClosedUnitDisc] using (interior_subset h))
      · exact fun h=>(_root_.LowDimensionalTopology.Geometry.Mobius.infty_not_mem_extendedUnitDisc h).elim
  | coe z =>
      have he : ((↑) : ℂ→Mobius.ExtendedComplex) ⁻¹' _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedClosedUnitDisc=Metric.closedBall 0 1 := by
        ext w
        simp only [mem_preimage, _root_.LowDimensionalTopology.Geometry.Hyperbolic.coe_mem_extendedClosedUnitDisc,
          Metric.mem_closedBall, dist_zero_right]
      have hi:=OnePoint.isOpenEmbedding_coe.isOpenMap.preimage_interior_eq_interior_preimage
        (OnePoint.continuous_coe : Continuous ((↑):ℂ→Mobius.ExtendedComplex)) _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedClosedUnitDisc
      have he' : ((↑) : ℂ→Mobius.ExtendedComplex) ⁻¹' interior _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedClosedUnitDisc=Metric.ball 0 1 := by
        rw [hi,he,interior_closedBall (0:ℂ) (by norm_num : (1:ℝ)≠0)]
      change z∈((↑):ℂ→Mobius.ExtendedComplex) ⁻¹' interior _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedClosedUnitDisc ↔ _
      rw [he']
      simp only [Metric.mem_ball, dist_zero_right,
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.coe_mem_extendedUnitDisc]

/-- Every genuine complex open disc is the actual interior of its closure. -/
theorem hecke_complexDisc_interior_closure
    {D : Set Mobius.ExtendedComplex}
    (hD : _root_.LowDimensionalTopology.Geometry.Mobius.IsComplexOpenDisc D) :
    interior (closure D)=D := by
  obtain ⟨q,hq⟩:=hD.normalize
  change (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusBoundaryHomeomorph q) '' D=_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc at hq
  apply (Set.image_injective.mpr q.val.injective)
  change (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusBoundaryHomeomorph q) '' interior (closure D)=
    (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusBoundaryHomeomorph q) '' D
  rw [Homeomorph.image_interior,Homeomorph.image_closure,hq,hecke_unitDisc_interior_closure]

/-- The genuine opposite complementary disc operation is involutive. -/
theorem hecke_complexDisc_exterior_involutive
    {D : Set Mobius.ExtendedComplex}
    (hD : _root_.LowDimensionalTopology.Geometry.Mobius.IsComplexOpenDisc D) :
    (closure (closure D)ᶜ)ᶜ=D := by
  rw [←interior_compl,compl_compl,hecke_complexDisc_interior_closure hD]

/-- Any original Fuchsian supergroup of an actual unit Hecke group preserves the source half-plane, without an added model assumption. -/
theorem unitHecke_supergroup_halfPlaneData (q : ℕ∞) (hq : 3≤q)
    (G : Subgroup Mobius.complexMobiusGroup)
    (hG : _root_.LowDimensionalTopology.Geometry.Surfaces.IsFuchsianGroup G)
    (hsub : unitHeckeMobiusGroup q hq≤G) : HalfPlaneFuchsianGroup G := by
  obtain ⟨D⟩:=(fuchsianDisc_exists_iff G).mpr hG
  let Q:=unitHeckeMobiusData q hq
  have hp : ∀f : unitHeckeMobiusGroup q hq,f.val.val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet=_root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet := Q.preserves
  have hD : ∀f : unitHeckeMobiusGroup q hq,f.val.val '' D.carrier=D.carrier :=
    fun f=>D.image_eq ⟨f.val,hsub f.property⟩
  have he:=_root_.LowDimensionalTopology.Geometry.Mobius.invariant_disc_eq_or_complement_closure (unitHeckeMobiusGroup q hq)
    (unitHeckeMobiusGroup_nonElementary q hq) _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet_isComplexOpenDisc D.isDisc hp hD
  refine ⟨?_,D.discrete⟩
  intro g
  rcases he with he|he
  · simpa only [he] using D.image_eq g
  · have hh:=_root_.LowDimensionalTopology.Geometry.Mobius.invariantComplexDisc_exterior G (fun f=>D.image_eq f) g
    rw [he,hecke_complexDisc_exterior_involutive _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet_isComplexOpenDisc] at hh
    exact hh

/-- Finite-parameter Hecke maximality for the original arbitrary Fuchsian supergroup, with no half-plane or primitive-stabilizer premise added. -/
theorem finiteHecke_fuchsian_supergroup_eq (n : ℕ) (hn : 3≤n)
    (G : Subgroup Mobius.complexMobiusGroup)
    (hG : _root_.LowDimensionalTopology.Geometry.Surfaces.IsFuchsianGroup G)
    (hsub : unitHeckeMobiusGroup n (by exact_mod_cast hn)≤G) :
    G=unitHeckeMobiusGroup n (by exact_mod_cast hn) :=
  finiteHecke_halfPlane_supergroup_eq n hn G
    (unitHecke_supergroup_halfPlaneData n (by exact_mod_cast hn) G hG hsub) hsub

/-- The finite maximality conclusion is invariant under actual global Mobius conjugation. -/
theorem finiteHecke_conjugate_fuchsian_supergroup_eq (n : ℕ) (hn : 3≤n)
    (H G : Subgroup Mobius.complexMobiusGroup)
    (hG : _root_.LowDimensionalTopology.Geometry.Surfaces.IsFuchsianGroup G)
    (hsub : H≤G)
    (q : Mobius.complexMobiusGroup)
    (hq : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q H=unitHeckeMobiusGroup n (by exact_mod_cast hn)) : G=H := by
  obtain ⟨D⟩:=(fuchsianDisc_exists_iff G).mpr hG
  have hCG : _root_.LowDimensionalTopology.Geometry.Surfaces.IsFuchsianGroup (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q G) :=
    (fuchsianDisc_exists_iff _).mp ⟨D.nielsenConjugate q⟩
  have hs : unitHeckeMobiusGroup n (by exact_mod_cast hn)≤_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q G := by
    rw [←hq]
    exact Subgroup.map_mono hsub
  have he:=finiteHecke_fuchsian_supergroup_eq n hn _ hCG hs
  have he' : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q G=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q H:=he.trans hq.symm
  exact (Subgroup.map_injective (MulAut.conj q).injective) he'

/-- An actual conformal conjugator intertwines the full original Mobius images of native groups. -/
theorem nativeConformal_range_conjugate_eq (K J : Subgroup (ℍ≃ᵢℍ))
    (hK : K≤_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneConformalIsometryGroup)
    (hJ : J≤_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneConformalIsometryGroup)
    (e : ℍ≃ᵢℍ) (he : e∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneConformalIsometryGroup)
    (hc : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate e K=J) :
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate (halfPlaneConformalMobiusHom ⟨e,he⟩)
      (nativeConformalSubgroupMobiusHom K hK).range=
      (nativeConformalSubgroupMobiusHom J hJ).range := by
  let q:=halfPlaneConformalMobiusHom ⟨e,he⟩
  ext f
  constructor
  · intro hf
    obtain ⟨k,hk,rfl⟩:=(_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff q _ f).mp hf
    obtain ⟨g,rfl⟩:=hk
    have hm : e*g.val*e⁻¹∈J := by
      rw [←hc]
      exact (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff e K _).mpr ⟨g.val,g.property,rfl⟩
    refine ⟨⟨e*g.val*e⁻¹,hm⟩,?_⟩
    change halfPlaneConformalMobiusHom ⟨e*g.val*e⁻¹,_⟩=
      halfPlaneConformalMobiusHom ⟨e,he⟩*halfPlaneConformalMobiusHom ⟨g.val,hK g.property⟩*
      (halfPlaneConformalMobiusHom ⟨e,he⟩)⁻¹
    rw [←map_inv,←map_mul,←map_mul]
    rfl
  · rintro ⟨j,rfl⟩
    have hj : j.val∈_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate e K := by rw [hc];exact j.property
    obtain ⟨g,hg,hgj⟩:=(_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff e K j.val).mp hj
    apply (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff q _ _).mpr
    refine ⟨nativeConformalSubgroupMobiusHom K hK ⟨g,hg⟩,⟨⟨g,hg⟩,rfl⟩,?_⟩
    change halfPlaneConformalMobiusHom ⟨e,he⟩*halfPlaneConformalMobiusHom ⟨g,hK hg⟩*
      (halfPlaneConformalMobiusHom ⟨e,he⟩)⁻¹=halfPlaneConformalMobiusHom ⟨j.val,hJ j.property⟩
    rw [←map_inv,←map_mul,←map_mul]
    apply congrArg halfPlaneConformalMobiusHom
    exact Subtype.ext hgj

/-- The original finite-order triangle definition supplies its genuine conformal subgroup. -/
theorem triangleOrders_conformal_le {K : Subgroup (ℍ≃ᵢℍ)} (n : ℕ)
    (hK : IsTriangleGroupOfOrders K 2 n ⊤) : K≤_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneConformalIsometryGroup := by
  obtain ⟨_,_,_,T,_,_,_,rfl⟩:=hK
  exact inf_le_right

/-- The original fixed finite signature constructs a conformal unit normalization preserving that same parameter. -/
theorem finite_triangle_conformal_conjugate_unit (K : Subgroup (ℍ≃ᵢℍ))
    (n : ℕ) (hn : 3≤n) (hK : IsTriangleGroupOfOrders K 2 n ⊤) :
    ∃e : ℍ≃ᵢℍ,e∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneConformalIsometryGroup ∧
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate e K=unitHeckeGroup n (by exact_mod_cast hn) := by
  obtain ⟨_,_,_,T,hα,hβ,hγ,rfl⟩:=hK
  have htwo : triangleOrderAngle 2=Real.pi/2 := by norm_num [triangleOrderAngle]
  rw [htwo] at hα
  rw [triangleOrderAngle_top] at hγ
  obtain ⟨e0,he0⟩:=equal_angle_triangle_conformalGroups_conjugate T
    (standardHeckeTriangle n (by exact_mod_cast hn))
    (hα.trans (standardHeckeTriangle_angles n (by exact_mod_cast hn)).1.symm)
    (hβ.trans (standardHeckeTriangle_angles n (by exact_mod_cast hn)).2.1.symm)
    (hγ.trans (standardHeckeTriangle_angles n (by exact_mod_cast hn)).2.2.symm)
  change _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate e0 (triangleConformalGroup T)=
    standardHeckeGroup n (by exact_mod_cast hn) at he0
  have he : ∃e : ℍ≃ᵢℍ,e∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneConformalIsometryGroup ∧
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate e (triangleConformalGroup T)=standardHeckeGroup n (by exact_mod_cast hn) := by
    rcases native_conformal_or_axis_mul_conformal e0 with hc|hc
    · exact ⟨e0,hc,he0⟩
    · refine ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionIsometry (.vertical 0)*e0,hc,?_⟩
      rw [←native_subgroupConjugate_compose,he0,standardHeckeGroup_axis_conjugate]
  obtain ⟨e,hconf,he⟩:=he
  refine ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (unitHeckeDilationSL n (by exact_mod_cast hn))*e,
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneConformalIsometryGroup.mul_mem ⟨unitHeckeDilationSL n (by exact_mod_cast hn),rfl⟩ hconf,?_⟩
  rw [←native_subgroupConjugate_compose,he]
  rfl

/-- A true global Mobius normalizer is constructed from the original fixed finite triangle signature. -/
theorem finite_triangle_mobius_normalizer (K : Subgroup (ℍ≃ᵢℍ))
    (n : ℕ) (hn : 3≤n) (hK : IsTriangleGroupOfOrders K 2 n ⊤) :
    ∃q : Mobius.complexMobiusGroup,_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q
      (nativeConformalSubgroupMobiusHom K (triangleOrders_conformal_le n hK)).range=
      unitHeckeMobiusGroup n (by exact_mod_cast hn) := by
  obtain ⟨e,he,hconj⟩:=finite_triangle_conformal_conjugate_unit K n hn hK
  exact ⟨halfPlaneConformalMobiusHom ⟨e,he⟩,
    nativeConformal_range_conjugate_eq K (unitHeckeGroup n (by exact_mod_cast hn))
      (triangleOrders_conformal_le n hK) (unitHeckeGroup_le_conformal n (by exact_mod_cast hn)) e he hconj⟩

/-- With its necessary finite-parameter correction, for the literal original triangle group and an arbitrary genuine Fuchsian supergroup. -/
theorem triangleGroup_two_order_cusp_isMaximal_fuchsian (K : Subgroup (ℍ≃ᵢℍ))
    (n : ℕ) (hn : 3≤n) (hK : IsTriangleGroupOfOrders K 2 n ⊤)
    (G : Subgroup Mobius.complexMobiusGroup)
    (hG : _root_.LowDimensionalTopology.Geometry.Surfaces.IsFuchsianGroup G)
    (hsub : (nativeConformalSubgroupMobiusHom K (triangleOrders_conformal_le n hK)).range≤G) :
    G=(nativeConformalSubgroupMobiusHom K (triangleOrders_conformal_le n hK)).range := by
  obtain ⟨q,hq⟩:=finite_triangle_mobius_normalizer K n hn hK
  exact finiteHecke_conjugate_fuchsian_supergroup_eq n hn _ G hG hsub q hq

/-- Actual global conjugation of the original whole groups composes in the usual order. -/
theorem hecke_mobius_subgroupConjugate_comp (q r : Mobius.complexMobiusGroup)
    (H : Subgroup Mobius.complexMobiusGroup) :
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate r H)=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate (q*r) H := by
  unfold _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate
  rw [Subgroup.map_map]
  congr 1

/-- The finite correction for every actual global Mobius image of an original finite Hecke triangle group. -/
theorem conjugate_triangleGroup_two_order_cusp_isMaximal_fuchsian (K : Subgroup (ℍ≃ᵢℍ))
    (n : ℕ) (hn : 3≤n) (hK : IsTriangleGroupOfOrders K 2 n ⊤)
    (r : Mobius.complexMobiusGroup)
    (G : Subgroup Mobius.complexMobiusGroup)
    (hG : _root_.LowDimensionalTopology.Geometry.Surfaces.IsFuchsianGroup G)
    (hsub : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate r
      (nativeConformalSubgroupMobiusHom K (triangleOrders_conformal_le n hK)).range≤G) :
    G=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate r
      (nativeConformalSubgroupMobiusHom K (triangleOrders_conformal_le n hK)).range := by
  obtain ⟨q,hq⟩:=finite_triangle_mobius_normalizer K n hn hK
  apply finiteHecke_conjugate_fuchsian_supergroup_eq n hn _ G hG hsub (q*r⁻¹)
  rw [hecke_mobius_subgroupConjugate_comp,show (q*r⁻¹)*r=q by group]
  exact hq

end LowDimensionalTopology.Geometry.Fuchsian
