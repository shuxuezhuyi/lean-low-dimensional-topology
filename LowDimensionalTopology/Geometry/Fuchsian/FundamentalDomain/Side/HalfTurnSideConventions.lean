/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Mobius.Affine.Basic
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.FiniteRotationFundamentalDomains
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.Side.PolygonSelfPairedSides
public import LowDimensionalTopology.Geometry.Hyperbolic.Metric.PointLineFormulas
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Topology
open scoped Complex.UnitDisc OnePoint Pointwise
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Surfaces LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Inversive LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
local instance halfTurnSideBorelMeasurableSpace : MeasurableSpace _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex:=borel _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex
local instance halfTurnSideBorelSpace : BorelSpace _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex:=⟨rfl⟩

abbrev halfTurnSideData := finiteMobiusRotationData 2 (by norm_num)

def halfTurnSideDomain : Set halfTurnSideData.domain.carrier:=
  {x|0<(halfTurnSideData.finiteCoordinate x:ℂ).im}

def halfTurnSideDiameter : Set halfTurnSideData.domain.carrier:=
  {x|(halfTurnSideData.finiteCoordinate x:ℂ).im=0}

def halfTurnSideFlip : finiteMobiusRotationGroup 2:=
  ⟨finiteMobiusRotationHom (_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationGenerator
    2),Subgroup.mem_zpowers _⟩

theorem halfTurnSide_generator : _root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationGenerator 2=(-1:Circle) := by
  apply Circle.coe_injective
  have hp:_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationPeriod 2=Real.pi:=by norm_num [_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationPeriod]
  simp only [_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationGenerator,hp,Circle.coe_exp,Complex.exp_pi_mul_I,Circle.coe_neg,Circle.coe_one]

theorem halfTurnSideFlip_coe (z:ℂ) : halfTurnSideFlip.val.val z=(-z:ℂ) := by
  change (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling (Circle.toUnits
    (_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationGenerator 2))).val z=(_ : ℂ)
  rw [_root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling_coe,halfTurnSide_generator]
  simp

theorem halfTurnSideFlip_ne_one : halfTurnSideFlip≠1 := by
  intro he
  have h:=congrArg (fun g:finiteMobiusRotationGroup 2=>g.val.val (1:ℂ)) he
  rw [halfTurnSideFlip_coe] at h
  change ((-1:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)=(1:ℂ) at h
  have h':(-1:ℂ)=1:=OnePoint.coe_injective h
  norm_num at h'

theorem halfTurnSide_group_cases (g:finiteMobiusRotationGroup 2) : g=1 ∨g=halfTurnSideFlip := by
  obtain ⟨i,hi⟩:=finiteMobiusRotation_mem_fin 2 (by norm_num) g
  fin_cases i
  · left
    apply Subtype.ext
    change g.val=1
    simpa only [pow_zero,map_one] using hi
  · right
    apply Subtype.ext
    change g.val=finiteMobiusRotationHom (_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationGenerator 2)
    simpa only [pow_one] using hi

theorem halfTurnSideFlip_action (x:halfTurnSideData.domain.carrier) :
    (halfTurnSideData.finiteCoordinate (halfTurnSideFlip • x):ℂ)=
      -(halfTurnSideData.finiteCoordinate x:ℂ) := by
  have h:=finiteMobiusRotation_finite_action 2 (by norm_num) 1 x
  simpa only [halfTurnSideFlip,pow_one,halfTurnSide_generator,Circle.coe_neg,Circle.coe_one,neg_one_mul] using h

theorem halfTurnSide_plane_sector : _root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationPlaneSector 2={z:ℂ|0<z.im} := by
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.finiteRotationPlaneSector_eq_halfPlanes 2 (by norm_num)]
  have hp:_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationPeriod 2=Real.pi:=by norm_num [_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationPeriod]
  have he:(Circle.exp (-Real.pi):ℂ)=-1:=by
    rw [Circle.coe_exp,Complex.ofReal_neg,neg_mul,Complex.exp_neg,Complex.exp_pi_mul_I]
    norm_num
  simp only [hp,he,neg_one_mul,Complex.neg_im,neg_lt_zero,and_self]

theorem halfTurnSideDomain_eq_sector : halfTurnSideDomain=finiteMobiusRotationDomain 2 (by norm_num) := by
  rw [finiteMobiusRotationDomain,_root_.LowDimensionalTopology.Geometry.Hyperbolic.finiteRotationDiscSector,halfTurnSide_plane_sector]
  rfl

/-- The literal original upper half-disc is a genuine convex locally finite fundamental polygon. -/
theorem halfTurnSideDomain_polygon : IsConvexFuchsianPolygon halfTurnSideData halfTurnSideDomain := by
  rw [halfTurnSideDomain_eq_sector]
  exact finiteMobiusRotationDomain_polygon 2 (by norm_num)

theorem halfTurnSideDomain_closure :
    closure halfTurnSideDomain={x|(0:ℝ)≤(halfTurnSideData.finiteCoordinate x:ℂ).im} := by
  have he:_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationClosedPlaneSector 2={z:ℂ|0≤z.im}:=by
    rw [←_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationPlaneSector_closure 2 (by norm_num),halfTurnSide_plane_sector]
    change closure (Complex.im ⁻¹' Ioi 0)=Complex.im ⁻¹' Ici 0
    rw [←Complex.isOpenMap_im.preimage_closure_eq_closure_preimage Complex.continuous_im,closure_Ioi]
  rw [halfTurnSideDomain_eq_sector,finiteMobiusRotationDomain_closure,he]
  rfl

theorem halfTurnSideDomain_frontier : frontier halfTurnSideDomain=halfTurnSideDiameter := by
  rw [frontier,halfTurnSideDomain_closure,
    halfTurnSideDomain_polygon.locallyFinite.fundamental.isOpen.interior_eq]
  ext x
  change ((0≤(halfTurnSideData.finiteCoordinate x:ℂ).im) ∧
    ¬(0<(halfTurnSideData.finiteCoordinate x:ℂ).im))↔(halfTurnSideData.finiteCoordinate x:ℂ).im=0
  exact ⟨fun h=>le_antisymm (not_lt.mp h.2) h.1,fun h=>by rw [h];norm_num⟩

theorem halfTurnSideFlip_inv : halfTurnSideFlip⁻¹=halfTurnSideFlip := by
  rcases halfTurnSide_group_cases halfTurnSideFlip⁻¹ with h|h
  · exact (halfTurnSideFlip_ne_one (inv_eq_one.mp h)).elim
  · exact h

theorem halfTurnSideFlip_order : orderOf halfTurnSideFlip=2 := by
  apply orderOf_eq_prime
  · simpa only [pow_two,halfTurnSideFlip_inv] using mul_inv_cancel halfTurnSideFlip
  · exact halfTurnSideFlip_ne_one

theorem halfTurnSideDomain_flip_tile :
    fuchsianDomainTile halfTurnSideData halfTurnSideDomain halfTurnSideFlip=
      {x|(halfTurnSideData.finiteCoordinate x:ℂ).im≤0} := by
  change (halfTurnSideFlip • ·) '' closure halfTurnSideDomain=_
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩
    rw [halfTurnSideDomain_closure] at hy
    change (halfTurnSideData.finiteCoordinate (halfTurnSideFlip • y):ℂ).im≤0
    rw [halfTurnSideFlip_action,Complex.neg_im]
    exact neg_nonpos.mpr hy
  · intro hx
    refine ⟨halfTurnSideFlip • x,?_,?_⟩
    · rw [halfTurnSideDomain_closure]
      change 0≤(halfTurnSideData.finiteCoordinate (halfTurnSideFlip • x):ℂ).im
      rw [halfTurnSideFlip_action,Complex.neg_im]
      exact neg_nonneg.mpr hx
    · change halfTurnSideFlip •(halfTurnSideFlip • x)=x
      nth_rw 1 [←halfTurnSideFlip_inv]
      exact inv_smul_smul halfTurnSideFlip x

theorem halfTurnSideDomain_intersection :
    closure halfTurnSideDomain ∩fuchsianDomainTile halfTurnSideData halfTurnSideDomain halfTurnSideFlip=
      halfTurnSideDiameter := by
  rw [halfTurnSideDomain_closure,halfTurnSideDomain_flip_tile]
  ext x
  change (0≤(halfTurnSideData.finiteCoordinate x:ℂ).im ∧
    (halfTurnSideData.finiteCoordinate x:ℂ).im≤0)↔(halfTurnSideData.finiteCoordinate x:ℂ).im=0
  exact ⟨fun h=>le_antisymm h.2 h.1,fun h=>by rw [h];norm_num⟩

def halfTurnSideCenter : halfTurnSideData.domain.carrier:=halfTurnSideData.finiteCoordinate.symm 0

def halfTurnSideLeft : Set halfTurnSideData.domain.carrier:=
  {x|(halfTurnSideData.finiteCoordinate x:ℂ).im=0 ∧(halfTurnSideData.finiteCoordinate x:ℂ).re<0}

def halfTurnSideRight : Set halfTurnSideData.domain.carrier:=
  {x|(halfTurnSideData.finiteCoordinate x:ℂ).im=0 ∧0<(halfTurnSideData.finiteCoordinate x:ℂ).re}

theorem halfTurnSideDiameter_nontrivial : halfTurnSideDiameter.Nontrivial := by
  let b:Complex.UnitDisc:=Complex.UnitDisc.mk (1/2:ℂ) (by norm_num)
  refine ⟨halfTurnSideCenter,?_,halfTurnSideData.finiteCoordinate.symm b,?_,?_⟩
  · simp [halfTurnSideDiameter,halfTurnSideCenter]
  · change (halfTurnSideData.finiteCoordinate (halfTurnSideData.finiteCoordinate.symm b):ℂ).im=0
    rw [halfTurnSideData.finiteCoordinate.apply_symm_apply]
    change (1/2:ℂ).im=0
    norm_num
  · intro h
    have he:=congrArg (fun x=>(halfTurnSideData.finiteCoordinate x:ℂ)) h
    norm_num [halfTurnSideCenter,b] at he

/-- With the original closed-tile convention the example has exactly the whole open diameter as its unique side. -/
theorem halfTurnSide_side_iff (S:Set halfTurnSideData.domain.carrier) :
    IsFuchsianPolygonSide halfTurnSideData halfTurnSideDomain S ↔S=halfTurnSideDiameter := by
  constructor
  · rintro ⟨⟨g,hg,rfl⟩,_hseg,_hn⟩
    rcases halfTurnSide_group_cases g with he|he
    · exact (hg he).elim
    · rw [he,halfTurnSideDomain_intersection]
  · rintro rfl
    rw [←halfTurnSideDomain_intersection]
    apply halfTurnSideDomain_polygon.side_of_nontrivial_intersection halfTurnSideFlip_ne_one
    rw [halfTurnSideDomain_intersection]
    exact halfTurnSideDiameter_nontrivial

/-- There are no triple-intersection vertices in the original convention for this genuine two-element group. -/
theorem halfTurnSide_no_original_vertices (x:halfTurnSideData.domain.carrier) :
    ¬IsFuchsianPolygonVertex halfTurnSideData halfTurnSideDomain x := by
  rintro ⟨g,h,hg,hh,hgh,_hpoint⟩
  have hge:g=halfTurnSideFlip:=(halfTurnSide_group_cases g).resolve_left hg
  have hhe:h=halfTurnSideFlip:=(halfTurnSide_group_cases h).resolve_left hh
  exact hgh (hge.trans hhe.symm)

theorem halfTurnSide_fixed_iff_center (x:halfTurnSideData.domain.carrier) :
    halfTurnSideFlip • x=x ↔x=halfTurnSideCenter := by
  constructor
  · intro h
    have he:=congrArg (fun y=>(halfTurnSideData.finiteCoordinate y:ℂ)) h
    rw [halfTurnSideFlip_action] at he
    have hz:(halfTurnSideData.finiteCoordinate x:ℂ)=0:=by
      have hr:=congrArg Complex.re he
      have hi:=congrArg Complex.im he
      apply Complex.ext <;> simp only [Complex.neg_re,Complex.neg_im,Complex.zero_re,Complex.zero_im] at * <;> linarith
    apply halfTurnSideData.finiteCoordinate.injective
    apply Complex.UnitDisc.coe_injective
    simpa [halfTurnSideCenter] using hz
  · rintro rfl
    apply halfTurnSideData.finiteCoordinate.injective
    apply Complex.UnitDisc.coe_injective
    rw [halfTurnSideFlip_action]
    simp [halfTurnSideCenter]

/-- Deleting the actual order-two fixed point splits the literal original side into its two open half-diameters. -/
theorem halfTurnSide_split_cover :
    halfTurnSideDiameter\{halfTurnSideCenter}=halfTurnSideLeft ∪halfTurnSideRight := by
  ext x
  change (((halfTurnSideData.finiteCoordinate x:ℂ).im=0) ∧x∉({halfTurnSideCenter}:Set _))↔
    (((halfTurnSideData.finiteCoordinate x:ℂ).im=0 ∧(halfTurnSideData.finiteCoordinate x:ℂ).re<0) ∨
      ((halfTurnSideData.finiteCoordinate x:ℂ).im=0 ∧0<(halfTurnSideData.finiteCoordinate x:ℂ).re))
  constructor
  · rintro ⟨hi,hc⟩
    have hn:(halfTurnSideData.finiteCoordinate x:ℂ).re≠0:=by
      intro hr
      apply hc
      apply Set.mem_singleton_iff.mpr
      apply halfTurnSideData.finiteCoordinate.injective
      apply Complex.UnitDisc.coe_injective
      simp only [halfTurnSideCenter,Homeomorph.apply_symm_apply,Complex.UnitDisc.coe_zero]
      exact Complex.ext hr hi
    rcases lt_or_gt_of_ne hn with h|h
    · exact Or.inl ⟨hi,h⟩
    · exact Or.inr ⟨hi,h⟩
  · rintro (⟨hi,hr⟩|⟨hi,hr⟩)
    all_goals
      refine ⟨hi,?_⟩
      rintro (rfl : x=halfTurnSideCenter)
      simp [halfTurnSideCenter] at hr

/-- The two refined sides are genuinely disjoint and are interchanged by the original half-turn. -/
theorem halfTurnSide_split_pairing :
    Disjoint halfTurnSideLeft halfTurnSideRight ∧
      halfTurnSideFlip • halfTurnSideLeft=halfTurnSideRight := by
  refine ⟨Set.disjoint_left.mpr (fun x hx hy=>lt_asymm hx.2 hy.2),?_⟩
  change (halfTurnSideFlip • ·) '' halfTurnSideLeft=halfTurnSideRight
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩
    change (halfTurnSideData.finiteCoordinate (halfTurnSideFlip • y):ℂ).im=0 ∧
      0<(halfTurnSideData.finiteCoordinate (halfTurnSideFlip • y):ℂ).re
    rw [halfTurnSideFlip_action,Complex.neg_im,Complex.neg_re]
    exact ⟨by rw [hy.1];norm_num,neg_pos.mpr hy.2⟩
  · intro hx
    refine ⟨halfTurnSideFlip • x,?_,?_⟩
    · change (halfTurnSideData.finiteCoordinate (halfTurnSideFlip • x):ℂ).im=0 ∧
        (halfTurnSideData.finiteCoordinate (halfTurnSideFlip • x):ℂ).re<0
      rw [halfTurnSideFlip_action,Complex.neg_im,Complex.neg_re]
      exact ⟨by rw [hx.1];norm_num,neg_neg_of_pos hx.2⟩
    · change halfTurnSideFlip •(halfTurnSideFlip • x)=x
      nth_rw 1 [←halfTurnSideFlip_inv]
      exact inv_smul_smul halfTurnSideFlip x

/-- Each half-diameter is a true geodesic segment, with no appeal to the numerical side count. -/
theorem halfTurnSide_signed_half_geodesic (σ:ℝ) :
    IsFuchsianGeodesicSegment halfTurnSideData
      {x|(halfTurnSideData.finiteCoordinate x:ℂ).im=0 ∧
        0<σ*(halfTurnSideData.finiteCoordinate x:ℂ).re} := by
  have hsign (z:Complex.UnitDisc) :
      0 < inner ℝ (σ:ℂ) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate z) ↔0<σ*(z:ℂ).re:=by
    have hc:0<(2:ℝ)/(1+‖(z:ℂ)‖^2):=by positivity
    change 0 < inner ℝ (σ:ℂ) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinFormula z) ↔0<σ*(z:ℂ).re
    simp only [Complex.inner,_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinFormula,Complex.conj_ofReal,Complex.mul_re,Complex.mul_im,
      Complex.ofReal_re,Complex.ofReal_im,mul_zero,zero_mul,sub_zero,add_zero]
    rw [mul_assoc,mul_comm (z:ℂ).re σ]
    exact mul_pos_iff_of_pos_left hc
  have he:halfTurnSideData.finiteCoordinate ''
      {x|(halfTurnSideData.finiteCoordinate x:ℂ).im=0 ∧0<σ*(halfTurnSideData.finiteCoordinate x:ℂ).re}=
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realDiameterDiscLine.carrier ∩_root_.LowDimensionalTopology.Geometry.Hyperbolic.discKleinCutGt (σ:ℂ) 0:=by
    ext z
    constructor
    · rintro ⟨x,hx,rfl⟩
      exact ⟨by rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.realDiameterDiscLine_carrier];exact hx.1,(hsign _).mpr hx.2⟩
    · rintro ⟨hz,hs⟩
      refine ⟨halfTurnSideData.finiteCoordinate.symm z,?_,halfTurnSideData.finiteCoordinate.apply_symm_apply z⟩
      change (halfTurnSideData.finiteCoordinate (halfTurnSideData.finiteCoordinate.symm z):ℂ).im=0 ∧
        0<σ*(halfTurnSideData.finiteCoordinate (halfTurnSideData.finiteCoordinate.symm z):ℂ).re
      rw [halfTurnSideData.finiteCoordinate.apply_symm_apply]
      exact ⟨by rwa [_root_.LowDimensionalTopology.Geometry.Hyperbolic.realDiameterDiscLine_carrier] at hz,(hsign z).mp hs⟩
  refine ⟨?_,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realDiameterDiscLine,?_⟩
  · rw [he]
    intro a ha b hb y hy
    exact ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.realDiameterDiscLine.hConvex a ha.1 b hb.1 hy,
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.discKleinCutGt_hConvex (σ:ℂ) 0 a ha.2 b hb.2 hy⟩
  · rw [he]
    exact inter_subset_left

theorem halfTurnSide_split_geodesic :
    IsFuchsianGeodesicSegment halfTurnSideData halfTurnSideLeft ∧
      IsFuchsianGeodesicSegment halfTurnSideData halfTurnSideRight := by
  constructor
  · simpa only [halfTurnSideLeft,neg_one_mul,neg_pos] using halfTurnSide_signed_half_geodesic (-1)
  · simpa only [halfTurnSideRight,one_mul] using halfTurnSide_signed_half_geodesic 1

def halfTurnSideRealPoint (r:ℝ) (hr:|r|<1) : halfTurnSideData.domain.carrier:=
  halfTurnSideData.finiteCoordinate.symm (Complex.UnitDisc.mk (r:ℂ) (by simpa using hr))

theorem halfTurnSideRealPoint_coordinate (r:ℝ) (hr:|r|<1) :
    (halfTurnSideData.finiteCoordinate (halfTurnSideRealPoint r hr):ℂ)=(r:ℂ) := by
  simp [halfTurnSideRealPoint]

theorem halfTurnSide_split_nontrivial : halfTurnSideLeft.Nontrivial ∧halfTurnSideRight.Nontrivial := by
  constructor
  · refine ⟨halfTurnSideRealPoint (-1/2) (by norm_num),?_,halfTurnSideRealPoint (-1/4) (by norm_num),?_,?_⟩
    · change (halfTurnSideData.finiteCoordinate _:ℂ).im=0 ∧(halfTurnSideData.finiteCoordinate _:ℂ).re<0
      rw [halfTurnSideRealPoint_coordinate]
      norm_num
    · change (halfTurnSideData.finiteCoordinate _:ℂ).im=0 ∧(halfTurnSideData.finiteCoordinate _:ℂ).re<0
      rw [halfTurnSideRealPoint_coordinate]
      norm_num
    · intro he
      have h:=congrArg (fun x=>(halfTurnSideData.finiteCoordinate x:ℂ)) he
      rw [halfTurnSideRealPoint_coordinate,halfTurnSideRealPoint_coordinate] at h
      norm_num at h
  · refine ⟨halfTurnSideRealPoint (1/2) (by norm_num),?_,halfTurnSideRealPoint (1/4) (by norm_num),?_,?_⟩
    · change (halfTurnSideData.finiteCoordinate _:ℂ).im=0 ∧0<(halfTurnSideData.finiteCoordinate _:ℂ).re
      rw [halfTurnSideRealPoint_coordinate]
      norm_num
    · change (halfTurnSideData.finiteCoordinate _:ℂ).im=0 ∧0<(halfTurnSideData.finiteCoordinate _:ℂ).re
      rw [halfTurnSideRealPoint_coordinate]
      norm_num
    · intro he
      have h:=congrArg (fun x=>(halfTurnSideData.finiteCoordinate x:ℂ)) he
      rw [halfTurnSideRealPoint_coordinate,halfTurnSideRealPoint_coordinate] at h
      norm_num at h

theorem halfTurnSide_split_ne : halfTurnSideLeft≠halfTurnSideRight := by
  intro he
  obtain ⟨x,hx⟩:=halfTurnSide_split_nontrivial.1.nonempty
  have hy:x∈halfTurnSideRight:=he ▸ hx
  exact lt_asymm hx.2 hy.2

/-- The two actual conventions have respectively one and two sides, and respectively zero and one vertices. -/
theorem halfTurnSide_convention_counts :
    Nat.card {S:Set halfTurnSideData.domain.carrier|
      IsFuchsianPolygonSide halfTurnSideData halfTurnSideDomain S}=1 ∧
      (∀x,¬IsFuchsianPolygonVertex halfTurnSideData halfTurnSideDomain x) ∧
      Nat.card {S:Set halfTurnSideData.domain.carrier|S=halfTurnSideLeft ∨S=halfTurnSideRight}=2 ∧
      Nat.card {x:halfTurnSideData.domain.carrier|halfTurnSideFlip • x=x}=1 := by
  have hs:{S:Set halfTurnSideData.domain.carrier|
      IsFuchsianPolygonSide halfTurnSideData halfTurnSideDomain S}=({halfTurnSideDiameter}:Set _):=by
    ext S
    simp only [mem_ofPred,mem_singleton_iff,halfTurnSide_side_iff]
  have hv:{x:halfTurnSideData.domain.carrier|halfTurnSideFlip • x=x}=({halfTurnSideCenter}:Set _):=by
    ext x
    simp only [mem_ofPred,mem_singleton_iff,halfTurnSide_fixed_iff_center]
  have ht:{S:Set halfTurnSideData.domain.carrier|S=halfTurnSideLeft ∨S=halfTurnSideRight}=
      ({halfTurnSideLeft,halfTurnSideRight}:Set _):=by
    ext S
    simp only [mem_ofPred,mem_insert_iff,mem_singleton_iff]
  refine ⟨?_,halfTurnSide_no_original_vertices,?_,?_⟩
  · rw [hs]
    simp
  · rw [ht]
    change Set.ncard ({halfTurnSideLeft,halfTurnSideRight}:Set _)=2
    exact Set.ncard_pair halfTurnSide_split_ne
  · rw [hv]
    simp

/-- The original real diameter coordinate is exactly the open interval, retaining every actual point. -/
theorem halfTurnSide_real_coordinate_image (p:ℝ→Prop) :
    (fun x=>(halfTurnSideData.finiteCoordinate x:ℂ)) ''
      {x|(halfTurnSideData.finiteCoordinate x:ℂ).im=0 ∧p (halfTurnSideData.finiteCoordinate x:ℂ).re}=
      Complex.ofReal '' {r:ℝ|-1<r ∧r<1 ∧p r} := by
  ext z
  constructor
  · rintro ⟨x,hx,rfl⟩
    have hr:|(halfTurnSideData.finiteCoordinate x:ℂ).re|<1:=
      lt_of_le_of_lt (Complex.abs_re_le_norm _) (halfTurnSideData.finiteCoordinate x).norm_lt_one
    refine ⟨(halfTurnSideData.finiteCoordinate x:ℂ).re,⟨(abs_lt.mp hr).1,(abs_lt.mp hr).2,hx.2⟩,?_⟩
    exact Complex.ext rfl (by simpa using hx.1.symm)
  · rintro ⟨r,⟨h1,h2,hp⟩,rfl⟩
    let x:=halfTurnSideRealPoint r (abs_lt.mpr ⟨h1,h2⟩)
    refine ⟨x,?_,halfTurnSideRealPoint_coordinate r _⟩
    change (halfTurnSideData.finiteCoordinate x:ℂ).im=0 ∧p (halfTurnSideData.finiteCoordinate x:ℂ).re
    rw [halfTurnSideRealPoint_coordinate]
    exact ⟨rfl,hp⟩

/-- The side descriptions are literal real intervals (-1,1), (-1,0), and (0,1) in the original disc. -/
theorem halfTurnSide_interval_descriptions :
    (fun x=>(halfTurnSideData.finiteCoordinate x:ℂ)) '' halfTurnSideDiameter=Complex.ofReal '' Ioo (-1:ℝ) 1 ∧
      (fun x=>(halfTurnSideData.finiteCoordinate x:ℂ)) '' halfTurnSideLeft=Complex.ofReal '' Ioo (-1:ℝ) 0 ∧
      (fun x=>(halfTurnSideData.finiteCoordinate x:ℂ)) '' halfTurnSideRight=Complex.ofReal '' Ioo (0:ℝ) 1 := by
  have h0:=halfTurnSide_real_coordinate_image (fun _=>True)
  have hL:=halfTurnSide_real_coordinate_image (fun r=>r<0)
  have hR:=halfTurnSide_real_coordinate_image (fun r=>0<r)
  refine ⟨?_,?_,?_⟩
  · simpa only [and_true,halfTurnSideDiameter,Set.Ioo,Set.mem_ofPred_eq] using h0
  · have he:{r:ℝ|-1<r ∧r<1 ∧r<0}=Ioo (-1:ℝ) 0:=by
      ext r
      change (-1<r ∧r<1 ∧r<0)↔(-1<r ∧r<0)
      constructor
      · exact fun h=>⟨h.1,h.2.2⟩
      · exact fun h=>⟨h.1,by linarith [h.2],h.2⟩
    simpa only [he,halfTurnSideLeft] using hL
  · have he:{r:ℝ|-1<r ∧r<1 ∧0<r}=Ioo (0:ℝ) 1:=by
      ext r
      change (-1<r ∧r<1 ∧0<r)↔(0<r ∧r<1)
      constructor
      · exact fun h=>⟨h.2.2,h.2.1⟩
      · exact fun h=>⟨by linarith [h.1],h.2,h.1⟩
    simpa only [he,halfTurnSideRight] using hR

end LowDimensionalTopology.Geometry.Fuchsian
