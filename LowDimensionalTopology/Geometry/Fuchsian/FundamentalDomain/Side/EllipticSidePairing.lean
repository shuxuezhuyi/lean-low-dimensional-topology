/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Mobius.Affine.Basic
public import LowDimensionalTopology.Geometry.Hyperbolic.Models.Disc.ExtendedCarrier
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.ZeroStabilizerRotations
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.Side.PolygonSidePairing
@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter MeasureTheory
open scoped Topology OnePoint Pointwise Complex.UnitDisc
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

theorem finiteMobiusRotationHom_injective : Function.Injective finiteMobiusRotationHom := by
  intro u v he
  have hu : Circle.toUnits u = Circle.toUnits v := _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusScaling_parameter_injective he
  apply Circle.coe_injective
  exact congrArg Units.val hu

theorem finiteMobiusRotation_order (n : ℕ) (hn : n ≠ 0) :
    orderOf (finiteMobiusRotationHom (_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationGenerator n)) = n := by
  rw [orderOf_injective finiteMobiusRotationHom finiteMobiusRotationHom_injective]
  exact (_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationGenerator_isPrimitiveRoot n hn).eq_orderOf.symm

theorem finiteMobiusRotation_elliptic (n : ℕ) (hn : 2 ≤ n) :
    _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic (finiteMobiusRotationHom (_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationGenerator n)) := by
  have horder := finiteMobiusRotation_order n (by omega)
  have hne : finiteMobiusRotationHom (_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationGenerator n) ≠ 1 := by
    intro he
    rw [he,orderOf_one] at horder
    omega
  have hpos : 0 < orderOf (finiteMobiusRotationHom (_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationGenerator n)) := by rw [horder];omega
  exact _root_.LowDimensionalTopology.Geometry.Mobius.mobius_finite_order_elliptic _ hne (orderOf_pos_iff.mp hpos)

/-- The actual normalized root acts by literal multiplication in the finite coordinate. -/
theorem UnitDiscFuchsianGroup.rotation_finite_action {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup G) (g : G) (u : Circle)
    (hg : g.val = finiteMobiusRotationHom u) (x : P.domain.carrier) :
    (P.finiteCoordinate (g • x) : ℂ) = (u:ℂ) * (P.finiteCoordinate x : ℂ) := by
  apply OnePoint.coe_injective
  have hc (y : P.domain.carrier) : ((((P.finiteCoordinate y : Complex.UnitDisc) : ℂ) :
    _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)) = y.val :=
    (_root_.LowDimensionalTopology.Geometry.Surfaces.discFiniteHomeomorph_symm_coe (P.finiteCoordinate y)).symm.trans
      (congrArg Subtype.val (P.finiteCoordinate.symm_apply_apply y))
  rw [hc]
  change g.val.val x.val = _
  rw [hg]
  change (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling (Circle.toUnits u)).val x.val = _
  rw [←hc x,_root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling_coe]
  rfl

/-- Finite native disc points have their genuine open ambient complex chart. -/
theorem ellipticSector_disc_coe_openEmbedding : Topology.IsOpenEmbedding (fun z : Complex.UnitDisc => (z : ℂ)) := by
  refine ⟨Complex.UnitDisc.isEmbedding_coe,?_⟩
  have hr : range (fun z : Complex.UnitDisc => (z : ℂ)) = Metric.ball 0 1 := by
    ext z
    constructor
    · rintro ⟨w,rfl⟩;simpa only [Metric.mem_ball,dist_zero_right] using w.norm_lt_one
    · intro hz
      exact ⟨Complex.UnitDisc.mk z (by simpa only [Metric.mem_ball,dist_zero_right] using hz),rfl⟩
  rw [hr]
  exact Metric.isOpen_ball

/-- A genuine point of a centered finite radial segment in the original disc model. -/
def ellipticRayPoint {G : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P :
  UnitDiscFuchsianGroup G)
    (u : Circle) (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1) : P.domain.carrier :=
  P.finiteCoordinate.symm (Complex.UnitDisc.mk ((r:ℂ)*(u:ℂ)) (by
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hr,Circle.norm_coe,mul_one]
    exact hr1))

theorem ellipticRayPoint_finite {G : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P :
  UnitDiscFuchsianGroup G)
    (u : Circle) (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1) :
    (P.finiteCoordinate (ellipticRayPoint P u r hr hr1) : ℂ) = (r:ℂ)*(u:ℂ) := by
  exact congrArg (fun z : Complex.UnitDisc => (z:ℂ)) (P.finiteCoordinate.apply_symm_apply _)

/-- The moving-center region contains all directions at every sufficiently small radius. -/
theorem stabilizerDirichletRegion_small_rays {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup G) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (u : Circle) (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1),
      r < ε → ellipticRayPoint P u r hr hr1 ∈
        stabilizerDirichletRegion P (P.finiteCoordinate.symm 0) := by
  let S := stabilizerDirichletRegion P (P.finiteCoordinate.symm 0)
  let U := (fun z : Complex.UnitDisc => (z:ℂ)) '' (P.finiteCoordinate '' S)
  have ho : IsOpen U := ellipticSector_disc_coe_openEmbedding.isOpenMap _
    (P.finiteCoordinate.isOpenMap _ (stabilizerDirichletRegion_isOpen P _))
  have h0 : (0:ℂ) ∈ U := by
    refine ⟨0,⟨P.finiteCoordinate.symm 0,stabilizerDirichletRegion_center_mem P _,
      P.finiteCoordinate.apply_symm_apply 0⟩,rfl⟩
  obtain ⟨ε,hε,hball⟩ := Metric.isOpen_iff.mp ho 0 h0
  refine ⟨ε,hε,?_⟩
  intro u r hr hr1 hrε
  have hn : ((r:ℂ)*(u:ℂ)) ∈ Metric.ball 0 ε := by
    rw [Metric.mem_ball,dist_zero_right,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg
      hr,Circle.norm_coe,mul_one]
    exact hrε
  obtain ⟨v,⟨x,hx,hxv⟩,hv⟩ := hball hn
  have he : x = ellipticRayPoint P u r hr hr1 := by
    apply P.finiteCoordinate.injective
    apply Complex.UnitDisc.coe_injective
    exact (congrArg (fun z : Complex.UnitDisc => (z:ℂ)) hxv).trans (hv.trans (ellipticRayPoint_finite P u r hr
      hr1).symm)
  rwa [←he]

/-- Both genuine sector boundary rays belong to the actual closed angular sector. -/
theorem ellipticRayPoint_mem_closure_sector {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup G) (n : ℕ) (hn : 0 < n)
    (u : Circle) (hu : u ∈ _root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationClosedArc n)
    (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1) :
    ellipticRayPoint P u r hr hr1 ∈ closure (P.finiteCoordinate ⁻¹' _root_.LowDimensionalTopology.Geometry.Hyperbolic.finiteRotationDiscSector n) := by
  rw [←P.finiteCoordinate.preimage_closure,finiteRotationDiscSector_closure n hn]
  change (P.finiteCoordinate (ellipticRayPoint P u r hr hr1) :
    ℂ) ∈ _root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationClosedPlaneSector n
  rw [ellipticRayPoint_finite]
  by_cases hr0 : r = 0
  · exact Or.inl (by rw [hr0,Complex.ofReal_zero,zero_mul])
  · exact _root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationClosedPlaneSector_radial n r (lt_of_le_of_ne hr
    (Ne.symm hr0)) u hu

/-- A boundary-ray point in the open common exterior belongs to the actual polygon closure. -/
theorem ellipticRayPoint_mem_closure_polygon {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup G) (n : ℕ) (hn : 0 < n)
    (u : Circle) (hu : u ∈ _root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationClosedArc n)
    (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1)
    (hS : ellipticRayPoint P u r hr hr1 ∈ stabilizerDirichletRegion P (P.finiteCoordinate.symm 0)) :
    ellipticRayPoint P u r hr hr1 ∈ closure
      ((P.finiteCoordinate ⁻¹' _root_.LowDimensionalTopology.Geometry.Hyperbolic.finiteRotationDiscSector n) ∩
        stabilizerDirichletRegion P (P.finiteCoordinate.symm 0)) := by
  have h := (stabilizerDirichletRegion_isOpen P (P.finiteCoordinate.symm 0)).inter_closure
    ⟨hS,ellipticRayPoint_mem_closure_sector P n hn u hu r hr hr1⟩
  simpa only [inter_comm] using h

/-- The actual primitive rotation has a positive-length common closed polygon side. -/
theorem ellipticRotation_closed_intersection_nontrivial {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup G) (n : ℕ) (hn : 2 ≤ n)
    (hG : finiteMobiusRotationHom (_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationGenerator n) ∈ G) :
    let D := (P.finiteCoordinate ⁻¹' _root_.LowDimensionalTopology.Geometry.Hyperbolic.finiteRotationDiscSector n) ∩
      stabilizerDirichletRegion P (P.finiteCoordinate.symm 0)
    (closure D ∩ ((⟨finiteMobiusRotationHom (_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationGenerator n),hG⟩ : G) • closure D)).Nontrivial := by
  let D := (P.finiteCoordinate ⁻¹' _root_.LowDimensionalTopology.Geometry.Hyperbolic.finiteRotationDiscSector n) ∩
    stabilizerDirichletRegion P (P.finiteCoordinate.symm 0)
  let g : G := ⟨finiteMobiusRotationHom (_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationGenerator n),hG⟩
  have hn0 : 0 < n := by omega
  have hOne : (1:Circle) ∈ _root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationClosedArc n :=
    ⟨0,⟨le_rfl,(_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationPeriod_pos n hn0).le⟩,Circle.exp_zero⟩
  have hGen : _root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationGenerator n ∈ _root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationClosedArc n :=
    ⟨_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationPeriod
      n,⟨(_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationPeriod_pos n hn0).le,le_rfl⟩,rfl⟩
  obtain ⟨ε,hε,hsmall⟩ := stabilizerDirichletRegion_small_rays P
  let r := min ε 1 / 2
  have hr : 0 < r := div_pos (lt_min hε zero_lt_one) (by norm_num)
  have hr1 : r < 1 := by have hh := min_le_right ε 1;dsimp [r];linarith
  have hrε : r < ε := by have hh := min_le_left ε 1;dsimp [r];linarith
  let z := ellipticRayPoint P 1 0 le_rfl zero_lt_one
  let p := ellipticRayPoint P 1 r hr.le hr1
  let q := ellipticRayPoint P (_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationGenerator n) r hr.le hr1
  have hzD : z ∈ closure D := ellipticRayPoint_mem_closure_polygon P n hn0 1 hOne 0 le_rfl zero_lt_one
    (hsmall 1 0 le_rfl zero_lt_one hε)
  have hpD : p ∈ closure D := ellipticRayPoint_mem_closure_polygon P n hn0 1 hOne r hr.le hr1
    (hsmall 1 r hr.le hr1 hrε)
  have hqD : q ∈ closure D := ellipticRayPoint_mem_closure_polygon P n hn0 (_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationGenerator n) hGen r hr.le hr1
    (hsmall (_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationGenerator n) r hr.le hr1 hrε)
  have hgz : g • z = z := by
    apply P.finiteCoordinate.injective
    apply Complex.UnitDisc.coe_injective
    rw [P.rotation_finite_action g (_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationGenerator n) rfl,
      ellipticRayPoint_finite,Complex.ofReal_zero,zero_mul,mul_zero]
  have hgp : g • p = q := by
    apply P.finiteCoordinate.injective
    apply Complex.UnitDisc.coe_injective
    rw [P.rotation_finite_action g (_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationGenerator n) rfl,
      ellipticRayPoint_finite,ellipticRayPoint_finite,Circle.coe_one,mul_one,mul_comm]
  have hzq : z ≠ q := by
    intro he
    have hh := congrArg (fun x => (P.finiteCoordinate x : ℂ)) he
    rw [ellipticRayPoint_finite,ellipticRayPoint_finite,Complex.ofReal_zero,zero_mul] at hh
    exact (mul_ne_zero (Complex.ofReal_ne_zero.mpr hr.ne')
      (_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationGenerator n).coe_ne_zero) hh.symm
  exact ⟨z,⟨hzD,⟨z,hzD,hgz⟩⟩,q,⟨hqD,⟨p,hpD,hgp⟩⟩,hzq⟩

/-- The normalized primitive elliptic genuinely pairs sides of an actual full-group polygon. -/
theorem primitive_elliptic_rotation_side_pairing {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup G) (n : ℕ) (hn : 2 ≤ n)
    (hprim : IsPrimitive G (finiteMobiusRotationHom
      (_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationGenerator n))) :
    let D := (P.finiteCoordinate ⁻¹' _root_.LowDimensionalTopology.Geometry.Hyperbolic.finiteRotationDiscSector n) ∩
      stabilizerDirichletRegion P (P.finiteCoordinate.symm 0)
    ∃ hD : IsConvexFuchsianPolygon P D, ∃ s : FuchsianPolygonSides P D,
      (fuchsianSideElement hD s).val = finiteMobiusRotationHom (_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationGenerator n) := by
  let f := finiteMobiusRotationHom (_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationGenerator n)
  let g : G := ⟨f,hprim.mem⟩
  have hf := finiteMobiusRotation_elliptic n hn
  have h0 : f.val (0:ℂ) = (0:ℂ) := _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusScaling_zero _
  have hP := primitive_elliptic_zero_polygon P f hf hprim h0
  rw [finiteMobiusRotation_order n (by omega)] at hP
  have hg : g ≠ 1 := by intro he;exact hf.1 (congrArg Subtype.val he)
  have hnon := ellipticRotation_closed_intersection_nontrivial P n hn hprim.mem
  let s : FuchsianPolygonSides P _ := ⟨_,hP.side_of_nontrivial_intersection hg hnon⟩
  refine ⟨hP,s,?_⟩
  have he := (hP.existsUnique_side_element s.property).choose_spec.2 g ⟨hg,rfl⟩
  exact congrArg (fun a : G => a.val) he.symm

/-- A literal primitive root is the actual least-angle elliptic rotation. -/
theorem finiteMobiusRotation_hasLeast (n : ℕ) (hn : 2 ≤ n) :
    HasLeastEllipticRotation (finiteMobiusRotationHom (_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationGenerator n)) := by
  let k := Circle.toUnits (_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationGenerator n)
  have hk : (k:ℂ) ≠ 1 := by
    intro he
    have hu : _root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationGenerator n = 1 := Circle.coe_injective he
    have ho := (_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationGenerator_isPrimitiveRoot n (by omega)).eq_orderOf
    rw [hu,orderOf_one] at ho
    omega
  refine ⟨n,by omega,k,?_,?_⟩
  · have he : finiteMobiusRotationHom (_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationGenerator
    n) = _root_.LowDimensionalTopology.Geometry.Mobius.mobiusStandardElement k :=
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusScaling_eq_standard k hk
    rw [he]
  · change Complex.exp (((_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationPeriod
    n:ℝ):ℂ)*Complex.I) = Complex.exp (2*Real.pi*Complex.I/n)
    congr 1
    simp only [_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationPeriod,Complex.ofReal_div,Complex.ofReal_mul,Complex.ofReal_natCast,Complex.ofReal_ofNat]
    ring

/-- Conjugate nonidentity actual scalings have equal or reciprocal literal multipliers. -/
theorem mobiusScaling_isConj_parameters (a b : ℂˣ) (ha : (a:ℂ) ≠ 1)
    (hconj : IsConj (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling a)
      (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusStandardElement b)) :
    a = b ∨ a = b⁻¹ := by
  obtain ⟨q,hq⟩ := isConj_iff.mp hconj
  have he : _root_.LowDimensionalTopology.Geometry.Mobius.mobiusSquaredTrace (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling a) = _root_.LowDimensionalTopology.Geometry.Mobius.mobiusSquaredTrace (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusStandardElement b) := by
    rw [←_root_.LowDimensionalTopology.Geometry.Mobius.mobiusSquaredTrace_conjugation
      (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling a) q,hq]
  rw [_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusScaling_eq_standard a ha,_root_.LowDimensionalTopology.Geometry.Mobius.mobiusStandardElement_squaredTrace,_root_.LowDimensionalTopology.Geometry.Mobius.mobiusStandardElement_squaredTrace] at he
  exact (_root_.LowDimensionalTopology.Geometry.Mobius.Classification.standardTrace_eq_iff a b).mp he

/-- In the genuine normalized disc, a least-angle elliptic is exactly the positive primitive root or its inverse. -/
theorem least_elliptic_fix_zero_rotation (f : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (hf :
  _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic f)
    (hp : f.val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc =
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc) (h0 : f.val (0:ℂ) = (0:ℂ))
    (hl : HasLeastEllipticRotation f) :
    2 ≤ orderOf f ∧
      (f = finiteMobiusRotationHom (_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationGenerator (orderOf
        f)) ∨
       f = (finiteMobiusRotationHom (_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationGenerator (orderOf f)))⁻¹) := by
  obtain ⟨a,_haNorm,ha⟩ := discPreserver_fix_zero_scaling f hp h0
  have ha0 : (a:ℂ) ≠ 1 := by
    intro he
    have hau : a = 1 := Units.ext he
    exact hf.1 (ha.trans (by rw [hau,_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusScaling_one]))
  obtain ⟨m,hm,k,hconj,hk⟩ := hl
  have hm0 : m ≠ 0 := by omega
  have hroot : IsPrimitiveRoot k m := IsPrimitiveRoot.coe_units_iff.mp
    (hk ▸ Complex.isPrimitiveRoot_exp m hm0)
  have hk0 : (k:ℂ) ≠ 1 := by
    intro he
    have hu : k = 1 := Units.ext he
    have ho := hroot.eq_orderOf
    rw [hu,orderOf_one] at ho
    omega
  have horder : orderOf f = m := by
    obtain ⟨q,hq⟩ := isConj_iff.mp hconj
    have he := (MulAut.conj q).orderOf_eq f
    change orderOf (q*f*q⁻¹) = orderOf f at he
    rw [hq,←_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusScaling_eq_standard k hk0] at he
    change orderOf (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusScalingHom k) = orderOf f at he
    rw [orderOf_injective _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusScalingHom
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusScaling_parameter_injective] at he
    exact he.symm.trans hroot.eq_orderOf.symm
  have hkRoot : k = Circle.toUnits (_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationGenerator m) := by
    apply Units.ext
    rw [hk]
    change Complex.exp (2*Real.pi*Complex.I/m) = Complex.exp (((_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationPeriod m:ℝ):ℂ)*Complex.I)
    congr 1
    simp only [_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationPeriod,Complex.ofReal_div,Complex.ofReal_mul,Complex.ofReal_natCast,Complex.ofReal_ofNat]
    ring
  refine ⟨by omega,?_⟩
  have hc : IsConj (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling
    a) (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusStandardElement k) := ha ▸ hconj
  rcases mobiusScaling_isConj_parameters a k ha0 hc with he | he
  · left
    rw [horder,ha,he,hkRoot]
    rfl
  · right
    rw [horder,ha,he,hkRoot]
    exact map_inv _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusScalingHom _

/-- Inverting the displayed primitive root preserves its full-stabilizer hypothesis. -/
theorem primitive_positive_root_of_inverse {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (n : ℕ) (hn : 2 ≤ n)
    (hp : IsPrimitive G (finiteMobiusRotationHom
      (_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationGenerator n))⁻¹) :
    IsPrimitive G (finiteMobiusRotationHom (_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationGenerator n)) := by
  let f := finiteMobiusRotationHom (_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationGenerator n)
  apply (primitive_iff_of_elliptic (finiteMobiusRotation_elliptic n hn)).mpr
  refine ⟨?_,?_,finiteMobiusRotation_hasLeast n hn⟩
  · have hmem : f⁻¹ ∈ G := hp.mem
    change f ∈ G
    simpa only [inv_inv] using G.inv_mem hmem
  · intro z hz
    have hi : f⁻¹.val z = z := by
      apply f.val.injective
      change f.val (f.val.symm z) = f.val z
      rw [f.val.apply_symm_apply,hz]
    have hh := hp.generates z hi
    simpa only [Subgroup.zpowers_inv] using hh

/-- Every genuine primitive elliptic fixing zero pairs sides, with no chosen signed orientation. -/
theorem primitive_elliptic_zero_side_pairing {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup G) (f : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hf : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic f) (hp : IsPrimitive G f) (h0 : f.val (0:ℂ) =
      (0:ℂ)) :
    ∃ D : Set P.domain.carrier, ∃ hD : IsConvexFuchsianPolygon P D,
      ∃ s : FuchsianPolygonSides P D, (fuchsianSideElement hD s).val = f := by
  have hl := ((primitive_iff_of_elliptic hf).mp hp).2.2
  obtain ⟨hn,hpos | hneg⟩ := least_elliptic_fix_zero_rotation f hf (P.image_eq ⟨f,hp.mem⟩) h0 hl
  · have hpR : IsPrimitive G (finiteMobiusRotationHom
    (_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationGenerator (orderOf f))) := hpos ▸ hp
    obtain ⟨hD,s,hs⟩ := primitive_elliptic_rotation_side_pairing P (orderOf f) hn hpR
    exact ⟨_,hD,s,hs.trans hpos.symm⟩
  · have hpI : IsPrimitive G (finiteMobiusRotationHom
    (_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationGenerator (orderOf f)))⁻¹ := hneg ▸ hp
    have hpR := primitive_positive_root_of_inverse (orderOf f) hn hpI
    obtain ⟨hD,s,hs⟩ := primitive_elliptic_rotation_side_pairing P (orderOf f) hn hpR
    refine ⟨_,hD,fuchsianPairedSide hD s,?_⟩
    rw [fuchsianSideElement_paired]
    change (fuchsianSideElement hD s).val⁻¹ = f
    rw [hs,←hneg]

end LowDimensionalTopology.Geometry.Fuchsian
