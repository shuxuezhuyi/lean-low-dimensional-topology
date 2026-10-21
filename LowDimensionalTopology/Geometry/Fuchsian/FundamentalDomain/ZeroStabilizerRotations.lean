/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Mobius.Affine.Basic
public import LowDimensionalTopology.Geometry.Mobius.Circle.GeometricDisc
public import LowDimensionalTopology.Geometry.Hyperbolic.Models.Disc.ExtendedCarrier
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.FiniteRotationFundamentalDomains
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.NativeFuchsianPolygons
public import LowDimensionalTopology.Geometry.Fuchsian.CanonicalRegion.PrimitiveEllipticAngles
@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set MeasureTheory
open scoped Topology OnePoint ComplexConjugate
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
local instance zeroStabilizerSphereMeasurable : MeasurableSpace Mobius.ExtendedComplex := borel Mobius.ExtendedComplex
local instance zeroStabilizerSphereBorel : BorelSpace Mobius.ExtendedComplex := ⟨rfl⟩

/-- A genuine disc-preserving Mobius map fixing zero also fixes its inverse point infinity. -/
theorem discPreserver_fix_zero_infty (f : Mobius.complexMobiusGroup)
    (hp : f.val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc = _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc)
    (h0 : f.val (0:ℂ) = (0:ℂ)) : f.val ∞ = ∞ := by
  obtain ⟨a,c,hd,hf⟩ := _root_.LowDimensionalTopology.Geometry.Hyperbolic.complexMobius_disc_normal_form f hp
  have he : _root_.LowDimensionalTopology.Geometry.Auxiliary.Analysis.discFractionalMap a c 0 = 0 := by
    have hh := h0
    rw [hf,_root_.LowDimensionalTopology.Geometry.Hyperbolic.normalizedDiscTransformation_of_closedDisc a c 0 hd (by norm_num)] at hh
    exact OnePoint.coe_injective hh
  have he' : conj c / conj a = 0 := by
    simpa only [_root_.LowDimensionalTopology.Geometry.Auxiliary.Analysis.discFractionalMap,
      _root_.LowDimensionalTopology.Geometry.Auxiliary.Analysis.fractionalLinearMap, mul_zero, zero_add] using he
  have ha : a ≠ 0 := by
    intro h
    rw [h,Complex.normSq_zero] at hd
    nlinarith [Complex.normSq_nonneg c]
  have hc : c = 0 := by
    have hconj : conj c = 0 := (div_eq_zero_iff.mp he').resolve_right (by intro hh;exact ha ((map_eq_zero _).mp hh))
    exact (map_eq_zero _).mp hconj
  rw [hf,_root_.LowDimensionalTopology.Geometry.Hyperbolic.normalizedDiscTransformation_infty,hc]
  simp only [ite_true]

/-- The entire normalized point stabilizer consists of actual unit rotations. -/
theorem discPreserver_fix_zero_scaling (f : Mobius.complexMobiusGroup)
    (hp : f.val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc = _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc)
    (h0 : f.val (0:ℂ) = (0:ℂ)) :
    ∃u : ℂˣ, ‖(u:ℂ)‖ = 1 ∧ f = _root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling u := by
  obtain ⟨u,hu⟩ := _root_.LowDimensionalTopology.Geometry.Mobius.mobius_fix_zero_infty_eq_scaling f h0 (discPreserver_fix_zero_infty f hp h0)
  obtain ⟨z,hz,he⟩ := _root_.LowDimensionalTopology.Geometry.Hyperbolic.disc_preserver_maps_circle (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusBoundaryHomeomorph f) hp (by norm_num : ‖(1:ℂ)‖ = 1)
  change f.val ((1:ℂ):Mobius.ExtendedComplex) = (z:Mobius.ExtendedComplex) at he
  rw [hu,_root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling_coe,mul_one] at he
  have hez := OnePoint.coe_injective he
  exact ⟨u,hez ▸ hz,hu⟩

/-- A finite normalized full point stabilizer is the entire root-of-unity rotation subgroup of its order. -/
theorem finiteZeroDiscGroup_eq_rotation
    (H : Subgroup Mobius.complexMobiusGroup) [Finite H]
    (hp : ∀ f ∈ H, f.val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc = _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc)
    (h0 : ∀ f ∈ H, f.val (0:ℂ) = (0:ℂ)) :
    H = finiteMobiusRotationGroup (Nat.card H) := by
  let N := Nat.card H
  have hN : N ≠ 0 := Nat.card_pos.ne'
  let finiteZeroRootNeZero : NeZero N := ⟨hN⟩
  have hi : H ≤ _root_.LowDimensionalTopology.Geometry.Mobius.mobiusInftyStabilizer := by
    intro f hf
    exact discPreserver_fix_zero_infty f (hp f hf) (h0 f hf)
  let φ := _root_.LowDimensionalTopology.Geometry.Mobius.subgroupMultiplierHom H hi
  have hφ : Function.Injective φ := _root_.LowDimensionalTopology.Geometry.DiscreteGroups.subgroupMultiplierHom_injective_of_fix_zero H hi h0
  let e := MonoidHom.ofInjective hφ
  let finiteZeroMultiplierRange : Finite φ.range := Finite.of_surjective e e.surjective
  have hc : Nat.card φ.range = N := (Nat.card_congr e.toEquiv).symm
  let c := Circle.toUnits (_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationGenerator N)
  have hto : Function.Injective Circle.toUnits := by
    intro a b he
    apply Circle.coe_injective
    exact congrArg Units.val he
  have hr : IsPrimitiveRoot c N :=
    (_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationGenerator_isPrimitiveRoot N hN).map_of_injective hto
  have hR : φ.range = Subgroup.zpowers c := by
    rw [hr.zpowers_eq,primitive_finite_complexUnits_eq_rootsOfUnity φ.range,hc]
  apply le_antisymm
  · intro f hf
    let g : H := ⟨f,hf⟩
    have hmem : φ g ∈ Subgroup.zpowers c := by
      rw [←hR]
      exact ⟨g,rfl⟩
    obtain ⟨k,hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have he := _root_.LowDimensionalTopology.Geometry.DiscreteGroups.dilation_multiplier_representation H hi h0 g
    change f = _root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling (φ g) at he
    rw [he,←hk]
    change _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusScalingHom (c ^ k) ∈ finiteMobiusRotationGroup N
    rw [map_zpow]
    exact (finiteMobiusRotationGroup N).zpow_mem (Subgroup.mem_zpowers _) k
  · apply Subgroup.zpowers_le.mpr
    have hmem : c ∈ φ.range := by rw [hR];exact Subgroup.mem_zpowers c
    obtain ⟨g,hg⟩ := hmem
    change _root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling c ∈ H
    rw [←hg,←_root_.LowDimensionalTopology.Geometry.DiscreteGroups.dilation_multiplier_representation H hi h0 g]
    exact g.property

/-- Discreteness makes a genuine disc stabilizer at zero finite, without a non-elementarity assumption. -/
theorem discreteZeroDiscGroup_finite (H : Subgroup Mobius.complexMobiusGroup)
    (hd : _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup H)
    (hp : ∀ f ∈ H, f.val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc = _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc)
    (h0 : ∀ f ∈ H, f.val (0:ℂ) = (0:ℂ)) : Finite H := by
  apply _root_.LowDimensionalTopology.Geometry.DiscreteGroups.discreteMobius_finite_of_common_H3_fixed H hd _root_.LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ
  intro f hf
  obtain ⟨u,hu,rfl⟩ := discPreserver_fix_zero_scaling f (hp f hf) (h0 f hf)
  change _root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling u • _root_.LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace.upperHalfSpacePoint 0 1 zero_lt_one = _
  rw [_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusScaling_axis_smul]
  simp only [hu,one_mul]
  rfl

/-- The original point stabilizer and the actual Mobius fixed-point subgroup agree, with their original actions. -/
def UnitDiscFuchsianGroup.stabilizerEquiv
    {G : Subgroup Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup G) (w : P.domain.carrier) :
    MulAction.stabilizer G w ≃* _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusBoundaryStabilizer G w.val where
  toFun g := ⟨g.val.val,(_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mem_mobiusBoundaryStabilizer G w.val _).mpr
    ⟨g.val.property,congrArg Subtype.val g.property⟩⟩
  invFun g := ⟨⟨g.val,((_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mem_mobiusBoundaryStabilizer G w.val _).mp g.property).1⟩,
    Subtype.ext ((_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mem_mobiusBoundaryStabilizer G w.val _).mp g.property).2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- Literal angular sectors are genuine domains for every actual canonical rotation subgroup presentation. -/
theorem rotation_sector_fundamental_of_eq
    {H : Subgroup Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (n : ℕ) (hn : 2 ≤ n)
    (hH : H = finiteMobiusRotationGroup n) :
    IsFuchsianFundamentalDomain P (P.finiteCoordinate ⁻¹' _root_.LowDimensionalTopology.Geometry.Hyperbolic.finiteRotationDiscSector n) := by
  subst H
  exact finiteMobiusRotationDomain_fundamental n hn

/-- The full original stabilizer of zero has a literal primitive angular fundamental domain. -/
theorem UnitDiscFuchsianGroup.zero_stabilizer_sector
    {G : Subgroup Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup G)
    (hfix : ∃ g : G, g ≠ 1 ∧ g • P.finiteCoordinate.symm 0 = P.finiteCoordinate.symm 0) :
    ∃ n : ℕ, n = Nat.card (MulAction.stabilizer G (P.finiteCoordinate.symm 0)) ∧ 2 ≤ n ∧
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain (MulAction.stabilizer G (P.finiteCoordinate.symm 0)) P.domain.carrier P.area
        (P.finiteCoordinate ⁻¹' _root_.LowDimensionalTopology.Geometry.Hyperbolic.finiteRotationDiscSector n) := by
  let w := P.finiteCoordinate.symm 0
  let K := _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusBoundaryStabilizer G w.val
  let e := P.stabilizerEquiv w
  let zeroStabilizerPointFinite := P.point_stabilizer_finite w
  let zeroStabilizerMobiusFinite : Finite K := Finite.of_surjective e e.surjective
  have hw : w.val = ((0:ℂ):Mobius.ExtendedComplex) := by
    change (_root_.LowDimensionalTopology.Geometry.Surfaces.discFiniteHomeomorph.symm (0:Complex.UnitDisc)).val = _
    exact _root_.LowDimensionalTopology.Geometry.Surfaces.discFiniteHomeomorph_symm_coe 0
  have hi : K ≤ G := fun f hf => ((_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mem_mobiusBoundaryStabilizer G w.val f).mp hf).1
  have hp : ∀ f ∈ K, f.val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc = _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc :=
    fun f hf => P.image_eq ⟨f,hi hf⟩
  have h0 : ∀ f ∈ K, f.val (0:ℂ) = (0:ℂ) := by
    intro f hf
    rw [←hw]
    exact ((_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mem_mobiusBoundaryStabilizer G w.val f).mp hf).2
  let Q : UnitDiscFuchsianGroup K :=
    { invariant := fun g z hz => P.invariant ⟨g.val,hi g.property⟩ z hz
      discontinuous := by intro L hL hLK;exact Set.toFinite _ }
  let n := Nat.card K
  have hK : K = finiteMobiusRotationGroup n := finiteZeroDiscGroup_eq_rotation K hp h0
  obtain ⟨g,hg,hgw⟩ := hfix
  let k : K := ⟨g.val,(_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mem_mobiusBoundaryStabilizer G w.val g.val).mpr
    ⟨g.property,congrArg Subtype.val hgw⟩⟩
  have hk : k ≠ 1 := by
    intro he
    apply hg
    apply Subtype.ext
    exact congrArg (fun a : K => a.val) he
  let zeroStabilizerNontrivial : Nontrivial K := ⟨⟨k,1,hk⟩⟩
  let zeroStabilizerFintype : Fintype K := Fintype.ofFinite K
  have hn : 2 ≤ n := by
    have hh : 1 < n := by simpa only [n,Nat.card_eq_fintype_card] using (Fintype.one_lt_card : 1 < Fintype.card K)
    omega
  have hQ := rotation_sector_fundamental_of_eq Q n hn hK
  let f : P.domain.carrier ≃ₜ Q.domain.carrier := Homeomorph.setCongr rfl
  have he (g : MulAction.stabilizer G w) (x : P.domain.carrier) : f (g • x) = e g • f x := rfl
  have h := _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain.equivariant_preimage e f he hQ
  change _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain (MulAction.stabilizer G w) P.domain.carrier
    (Measure.map id Q.area) (P.finiteCoordinate ⁻¹' _root_.LowDimensionalTopology.Geometry.Hyperbolic.finiteRotationDiscSector n) at h
  rw [Measure.map_id] at h
  exact ⟨n,(Nat.card_congr e.toEquiv).symm,hn,h⟩

/-- The corrected normalized elliptic construction uses the full stabilizer and yields a genuine full-group polygon. -/
theorem UnitDiscFuchsianGroup.zero_stabilizer_polygon
    {G : Subgroup Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup G)
    (hfix : ∃ g : G, g ≠ 1 ∧ g • P.finiteCoordinate.symm 0 = P.finiteCoordinate.symm 0) :
    ∃ n : ℕ, n = Nat.card (MulAction.stabilizer G (P.finiteCoordinate.symm 0)) ∧
      2 ≤ n ∧ IsConvexFuchsianPolygon P
      ((P.finiteCoordinate ⁻¹' _root_.LowDimensionalTopology.Geometry.Hyperbolic.finiteRotationDiscSector n) ∩
        stabilizerDirichletRegion P (P.finiteCoordinate.symm 0)) := by
  obtain ⟨n,hncard,hn,hF⟩ := P.zero_stabilizer_sector hfix
  refine ⟨n,hncard,hn,stabilizerDirichletRegion_intersection_polygon P (P.finiteCoordinate.symm 0) _ hF ?_⟩
  rw [P.finiteCoordinate.surjective.image_preimage]
  exact _root_.LowDimensionalTopology.Geometry.Hyperbolic.finiteRotationDiscSector_hConvex n hn

/-- The primitive normalized elliptic element gives exactly the displayed sector of angle two pi divided by its order. -/
theorem primitive_elliptic_zero_polygon {G : Subgroup Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup G) (f : Mobius.complexMobiusGroup)
    (hf : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic f) (hprim : IsPrimitive G f)
    (h0 : f.val (0:ℂ) = (0:ℂ)) :
    IsConvexFuchsianPolygon P
      ((P.finiteCoordinate ⁻¹' _root_.LowDimensionalTopology.Geometry.Hyperbolic.finiteRotationDiscSector (orderOf f)) ∩
        stabilizerDirichletRegion P (P.finiteCoordinate.symm 0)) := by
  let w := P.finiteCoordinate.symm 0
  have hw : w.val = ((0:ℂ):Mobius.ExtendedComplex) := _root_.LowDimensionalTopology.Geometry.Surfaces.discFiniteHomeomorph_symm_coe 0
  have hfix : ∃ g : G, g ≠ 1 ∧ g • w = w := by
    refine ⟨⟨f,hprim.mem⟩,?_,?_⟩
    · intro he
      exact hf.1 (congrArg Subtype.val he)
    · apply Subtype.ext
      change f.val w.val = w.val
      rw [hw]
      exact h0
  obtain ⟨n,hncard,hn,hP⟩ := P.zero_stabilizer_polygon hfix
  have hnorder : n = orderOf f := by
    calc n = Nat.card (MulAction.stabilizer G w) := hncard
         _ = Nat.card (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusBoundaryStabilizer G w.val) := Nat.card_congr (P.stabilizerEquiv w).toEquiv
         _ = orderOf f := by rw [hw,←hprim.generates _ h0,Nat.card_zpowers]
  rwa [hnorder] at hP

end LowDimensionalTopology.Geometry.Fuchsian
