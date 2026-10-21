/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Hyperbolic.Models.Disc.ExtendedCarrier
public import LowDimensionalTopology.Geometry.Fuchsian.Dirichlet.DirichletIdealWeights
public import LowDimensionalTopology.Geometry.Fuchsian.Dirichlet.GenericDirichletHorocycles
public import LowDimensionalTopology.Geometry.Fuchsian.Dirichlet.GenericDirichletAccidental
public import LowDimensionalTopology.Geometry.Hyperbolic.Geodesic.Pencils.NativeParabolicPencils
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory
open scoped UpperHalfPlane MatrixGroups OnePoint Complex.UnitDisc Topology ComplexConjugate
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
local instance ordinaryCycleSphereMeasurableSpace : MeasurableSpace _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex := borel _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex
local instance ordinaryCycleSphereBorelSpace : BorelSpace _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex := ⟨rfl⟩

/-- The genuine inverse Cayley height equals the actual boundary-one Poisson kernel. -/
theorem discToHalfPlane_im_eq_poisson (z : 𝔻) :
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane z).im=_root_.LowDimensionalTopology.Geometry.Auxiliary.Analysis.discPoissonKernel (z:ℂ) 1 := by
  change (_root_.LowDimensionalTopology.Geometry.Hyperbolic.inverseCayleyFormula z).im=_
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.inverseCayley_im]
  simp only [_root_.LowDimensionalTopology.Geometry.Auxiliary.Analysis.discPoissonKernel,norm_sub_rev]

/-- Unit rotation transports the actual boundary Poisson weight with factor one. -/
theorem discPoissonKernel_rotation_inverse (ξ : ℂ) (hξ : ‖ξ‖=1) (z : 𝔻) :
    _root_.LowDimensionalTopology.Geometry.Auxiliary.Analysis.discPoissonKernel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discUnitRotation (conj ξ) (by simpa using hξ) z : ℂ) 1=
      _root_.LowDimensionalTopology.Geometry.Auxiliary.Analysis.discPoissonKernel (z:ℂ) ξ := by
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.discUnitRotation_coe]
  have hc : conj ξ*ξ=1:=by simpa only [mul_comm] using _root_.LowDimensionalTopology.Geometry.Hyperbolic.unit_mul_conj_eq_one ξ hξ
  have hd : conj ξ*(z:ℂ)-1=conj ξ*((z:ℂ)-ξ) := by rw [mul_sub,hc]
  simp only [_root_.LowDimensionalTopology.Geometry.Auxiliary.Analysis.discPoissonKernel,hd,norm_mul,Complex.norm_conj,hξ,one_mul]

/-- Equality of genuine Poisson weights places the three actual points on one independently defined intrinsic horocycle. -/
theorem disc_equal_poisson_common_horocycle (ξ : ℂ) (hξ : ‖ξ‖=1) (a b c : 𝔻)
    (hb : _root_.LowDimensionalTopology.Geometry.Auxiliary.Analysis.discPoissonKernel (b:ℂ)
      ξ=_root_.LowDimensionalTopology.Geometry.Auxiliary.Analysis.discPoissonKernel (a:ℂ) ξ)
    (hc : _root_.LowDimensionalTopology.Geometry.Auxiliary.Analysis.discPoissonKernel (c:ℂ)
      ξ=_root_.LowDimensionalTopology.Geometry.Auxiliary.Analysis.discPoissonKernel (a:ℂ) ξ) :
    ∃S : Set 𝔻,_root_.LowDimensionalTopology.Geometry.Hyperbolic.IsDiscHorocycleAt (ξ:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) S ∧ a∈S ∧ b∈S ∧ c∈S := by
  let κ:=_root_.LowDimensionalTopology.Geometry.Auxiliary.Analysis.discPoissonKernel (a:ℂ) ξ
  have hκ : 0<κ:=_root_.LowDimensionalTopology.Geometry.Auxiliary.Analysis.discPoissonKernel_pos a.norm_lt_one hξ
  let S:Set 𝔻:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discUnitRotation ξ hξ '' (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.horizontalHorocycle κ)
  have hS0:=(_root_.LowDimensionalTopology.Geometry.Hyperbolic.horizontalHorocycle_isHHorocycleAt κ hκ).cayley_image
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedCayley_infty] at hS0
  have hS:=hS0.rotation_image ξ hξ
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.discRotationMobius_coe,mul_one] at hS
  have hmem (z : 𝔻) (hz : _root_.LowDimensionalTopology.Geometry.Auxiliary.Analysis.discPoissonKernel (z:ℂ) ξ=κ) : z∈S := by
    let zr:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discUnitRotation (conj ξ) (by simpa using hξ) z
    have him : (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane zr).im=κ :=
      (discToHalfPlane_im_eq_poisson zr).trans ((discPoissonKernel_rotation_inverse ξ hξ z).trans hz)
    refine ⟨zr,⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane
      zr,him,_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc_discToHalfPlane zr⟩,?_⟩
    exact (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discUnitRotationHomeomorph ξ hξ).apply_symm_apply z
  exact ⟨S,hS,hmem a rfl,hmem b hb,hmem c hc⟩

/-- Actual ideal-cycle equivalence gives equality of two weights at the same actual ideal point. -/
theorem dirichlet_ideal_pair_same_poisson_weight {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (w : P.domain.carrier) (g : H) (ξ η : ℂ)
    (hξ : ξ∈fuchsianPolygonIdealBoundary P (dirichletDomain P w))
    (hη : η∈fuchsianPolygonIdealBoundary P (dirichletDomain P w))
    (himage : g.val.val (ξ:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)=(η:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)) :
    _root_.LowDimensionalTopology.Geometry.Auxiliary.Analysis.discPoissonKernel (P.finiteCoordinate (g⁻¹ • w)) ξ=_root_.LowDimensionalTopology.Geometry.Auxiliary.Analysis.discPoissonKernel (P.finiteCoordinate w) ξ := by
  obtain ⟨κ,hκ,hcov⟩:=P.poisson_covariance g ξ η ((mem_fuchsianPolygonIdealBoundary _ _ _).mp hξ).2 himage
  have hle:=dirichlet_ideal_poisson_max P w ξ hξ g⁻¹
  have hle':=mul_le_mul_of_nonneg_right (dirichlet_ideal_poisson_max P w η hη g) hκ.le
  have hcw:=hcov w
  have hci:=hcov (g⁻¹ • w)
  rw [smul_inv_smul] at hci
  rw [hcw,hci] at hle'
  exact le_antisymm hle hle'



/-- At a genuine good centre there cannot be three distinct actual ideal boundary points in the same original group orbit. -/
theorem dirichlet_good_ideal_boundary_no_three {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (w : P.domain.carrier) (hw : IsDirichletCenter P w)
    (hgood : w∉dirichletHorocycleBadCenters P) (ξ η ζ : ℂ)
    (hξ : ξ∈fuchsianPolygonIdealBoundary P (dirichletDomain P w))
    (hη : η∈fuchsianPolygonIdealBoundary P (dirichletDomain P w))
    (hζ : ζ∈fuchsianPolygonIdealBoundary P (dirichletDomain P w))
    (hξη : ξ≠η) (hξζ : ξ≠ζ) (hηζ : η≠ζ) (g h : H)
    (hgξ : g.val.val (ξ:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)=(η:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex))
    (hhξ : h.val.val (ξ:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)=(ζ:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)) : False := by
  have hg : g≠1 := by
    intro he
    have hx : (ξ:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)=(η:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex):=by simpa [he] using hgξ
    exact hξη (OnePoint.coe_injective hx)
  have hh : h≠1 := by
    intro he
    have hx : (ξ:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)=(ζ:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex):=by simpa [he] using hhξ
    exact hξζ (OnePoint.coe_injective hx)
  have hgh : g≠h := by
    intro he
    have hx : (η:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)=(ζ:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex):=hgξ.symm.trans (he ▸ hhξ)
    exact hηζ (OnePoint.coe_injective hx)
  have hgK:=dirichlet_ideal_pair_same_poisson_weight P w g ξ η hξ hη hgξ
  have hhK:=dirichlet_ideal_pair_same_poisson_weight P w h ξ ζ hξ hζ hhξ
  obtain ⟨U,hU,hwU,hgwU,hhwU⟩:=disc_equal_poisson_common_horocycle ξ
    ((mem_fuchsianPolygonIdealBoundary _ _ _).mp hξ).2
    (P.finiteCoordinate w) (P.finiteCoordinate (g⁻¹ • w)) (P.finiteCoordinate (h⁻¹ • w)) hgK hhK
  let ξH:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedCayley.symm (ξ:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)
  have hUH : _root_.LowDimensionalTopology.Geometry.Hyperbolic.IsHHorocycleAt ξH (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane '' U):=hU.cayley_inverse_image
  obtain ⟨_hgP,_hhP,hfix,_hhfix⟩:=dirichlet_good_center_horocycle_fixed P w hw hgood g⁻¹ h⁻¹
    (inv_ne_one.mpr hg) (inv_ne_one.mpr hh) (inv_injective.ne hgh) hUH
    ⟨P.finiteCoordinate w,hwU,rfl⟩ ⟨P.finiteCoordinate (g⁻¹ • w),hgwU,rfl⟩
    ⟨P.finiteCoordinate (h⁻¹ • w),hhwU,rfl⟩
  have hξH : _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius.val ξH=(ξ:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) := by
    change _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedCayley (_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedCayley.symm (ξ:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex))=_
    exact _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedCayley.apply_symm_apply _
  rw [P.dirichletRealLift_projection] at hfix
  change _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius.val.symm (g.val.val.symm
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius.val ξH))=ξH at hfix
  have hfixed:=congrArg _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius.val hfix
  rw [Equiv.apply_symm_apply,hξH] at hfixed
  have hhfixed:=congrArg g.val.val hfixed
  rw [Equiv.apply_symm_apply,hgξ] at hhfixed
  exact hξη (OnePoint.coe_injective hhfixed)

/-- Every literal ideal orbit cycle at a genuine good centre has at most two actual points. -/
theorem dirichlet_good_ideal_cycle_no_three {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (w : P.domain.carrier) (hw : IsDirichletCenter P w)
    (hgood : w∉dirichletHorocycleBadCenters P) (α a b c : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)
    (ha : a∈fuchsianPolygonIdealCycle P (dirichletDomain P w) α)
    (hb : b∈fuchsianPolygonIdealCycle P (dirichletDomain P w) α)
    (hc : c∈fuchsianPolygonIdealCycle P (dirichletDomain P w) α)
    (hab : a≠b) (hac : a≠c) (hbc : b≠c) : False := by
  obtain ⟨ξ,hξ,rfl⟩:=ha.1
  obtain ⟨η,hη,rfl⟩:=hb.1
  obtain ⟨ζ,hζ,rfl⟩:=hc.1
  have horb : MulAction.orbit H (ξ:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)=MulAction.orbit H α:=MulAction.orbit_eq_iff.mpr ha.2
  have hbξ : (η:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)∈MulAction.orbit H (ξ:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex):=horb.symm ▸ hb.2
  have hcξ : (ζ:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)∈MulAction.orbit H (ξ:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex):=horb.symm ▸ hc.2
  obtain ⟨g,hg⟩:=MulAction.mem_orbit_iff.mp hbξ
  obtain ⟨h,hh⟩:=MulAction.mem_orbit_iff.mp hcξ
  exact dirichlet_good_ideal_boundary_no_three P w hw hgood ξ η ζ hξ hη hζ
    (fun he=>hab (congrArg OnePoint.some he)) (fun he=>hac (congrArg OnePoint.some he))
    (fun he=>hbc (congrArg OnePoint.some he)) g h hg hh



/-- The actual ordinary-point condition, including elementary groups. -/
def HasMobiusOrdinaryNeighborhood (H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (ξ :
  _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) : Prop :=
  ∃U : Set _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex,IsOpen U ∧ ξ∈U ∧ _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn H U

/-- The usual non-elementary ordinary set gives the actual local condition. -/
theorem hasMobiusOrdinaryNeighborhood_of_ordinarySet (H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hH : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary H) (hd :
      _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup H) (ξ :
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)
    (hξ : ξ∈_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusOrdinarySet
      H) : HasMobiusOrdinaryNeighborhood H ξ :=
  ⟨_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusOrdinarySet
    H,_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusOrdinarySet_isOpen
    H,hξ,_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobius_ordinary_discontinuous H hH hd⟩

/-- A genuine parabolic fixed point is not an actual ordinary point. -/
theorem ordinaryNeighborhood_not_parabolic_fixed {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (ξ : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) (hξ : HasMobiusOrdinaryNeighborhood H ξ) (g : H)
    (hg : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic g.val) : g.val.val ξ≠ξ := by
  intro hfix
  obtain ⟨U,_hU,hξU,hd⟩:=hξ
  exact _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobius_infinite_order_fixed_not_discontinuousOn H U g
    (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobius_parabolic_or_loxodromic_not_isOfFinOrder g.val (Or.inl
      hg)) ξ hξU hfix hd

/-- Every genuine ordinary ideal polygon point has trivial actual stabilizer. -/
theorem dirichlet_ordinary_ideal_free {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (w : P.domain.carrier) (hw : IsDirichletCenter P w)
    (u : Circle) (hu : (u:ℂ)∈fuchsianPolygonIdealBoundary P (dirichletDomain P w))
    (hOrd : HasMobiusOrdinaryNeighborhood H ((u:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)) :
    ∀g : H,g.val.val ((u:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)=((u:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)→g=1 := by
  intro g hfix
  by_contra hg
  have hp:=(dirichletDomain_isConvexFuchsianPolygon P w hw).nonidentity_ideal_fixer_parabolic g hg (u:ℂ) hu hfix
  exact ordinaryNeighborhood_not_parabolic_fixed _ hOrd g hp hfix

/-- Original disc-preserving elements preserve the actual ideal unit circle. -/
theorem UnitDiscFuchsianGroup.unitCircle_image {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (g : H) (ξ : ℂ) (hξ : ‖ξ‖=1) :
    ∃η : ℂ,‖η‖=1 ∧ g.val.val (ξ:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)=(η:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) := by
  have hξF : (ξ:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)∈frontier _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc := by
    rw [_root_.LowDimensionalTopology.Geometry.Mobius.frontier_extendedUnitDisc_eq_circle,_root_.LowDimensionalTopology.Geometry.Mobius.complexCircle_coe,sub_zero]
    exact hξ
  let F:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex≃ₜ_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex :=
    { toEquiv:=g.val.val
      continuous_toFun:=(_root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusContinuousMap g.val).continuous
      continuous_invFun:=(_root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusContinuousMap g.val⁻¹).continuous }
  have him : F '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc=_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc :=P.image_eq g
  have hfront:=F.image_frontier _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc
  rw [him] at hfront
  have hy : g.val.val (ξ:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)∈frontier _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc := by
    rw [←hfront]
    exact ⟨(ξ:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex),hξF,rfl⟩
  generalize he : g.val.val (ξ:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)=y at hy ⊢
  induction y using OnePoint.rec with
  | infty => exact False.elim (_root_.LowDimensionalTopology.Geometry.Mobius.complexCircle_infty 0 1
    (_root_.LowDimensionalTopology.Geometry.Mobius.frontier_extendedUnitDisc_eq_circle ▸ hy))
  | coe η => exact ⟨η,by simpa only [_root_.LowDimensionalTopology.Geometry.Mobius.frontier_extendedUnitDisc_eq_circle,_root_.LowDimensionalTopology.Geometry.Mobius.complexCircle_coe,sub_zero] using hy,rfl⟩

/-- A literal side label transports the true ideal endpoint to the actual paired polygon boundary. -/
theorem dirichlet_side_ideal_paired_point {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (w : P.domain.carrier) (g : H) (S : Set P.domain.carrier)
    (hS : S=closure (dirichletDomain P w)∩fuchsianDomainTile P (dirichletDomain P w) g)
    (u : Circle) (hu : IsFuchsianSideIdealEndpoint P S u) :
    ∃η : ℂ,η∈fuchsianPolygonIdealBoundary P (dirichletDomain P w) ∧
      (g⁻¹).val.val ((u:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)=(η:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) := by
  obtain ⟨η,hη,himage⟩:=P.unitCircle_image g⁻¹ (u:ℂ) (Circle.norm_coe u)
  have huCl : ((u:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)∈closure ((Subtype.val : P.domain.carrier→_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) '' S) := by
    have hh:=image_closure_subset_closure_image OnePoint.continuous_coe ⟨(u:ℂ),hu,rfl⟩
    rwa [fuchsianPolygon_finite_image_extended P S] at hh
  have hmap:=image_closure_subset_closure_image (_root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusContinuousMap (g⁻¹).val).continuous ⟨((u:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex),huCl,rfl⟩
  have hsub : (fun x : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex=>g⁻¹ • x) '' ((Subtype.val :
    P.domain.carrier→_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) '' S) ⊆
      (Subtype.val : P.domain.carrier→_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) '' closure (dirichletDomain P w) := by
    rintro _ ⟨_,⟨x,hx,rfl⟩,rfl⟩
    have hxS:=hS ▸ hx
    obtain ⟨y,hy,hgy⟩:=hxS.2
    refine ⟨y,hy,?_⟩
    have hpre : g⁻¹ • x=y := by rw [←hgy,inv_smul_smul]
    exact (congrArg Subtype.val hpre).symm
  have hclosure := closure_mono hsub hmap
  have himcl : ((Subtype.val : P.domain.carrier→_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) ''
    closure (dirichletDomain P w)) ⊆
      closure ((Subtype.val : P.domain.carrier→_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) ''
        dirichletDomain P w) :=
    image_closure_subset_closure_image continuous_subtype_val
  have hclosure':=closure_mono himcl hclosure
  rw [closure_closure] at hclosure'
  change (g⁻¹).val.val ((u:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)∈_ at hclosure'
  rw [himage] at hclosure'
  exact ⟨η,(mem_fuchsianPolygonIdealBoundary_iff_extendedClosure P _ η).mpr ⟨hη,hclosure'⟩,himage⟩



/-- The actual improper ordinary vertex has a second distinct literal orbit-cycle point. -/
theorem dirichlet_improper_ordinary_cycle_pair {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (w : P.domain.carrier) (hw : IsDirichletCenter P w)
    (hgood : w∉dirichletHorocycleBadCenters P) (u : Circle)
    (hu : IsImproperFuchsianInfiniteVertex P (dirichletDomain P w) u)
    (hOrd : HasMobiusOrdinaryNeighborhood H ((u:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)) :
    ∃η : ℂ,((u:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)≠(η:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) ∧
      fuchsianPolygonIdealCycle P (dirichletDomain P
        w) ((u:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)=
        {((u:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex),(η:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)} := by
  obtain ⟨huE,S,_F,hS,huS,_hF,_huF⟩:=hu
  obtain ⟨g,hg,hSeq⟩:=hS.1
  obtain ⟨η,hηE,himage⟩:=dirichlet_side_ideal_paired_point P w g S hSeq u huS
  have hne : ((u:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)≠(η:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) := by
    intro he
    have hfix : (g⁻¹).val.val ((u:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)=((u:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex):=himage.trans he.symm
    have hInv:=dirichlet_ordinary_ideal_free P w hw u huE hOrd g⁻¹ hfix
    exact hg (inv_eq_one.mp hInv)
  have huCycle : ((u:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)∈fuchsianPolygonIdealCycle P (dirichletDomain P w) ((u:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) :=
    ⟨⟨(u:ℂ),huE,rfl⟩,MulAction.mem_orbit_self _⟩
  have hηCycle : (η:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)∈fuchsianPolygonIdealCycle P (dirichletDomain P w) ((u:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) :=
    ⟨⟨η,hηE,rfl⟩,MulAction.mem_orbit_iff.mpr ⟨g⁻¹,himage⟩⟩
  refine ⟨η,hne,?_⟩
  apply Set.Subset.antisymm
  · intro x hx
    by_cases hxu : x=((u:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)
    · exact Or.inl hxu
    by_cases hxη : x=(η:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)
    · exact Or.inr hxη
    exact False.elim (dirichlet_good_ideal_cycle_no_three P w hw hgood
      ((u:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)
      ((u:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) (η:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) x huCycle hηCycle hx hne (Ne.symm hxu) (Ne.symm hxη))
  · rintro x (rfl|rfl)
    · exact huCycle
    · exact hηCycle

/-- For almost every actual centre, every improper vertex which is an ordinary point has literal ideal-cycle length two. -/
theorem ae_dirichlet_improper_ordinary_ideal_cycle_ncard_eq_two {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) :
    ∀ᵐw : P.domain.carrier ∂P.area,IsDirichletCenter P w ∧ ∀u : Circle,
      IsImproperFuchsianInfiniteVertex P (dirichletDomain P w) u→
      HasMobiusOrdinaryNeighborhood H ((u:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)→
      (fuchsianPolygonIdealCycle P (dirichletDomain P w) ((u:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)).ncard=2 := by
  filter_upwards [dirichletHorocycle_ae_good P] with w hw
  refine ⟨hw.1,?_⟩
  intro u hu hOrd
  obtain ⟨η,hne,he⟩:=dirichlet_improper_ordinary_cycle_pair P w hw.1 hw.2 u hu hOrd
  exact Set.ncard_eq_two.mpr ⟨((u:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex),(η:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex),hne,he⟩



/-- Elliptic, accidental, ordinary ideal and parabolic cycle properties hold
simultaneously for almost every center with respect to the quotient density area. -/
theorem ae_dirichlet_elliptic_accidental_ordinary_parabolic_cycle_properties {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P : UnitDiscFuchsianGroup H) :
    ∀ᵐw : P.domain.carrier ∂P.area,IsDirichletCenter P w ∧
      (∀x∈fuchsianEllipticPoints P,
        fuchsianPolygonCycleLength P (fuchsianPolygonCycle P (dirichletDomain P w) x)=1) ∧
      (∀x,IsFuchsianPolygonVertex P (dirichletDomain P w) x→IsAccidentalFuchsianPoint P x→
        fuchsianPolygonCycleLength P (fuchsianPolygonCycle P (dirichletDomain P w) x)=3) ∧
      (∀u : Circle,IsImproperFuchsianInfiniteVertex P (dirichletDomain P w) u→
        HasMobiusOrdinaryNeighborhood H ((u:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)→
        (fuchsianPolygonIdealCycle P (dirichletDomain P w)
          ((u:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)).ncard=2) ∧
      (∀u : Circle,IsProperFuchsianInfiniteVertex P (dirichletDomain P w) u→
        ∃g : H,g≠1 ∧ _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic g.val ∧ g.val.val ((u:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)=((u:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) ∧
          fuchsianPolygonIdealCycle P (dirichletDomain P w) ((u:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)={((u:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)}) ∧
      (∀f : H,_root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic f.val→∀ξ :
        _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex,f.val.val ξ=ξ→
        ∃η : Circle,fuchsianPolygonIdealCycle P (dirichletDomain P
          w) ξ={((η:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)} ∧
          IsProperFuchsianInfiniteVertex P (dirichletDomain P w) η) := by
  filter_upwards [ae_dirichlet_elliptic_cycleLength_eq_one P,ae_dirichlet_accidental_vertex_cycleLength_eq_three P,
    ae_dirichlet_improper_ordinary_ideal_cycle_ncard_eq_two P,ae_dirichlet_proper_ideal_vertex_parabolic_fixer_and_singleton_cycle P,
    ae_dirichlet_parabolic_fixed_cycle_singleton_proper_vertex P] with w h1 h2 h3 h4 h5
  exact ⟨h1.1,h1.2,h2.2,h3.2,h4.2,h5.2⟩

end LowDimensionalTopology.Geometry.Fuchsian
