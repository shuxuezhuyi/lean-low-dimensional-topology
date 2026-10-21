/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Hyperbolic.Models.Disc.ExtendedCarrier
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.GeneralizedFundamentalDomains
public import LowDimensionalTopology.Geometry.Mobius.Circle.IsometricCircles
public import LowDimensionalTopology.Geometry.Mobius.Topology.MobiusOmittedValues
public import LowDimensionalTopology.Geometry.Hyperbolic.Metric.DiscCircleDistance
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory
open scoped Topology OnePoint Pointwise ComplexConjugate
namespace LowDimensionalTopology.Geometry.Mobius
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
noncomputable section

/-- The original Euclidean Ford region: the common strict exterior of all actual non-affine group isometric circles. -/
def complexFordRegion (H : Subgroup complexMobiusGroup) : Set ℂ:=
  {z | ∀A : Auxiliary.Algebra.SpecialLinear2,mobiusSpecialLinearProjection A∈H→A 1 0≠0→1<‖A 1 0*z+A 1 1‖}

/-- Each matrix condition is the strict Euclidean exterior of its genuine isometric circle. -/
theorem complexFordRegion_circle_exterior (A : Auxiliary.Algebra.SpecialLinear2) (hc : A 1 0≠0) (z : ℂ) :
    1<‖A 1 0*z+A 1 1‖ ↔
      isometricCircleRadius (A 0 0) (A 0 1) (A 1 0) (A 1 1)<‖z-(-A 1 1/A 1 0)‖:=by
  have hd : A 0 0*A 1 1-A 0 1*A 1 0=1:=by simpa only [Matrix.det_fin_two] using A.det_coe
  have hp : 0<‖A 1 0‖:=norm_pos_iff.mpr hc
  have he : A 1 0*z+A 1 1=A 1 0*(z-(-A 1 1/A 1 0)):=by field_simp;ring
  rw [isometricCircleRadius,hd,norm_one,Real.sqrt_one,div_lt_iff₀ hp,he,norm_mul]
  rw [mul_comm]

/-- No chosen matrix representative enters the original common-exterior definition. -/
theorem mem_complexFordRegion_iff (H : Subgroup complexMobiusGroup) (z : ℂ) :
    z∈complexFordRegion H ↔ ∀A : Auxiliary.Algebra.SpecialLinear2,mobiusSpecialLinearProjection A∈H→
      ∀_hc : A 1 0≠0,isometricCircleRadius (A 0 0) (A 0 1) (A 1 0) (A 1 1)<‖z-(-A 1 1/A 1 0)‖:=by
  constructor
  · intro hz A hA hc
    exact (complexFordRegion_circle_exterior A hc z).mp (hz A hA hc)
  · intro hz A hA hc
    exact (complexFordRegion_circle_exterior A hc z).mpr (hz A hA hc)

/-- The source's free-infinity hypothesis gives a genuine non-affine isometric circle for each nonidentity original map. -/
theorem free_infty_nonidentity_has_isometricCircle
    (H : Subgroup complexMobiusGroup) (hfree : ∀g : H,g • (∞ : ExtendedComplex)=∞→g=1)
    (g : H) (hg : g≠1) :
    ∃A : Auxiliary.Algebra.SpecialLinear2,mobiusSpecialLinearProjection A=g.val ∧ A 1 0≠0:=by
  obtain ⟨A,hA⟩:=mobiusSpecialLinearProjection_surjective g.val
  refine ⟨A,hA,?_⟩
  intro hc
  apply hg
  apply hfree g
  change g.val.val ∞=∞
  rw [←hA,specialLinear_projection_coe]
  exact (Mobius.Classification.specialLinear_fixes_infty_iff A).mpr hc

/-- Radial strict order of genuine disc path distance is exactly Euclidean radial strict order. -/
theorem disc_radial_distance_lt_iff (z w : Complex.UnitDisc) :
    Hyperbolic.discPathDist 0 z<Hyperbolic.discPathDist 0 w ↔ ‖(z : ℂ)‖<‖(w : ℂ)‖:=by
  rw [lt_iff_not_ge,Hyperbolic.disc_distance_zero_le_iff,←Hyperbolic.disc_norm_eq_tanh_half_distance,not_le]

/-- The genuine normalized-disc defect identity identifies its isometric-circle exterior with radial distance growth. -/
theorem discFractional_radial_growth_iff (a c : ℂ) (hdet : Complex.normSq a-Complex.normSq c=1)
    (z : Complex.UnitDisc) :
    Hyperbolic.discPathDist 0 z<Hyperbolic.discPathDist 0 (Hyperbolic.discFractionalHomeomorph a c hdet z) ↔
      1<‖c*z+conj a‖:=by
  rw [disc_radial_distance_lt_iff]
  let w:=Hyperbolic.discFractionalHomeomorph a c hdet z
  let d:=‖c*(z : ℂ)+conj a‖
  have hd0 : 0<d:=norm_pos_iff.mpr (Auxiliary.Analysis.discFractional_den_ne_zero hdet z.norm_lt_one.le)
  have hz0 : 0<1-‖(z : ℂ)‖^2:=sub_pos.mpr z.sq_norm_lt_one
  have hdef : 1-‖(w : ℂ)‖^2=(1-‖(z : ℂ)‖^2)/d^2:=
    Auxiliary.Analysis.discFractional_defect hdet (Auxiliary.Analysis.discFractional_den_ne_zero hdet z.norm_lt_one.le)
  have hsq : ‖(z : ℂ)‖<‖(w : ℂ)‖ ↔ 1-‖(w : ℂ)‖^2<1-‖(z : ℂ)‖^2:=by
    constructor <;> intro h <;> nlinarith [norm_nonneg (z : ℂ),norm_nonneg (w : ℂ)]
  rw [hsq,hdef,div_lt_iff₀ (sq_pos_of_pos hd0),lt_mul_iff_one_lt_right hz0]
  change 1<d^2 ↔ 1<d
  constructor <;> intro h <;> nlinarith


/-- The actual determinant-one representative of a disc-preserving map has the standard disc coefficients. -/
theorem complexFord_disc_coefficients (A : Auxiliary.Algebra.SpecialLinear2)
    (hpres : (mobiusSpecialLinearProjection A).val '' Hyperbolic.extendedUnitDisc=Hyperbolic.extendedUnitDisc) :
    ∃hdet : Complex.normSq (A 0 0)-Complex.normSq (A 1 0)=1,
      A 1 1=conj (A 0 0) ∧
      (mobiusSpecialLinearProjection A).val=Hyperbolic.normalizedDiscTransformation (A 0 0) (A 1 0) hdet:=by
  rw [specialLinear_projection_coe] at hpres
  obtain ⟨hb,hd,hdet⟩:=Hyperbolic.specialLinear_disc_coefficients A hpres
  refine ⟨hdet,hd,?_⟩
  rw [specialLinear_projection_coe]
  unfold Hyperbolic.normalizedDiscTransformation fractionalLinearOfCoefficients
  apply congrArg fractionalLinear
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coefficientMatrix,hb,hd]

/-- The actual origin in the original unit-disc sphere model. -/
def _root_.LowDimensionalTopology.Geometry.Fuchsian.UnitDiscFuchsianGroup.origin {H : Subgroup complexMobiusGroup}
    (P : Fuchsian.UnitDiscFuchsianGroup H) :
    P.domain.carrier:=P.finiteCoordinate.symm 0

theorem _root_.LowDimensionalTopology.Geometry.Fuchsian.UnitDiscFuchsianGroup.origin_finite {H : Subgroup
    complexMobiusGroup} (P : Fuchsian.UnitDiscFuchsianGroup H) :
    P.finiteCoordinate P.origin=0:=P.finiteCoordinate.apply_symm_apply 0

theorem _root_.LowDimensionalTopology.Geometry.Fuchsian.UnitDiscFuchsianGroup.origin_extended {H : Subgroup
    complexMobiusGroup} (P : Fuchsian.UnitDiscFuchsianGroup H) :
    P.origin.val=((0 : ℂ) : ExtendedComplex):=by
  have he:=(P.finiteCoordinate_extended P.origin).symm
  rw [P.origin_finite] at he
  exact he

/-- The original isometric-circle cut is exactly the actual metric comparison with the inverse image of zero. -/
theorem unitDisc_isometricCircle_distanceComparison {H : Subgroup complexMobiusGroup}
    (P : Fuchsian.UnitDiscFuchsianGroup H) (g : H) (A : Auxiliary.Algebra.SpecialLinear2)
    (hA : mobiusSpecialLinearProjection A=g.val) (x : P.domain.carrier) :
    1<‖A 1 0*(P.finiteCoordinate x : ℂ)+A 1 1‖ ↔
      P.hyperbolicDist x P.origin<P.hyperbolicDist x (g⁻¹ • P.origin):=by
  have hp : (mobiusSpecialLinearProjection A).val '' Hyperbolic.extendedUnitDisc=Hyperbolic.extendedUnitDisc:=by
    rw [hA];exact P.image_eq g
  obtain ⟨hdet,hd,hform⟩:=complexFord_disc_coefficients A hp
  have hform' : g.val.val=Hyperbolic.normalizedDiscTransformation (A 0 0) (A 1 0) hdet:=by rw [←hA];exact hform
  have hs (z : Complex.UnitDisc) : Hyperbolic.discPathDist z 0=Hyperbolic.discPathDist 0 z:=by
    rw [Hyperbolic.discPathDist_eq_halfPlane,Hyperbolic.discPathDist_eq_halfPlane,dist_comm]
  rw [P.hyperbolicDist_inverse_smul,inv_inv,P.hyperbolicDist_eq_discPathDist,
    P.hyperbolicDist_eq_discPathDist,P.origin_finite,
    P.finite_smul g (A 0 0) (A 1 0) hdet hform',hs,hs,hd]
  exact (discFractional_radial_growth_iff _ _ hdet _).symm

/-- The true complex Ford region intersected with the actual unit disc is exactly the zero-centered original Dirichlet polygon. -/
theorem complexFordRegion_unitDisc_eq_dirichlet {H : Subgroup complexMobiusGroup}
    (P : Fuchsian.UnitDiscFuchsianGroup H)
    (hfree : ∀g : H,g • (∞ : ExtendedComplex)=∞→g=1) :
    {x : P.domain.carrier | (P.finiteCoordinate x : ℂ)∈complexFordRegion H}=Fuchsian.dirichletDomain P P.origin:=by
  ext x
  constructor
  · intro hx g hg
    obtain ⟨A,hA,hc⟩:=free_infty_nonidentity_has_isometricCircle H hfree g⁻¹ (inv_ne_one.mpr hg)
    have hi:=(unitDisc_isometricCircle_distanceComparison P g⁻¹ A hA x).mp (hx A (hA.symm ▸ g⁻¹.property) hc)
    change P.hyperbolicDist x P.origin<P.hyperbolicDist x (g • P.origin)
    simpa only [inv_inv] using hi
  · intro hx A hA hc
    let g : H:=⟨mobiusSpecialLinearProjection A,hA⟩
    have hg : g≠1:=by
      intro he
      apply hc
      apply (Mobius.Classification.specialLinear_fixes_infty_iff A).mp
      change fractionalLinear (Matrix.SpecialLinearGroup.toGL A) ∞=∞
      rw [←specialLinear_projection_coe]
      change g.val.val ∞=∞
      rw [he]
      rfl
    apply (unitDisc_isometricCircle_distanceComparison P g A rfl x).mpr
    exact hx g⁻¹ (inv_ne_one.mpr hg)


/-- The original extended-plane Ford region is the intersection of the actual spherical exterior components. -/
def extendedComplexFordRegion (H : Subgroup complexMobiusGroup) : Set ExtendedComplex:=
  {ξ | ∀A : Auxiliary.Algebra.SpecialLinear2,mobiusSpecialLinearProjection A∈H→∀_hc : A 1 0≠0,
    ξ∈connectedComponentIn (complexCircle (-A 1 1/A 1 0)
      (isometricCircleRadius (A 0 0) (A 0 1) (A 1 0) (A 1 1)))ᶜ ∞}

/-- Its genuine finite coordinate is exactly the common strict Euclidean circle exterior. -/
theorem extendedComplexFordRegion_coe (H : Subgroup complexMobiusGroup) (z : ℂ) :
    (z : ExtendedComplex)∈extendedComplexFordRegion H ↔ z∈complexFordRegion H:=by
  have hpos (A : Auxiliary.Algebra.SpecialLinear2) (hc : A 1 0≠0) :
      0 < isometricCircleRadius (A 0 0) (A 0 1) (A 1 0) (A 1 1):=by
    apply isometricCircleRadius_pos _ _ _ _ _ hc
    have hd : A 0 0*A 1 1-A 0 1*A 1 0=1:=by simpa only [Matrix.det_fin_two] using A.det_coe
    rw [hd]
    norm_num
  constructor
  · intro hz A hA hc
    apply (complexFordRegion_circle_exterior A hc z).mpr
    exact (Fuchsian.mem_circle_complement_component_infty _ _ _ (hpos A hc)).mp (hz A hA hc)
  · intro hz A hA hc
    apply (Fuchsian.mem_circle_complement_component_infty _ _ _ (hpos A hc)).mpr
    exact (complexFordRegion_circle_exterior A hc z).mp (hz A hA hc)

/-- The ordinary distinguished point infinity is included in the genuine spherical exterior. -/
theorem extendedComplexFordRegion_infty (H : Subgroup complexMobiusGroup) :
    (∞ : ExtendedComplex)∈extendedComplexFordRegion H:=by
  intro A _ _
  exact mem_connectedComponentIn (complexCircle_infty _ _)

/-- The full extended region consists precisely of the finite original Ford region and infinity. -/
theorem extendedComplexFordRegion_eq (H : Subgroup complexMobiusGroup) :
    extendedComplexFordRegion H=((↑) : ℂ→ExtendedComplex) '' complexFordRegion H∪{∞}:=by
  ext ξ
  induction ξ using OnePoint.rec with
  | infty => simp [extendedComplexFordRegion_infty]
  | coe z => simp only [extendedComplexFordRegion_coe,mem_union,mem_image,OnePoint.coe_injective.eq_iff,
      exists_eq_right,mem_singleton_iff,OnePoint.coe_ne_infty,or_false]

/-- The actual extended Ford subset restricts to exactly the original zero-centered metric Dirichlet polygon. -/
theorem extendedComplexFordRegion_unitDisc_preimage {H : Subgroup complexMobiusGroup}
    (P : Fuchsian.UnitDiscFuchsianGroup H) (hfree : ∀g : H,g • (∞ : ExtendedComplex)=∞→g=1) :
    {x : P.domain.carrier | x.val∈extendedComplexFordRegion H}=Fuchsian.dirichletDomain P P.origin:=by
  ext x
  have he:=Set.ext_iff.mp (complexFordRegion_unitDisc_eq_dirichlet P hfree) x
  change (x.val∈extendedComplexFordRegion H) ↔ x∈Fuchsian.dirichletDomain P P.origin
  rw [←P.finiteCoordinate_extended x,extendedComplexFordRegion_coe]
  exact he

/-- on the actual extended complex plane, with literal intersection and original Dirichlet set. -/
theorem fordRegion_inter_disc_eq_origin_dirichletDomain {H : Subgroup complexMobiusGroup}
    (P : Fuchsian.UnitDiscFuchsianGroup H) (hfree : ∀g : H,g • (∞ : ExtendedComplex)=∞→g=1) :
    Hyperbolic.extendedUnitDisc∩extendedComplexFordRegion H=
      Subtype.val '' Fuchsian.dirichletDomain P P.origin:=by
  ext ξ
  constructor
  · rintro ⟨hξ,hF⟩
    let x : P.domain.carrier:=⟨ξ,hξ⟩
    refine ⟨x,?_,rfl⟩
    exact (Set.ext_iff.mp (extendedComplexFordRegion_unitDisc_preimage P hfree) x).mp hF
  · rintro ⟨x,hx,rfl⟩
    exact ⟨x.property,(Set.ext_iff.mp (extendedComplexFordRegion_unitDisc_preimage P hfree) x).mpr hx⟩


/-- The original free-infinity convention forces the actual origin to have trivial stabilizer as well. -/
theorem unitDisc_origin_free_of_infty {H : Subgroup complexMobiusGroup}
    (P : Fuchsian.UnitDiscFuchsianGroup H) (hfree : ∀g : H,g • (∞ : ExtendedComplex)=∞→g=1) :
    Fuchsian.IsDirichletCenter P P.origin:=by
  apply Fuchsian.unitDisc_dirichletCenter_of_free
  rw [P.origin_extended]
  exact Fuchsian.unitDisc_zero_free_of_infty P.asFuchsianDisc rfl hfree

/-- In the original Fuchsian disc case the literal Ford intersection is a genuine fundamental domain. -/
theorem complexFordRegion_unitDisc_fundamental {H : Subgroup complexMobiusGroup}
    (P : Fuchsian.UnitDiscFuchsianGroup H) (hfree : ∀g : H,g • (∞ : ExtendedComplex)=∞→g=1) :
    Fuchsian.IsFuchsianFundamentalDomain P {x | x.val∈extendedComplexFordRegion H}:=by
  rw [extendedComplexFordRegion_unitDisc_preimage P hfree]
  exact Fuchsian.dirichletDomain_fundamental P P.origin (unitDisc_origin_free_of_infty P hfree)

end
end LowDimensionalTopology.Geometry.Mobius
