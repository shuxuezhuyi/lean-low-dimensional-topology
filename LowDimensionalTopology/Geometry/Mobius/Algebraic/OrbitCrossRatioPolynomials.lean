/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Hyperbolic.Models.Disc.ExtendedCarrier
public import LowDimensionalTopology.Geometry.Auxiliary.Analysis.RationalRealLocus
public import LowDimensionalTopology.Geometry.Fuchsian.Dirichlet.GenericDirichletCenters
public import LowDimensionalTopology.Geometry.Mobius.Circle.ComplexCircles
public import LowDimensionalTopology.Geometry.Mobius.Topology.MobiusOmittedValues
@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Polynomial MeasureTheory
open scoped OnePoint Topology
namespace LowDimensionalTopology.Geometry.Mobius
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Surfaces LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Inversive LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
local instance orbitRatioSphereMeasurableSpace : MeasurableSpace ExtendedComplex:=borel ExtendedComplex
local instance orbitRatioSphereBorelSpace : BorelSpace ExtendedComplex:=⟨rfl⟩

/-- The actual homogeneous numerator or denominator of a determinant-one Mobius representative. -/
def orbitLinearPolynomial (A : Auxiliary.Algebra.SpecialLinear2) (i : Fin 2) : Polynomial ℂ:=
  C (A i 0)*X+C (A i 1)

/-- The projective difference of two actual matrix images is a genuine quadratic polynomial. -/
def orbitPairPolynomial (A B : Auxiliary.Algebra.SpecialLinear2) : Polynomial ℂ:=
  orbitLinearPolynomial A 0*orbitLinearPolynomial B 1-
    orbitLinearPolynomial A 1*orbitLinearPolynomial B 0

theorem orbitLinearPolynomial_eval (A : Auxiliary.Algebra.SpecialLinear2) (i : Fin 2) (z : ℂ) :
    (orbitLinearPolynomial A i).eval z=A i 0*z+A i 1:=by simp [orbitLinearPolynomial]

theorem orbitPairPolynomial_eval (A B : Auxiliary.Algebra.SpecialLinear2) (z : ℂ) :
    (orbitPairPolynomial A B).eval z=
      complexWedge (Matrix.SpecialLinearGroup.toGL A • complexProjectiveVector (z : ExtendedComplex))
        (Matrix.SpecialLinearGroup.toGL B • complexProjectiveVector (z : ExtendedComplex)):=by
  rw [orbitPairPolynomial,Polynomial.eval_sub,Polynomial.eval_mul,Polynomial.eval_mul,
    orbitLinearPolynomial_eval,orbitLinearPolynomial_eval,orbitLinearPolynomial_eval,orbitLinearPolynomial_eval,
    specialLinear_vector_formula,specialLinear_vector_formula]
  simp [complexWedge,complexProjectiveVector]

/-- Equality of projective points is exactly vanishing of their arbitrary nonzero homogeneous wedge. -/
theorem complexWedge_eq_zero_iff_projectivePoint (v w : Fin 2→ℂ) (hv : v≠0) (hw : w≠0) :
    complexWedge v w=0 ↔ complexProjectivePoint v=complexProjectivePoint w:=by
  obtain ⟨a,ha⟩:=exists_unit_smul_projectiveVector v hv
  obtain ⟨b,hb⟩:=exists_unit_smul_projectiveVector w hw
  have he:=complexWedge_projectiveVector_eq_zero_iff (complexProjectivePoint v) (complexProjectivePoint w)
  rw [←ha,←hb,complexWedge_units_smul] at he
  simpa only [mul_eq_zero,Units.ne_zero,false_or] using he

theorem orbitPairPolynomial_eval_eq_zero_iff (A B : Auxiliary.Algebra.SpecialLinear2) (z : ℂ) :
    (orbitPairPolynomial A B).eval z=0 ↔
      (mobiusSpecialLinearProjection A).val (z : ExtendedComplex)=
        (mobiusSpecialLinearProjection B).val (z : ExtendedComplex):=by
  rw [orbitPairPolynomial_eval]
  rw [complexWedge_eq_zero_iff_projectivePoint _ _
    ((smul_ne_zero_iff_ne _).mpr (complexProjectiveVector_ne_zero _))
    ((smul_ne_zero_iff_ne _).mpr (complexProjectiveVector_ne_zero _))]
  rw [←specialLinear_projective_point _ _ (complexProjectiveVector_ne_zero _),
    ←specialLinear_projective_point _ _ (complexProjectiveVector_ne_zero _),complexProjectivePoint_vector]

/-- Different genuine Mobius transformations give a nonzero projective-difference polynomial. -/
theorem orbitPairPolynomial_ne_zero (A B : Auxiliary.Algebra.SpecialLinear2)
    (hab : mobiusSpecialLinearProjection A≠mobiusSpecialLinearProjection B) : orbitPairPolynomial A B≠0:=by
  intro he
  apply hab
  apply Fuchsian.mobius_ext_on_halfPlane
  intro z
  apply (orbitPairPolynomial_eval_eq_zero_iff A B (z : ℂ)).mp
  rw [he]
  simp

/-- The polynomial numerator of the original ordered cross-ratio of four actual orbit maps. -/
def orbitRatioNumerator (A B C D : Auxiliary.Algebra.SpecialLinear2) : Polynomial ℂ:=
  orbitPairPolynomial A C*orbitPairPolynomial B D

/-- The polynomial denominator retains the geometric ordered cross-ratio convention. -/
def orbitRatioDenominator (A B C D : Auxiliary.Algebra.SpecialLinear2) : Polynomial ℂ:=
  orbitPairPolynomial A B*orbitPairPolynomial C D

/-- The actual extended-plane cross-ratio is a genuine rational polynomial quotient even at poles of individual orbit maps. -/
theorem orbitCrossRatio_polynomial (A B C D : Auxiliary.Algebra.SpecialLinear2) (z : ℂ) :
    extendedCrossRatio ((mobiusSpecialLinearProjection A).val (z : ExtendedComplex))
      ((mobiusSpecialLinearProjection B).val (z : ExtendedComplex))
      ((mobiusSpecialLinearProjection C).val (z : ExtendedComplex))
      ((mobiusSpecialLinearProjection D).val (z : ExtendedComplex))=
        (orbitRatioNumerator A B C D).eval z/(orbitRatioDenominator A B C D).eval z:=by
  have hp (M : Auxiliary.Algebra.SpecialLinear2) : (mobiusSpecialLinearProjection M).val (z : ExtendedComplex)=
      complexProjectivePoint (Matrix.SpecialLinearGroup.toGL M • complexProjectiveVector (z : ExtendedComplex)):=by
    rw [←specialLinear_projective_point M _ (complexProjectiveVector_ne_zero _),complexProjectivePoint_vector]
  rw [hp A,hp B,hp C,hp D,extendedCrossRatio_projective _ _ _ _
    ((smul_ne_zero_iff_ne _).mpr (complexProjectiveVector_ne_zero _))
    ((smul_ne_zero_iff_ne _).mpr (complexProjectiveVector_ne_zero _))
    ((smul_ne_zero_iff_ne _).mpr (complexProjectiveVector_ne_zero _))
    ((smul_ne_zero_iff_ne _).mpr (complexProjectiveVector_ne_zero _))]
  simp only [homogeneousCrossRatio,orbitRatioNumerator,orbitRatioDenominator,
    Polynomial.eval_mul,orbitPairPolynomial_eval]

/-- The rational denominator is nonzero under precisely the required distinct-map pair conditions. -/
theorem orbitRatioDenominator_ne_zero (A B C D : Auxiliary.Algebra.SpecialLinear2)
    (hab : mobiusSpecialLinearProjection A≠mobiusSpecialLinearProjection B)
    (hcd : mobiusSpecialLinearProjection C≠mobiusSpecialLinearProjection D) : orbitRatioDenominator A B C D≠0:=
  mul_ne_zero (orbitPairPolynomial_ne_zero A B hab) (orbitPairPolynomial_ne_zero C D hcd)

/-- Every nonconstant actual ordered orbit cross-ratio has a genuine Euclidean area-zero real locus. -/
theorem orbitCrossRatio_real_locus_volume_zero (A B C D : Auxiliary.Algebra.SpecialLinear2)
    (hab : mobiusSpecialLinearProjection A≠mobiusSpecialLinearProjection B)
    (hcd : mobiusSpecialLinearProjection C≠mobiusSpecialLinearProjection D)
    (hn : ¬∃c : ℂ,orbitRatioNumerator A B C D=Polynomial.C c*orbitRatioDenominator A B C D) :
    volume {z : ℂ | (extendedCrossRatio ((mobiusSpecialLinearProjection A).val (z : ExtendedComplex))
      ((mobiusSpecialLinearProjection B).val (z : ExtendedComplex))
      ((mobiusSpecialLinearProjection C).val (z : ExtendedComplex))
      ((mobiusSpecialLinearProjection D).val (z : ExtendedComplex))).im=0}=0:=by
  simp only [orbitCrossRatio_polynomial]
  exact Auxiliary.Analysis.rational_real_locus_volume_zero _ _ (orbitRatioDenominator_ne_zero A B C D hab hcd) hn


/-- Distinct numerator pairs give the nonzero polynomial needed to exclude the zero constant. -/
theorem orbitRatioNumerator_ne_zero (A B C D : Auxiliary.Algebra.SpecialLinear2)
    (hac : mobiusSpecialLinearProjection A≠mobiusSpecialLinearProjection C)
    (hbd : mobiusSpecialLinearProjection B≠mobiusSpecialLinearProjection D) : orbitRatioNumerator A B C D≠0:=
  mul_ne_zero (orbitPairPolynomial_ne_zero A C hac) (orbitPairPolynomial_ne_zero B D hbd)

/-- At a finite fixed point of the third map, a nonzero constant ratio forces one of the other maps to fix that same actual point. -/
theorem constantOrbitRatio_common_fixed_at (A B C : Auxiliary.Algebra.SpecialLinear2) (c : ℂ) (hc : c≠0)
    (hpoly : orbitRatioNumerator 1 A B C=Polynomial.C c*orbitRatioDenominator 1 A B C)
    (z : ℂ) (hB : (mobiusSpecialLinearProjection B).val (z : ExtendedComplex)=(z : ExtendedComplex)) :
    (mobiusSpecialLinearProjection A).val (z : ExtendedComplex)=(z : ExtendedComplex) ∨
      (mobiusSpecialLinearProjection C).val (z : ExtendedComplex)=(z : ExtendedComplex):=by
  have h1B : (orbitPairPolynomial 1 B).eval z=0:=by
    apply (orbitPairPolynomial_eval_eq_zero_iff 1 B z).mpr
    simpa only [map_one,Subgroup.coe_one,Equiv.Perm.one_apply] using hB.symm
  have he:=congrArg (fun p : Polynomial ℂ=>p.eval z) hpoly
  simp only [orbitRatioNumerator,orbitRatioDenominator,Polynomial.eval_mul,Polynomial.eval_C,h1B,zero_mul] at he
  have hd : (orbitPairPolynomial 1 A).eval z*(orbitPairPolynomial B C).eval z=0:=
    (mul_eq_zero.mp he.symm).resolve_left hc
  rcases mul_eq_zero.mp hd with hf|hh
  · left
    have hf':=(orbitPairPolynomial_eval_eq_zero_iff 1 A z).mp hf
    simpa only [map_one,Subgroup.coe_one,Equiv.Perm.one_apply] using hf'.symm
  · right
    exact ((orbitPairPolynomial_eval_eq_zero_iff B C z).mp hh).symm.trans hB

/-- Every actual disc-preserving original map has a finite fixed point; the affine branch fixes zero. -/
theorem _root_.LowDimensionalTopology.Geometry.Fuchsian.UnitDiscFuchsianGroup.exists_finite_fixed {H : Subgroup
    complexMobiusGroup}
    (P : Fuchsian.UnitDiscFuchsianGroup H) (g : H) :
    ∃z : ℂ,g.val.val (z : ExtendedComplex)=(z : ExtendedComplex):=by
  obtain ⟨A,hA⟩:=mobiusSpecialLinearProjection_surjective g.val
  have hp : fractionalLinear (Matrix.SpecialLinearGroup.toGL A) ''
    Hyperbolic.extendedUnitDisc=Hyperbolic.extendedUnitDisc:=by
    rw [←specialLinear_projection_coe,hA]
    exact P.image_eq g
  obtain ⟨hb,_,_⟩:=Hyperbolic.specialLinear_disc_coefficients A hp
  by_cases hc : A 1 0=0
  · refine ⟨0,?_⟩
    have hb0 : A 0 1=0:=by rw [hb,hc];simp
    have he:=(Mobius.Classification.specialLinear_fixes_zero_iff A).mpr hb0
    change (mobiusSpecialLinearProjection A).val ((0 : ℂ) : ExtendedComplex)=((0 : ℂ) : ExtendedComplex) at he
    rwa [hA] at he
  · have hb0 : A 0 1≠0:=by rw [hb];exact (map_ne_zero (starRingEnd ℂ)).mpr hc
    obtain ⟨z,_,hz⟩:=specialLinear_exists_nonzero_finite_fixed A hb0 hc
    exact ⟨z,by rwa [hA] at hz⟩

/-- A constant actual triple-orbit ratio in the disc forces two genuine original transformations to share a finite fixed point. -/
theorem unitDisc_constantOrbitRatio_common_fixed {H : Subgroup complexMobiusGroup}
    (P : Fuchsian.UnitDiscFuchsianGroup H) (f g h : H) (A B C : Auxiliary.Algebra.SpecialLinear2)
    (hA : mobiusSpecialLinearProjection A=f.val) (hB : mobiusSpecialLinearProjection B=g.val)
    (hC : mobiusSpecialLinearProjection C=h.val) (hg : g≠1) (hfh : f≠h)
    (hconstant : ∃c : ℂ,orbitRatioNumerator 1 A B C=Polynomial.C c*orbitRatioDenominator 1 A B C) :
    ∃z : ℂ,g.val.val (z : ExtendedComplex)=(z : ExtendedComplex) ∧
      (f.val.val (z : ExtendedComplex)=(z : ExtendedComplex) ∨ h.val.val (z : ExtendedComplex)=(z :
        ExtendedComplex)):=by
  obtain ⟨c,hc⟩:=hconstant
  have hnum : orbitRatioNumerator 1 A B C≠0:=by
    apply orbitRatioNumerator_ne_zero
    · rw [map_one,hB]
      exact fun he=>hg (Subtype.val_injective he.symm)
    · rw [hA,hC]
      exact fun he=>hfh (Subtype.val_injective he)
  have hc0 : c≠0:=by intro he;rw [he,Polynomial.C_0,zero_mul] at hc;exact hnum hc
  obtain ⟨z,hz⟩:=P.exists_finite_fixed g
  refine ⟨z,hz,?_⟩
  have hzB : (mobiusSpecialLinearProjection B).val (z : ExtendedComplex)=(z : ExtendedComplex):=by rwa [hB]
  have he:=constantOrbitRatio_common_fixed_at A B C c hc0 hc z hzB
  simpa only [hA,hC] using he


/-- Euclidean null sets have zero genuine hyperbolic density area in the actual finite disc coordinate. -/
theorem _root_.LowDimensionalTopology.Geometry.Fuchsian.UnitDiscFuchsianGroup.finiteCoordinate_area_zero_of_volume_zero
    {H : Subgroup complexMobiusGroup} (P : Fuchsian.UnitDiscFuchsianGroup H)
    (R : Set ℂ) (hR : MeasurableSet R) (hzero : volume R=0) :
    P.area {w | (P.finiteCoordinate w : ℂ)∈R}=0:=by
  have hS : MeasurableSet {w | (P.finiteCoordinate w : ℂ)∈R}:=
    hR.preimage (Complex.UnitDisc.continuous_coe.comp P.finiteCoordinate.continuous).measurable
  rw [P.area_apply _ hS]
  change Hyperbolic.discAreaMeasure (((↑) : Complex.UnitDisc→ℂ) ''
    (P.finiteCoordinate '' {w | (P.finiteCoordinate w : ℂ)∈R}))=0
  have hnull : Hyperbolic.discAreaMeasure R=0:=withDensity_absolutelyContinuous volume _ hzero
  apply measure_mono_null _ hnull
  rintro _ ⟨z,⟨w,hw,rfl⟩,rfl⟩
  exact hw

/-- The original model's genuine density area obeys the same nonconstant rational real-locus exception theorem. -/
theorem _root_.LowDimensionalTopology.Geometry.Fuchsian.UnitDiscFuchsianGroup.rational_real_locus_area_zero
    {H : Subgroup complexMobiusGroup} (P : Fuchsian.UnitDiscFuchsianGroup H) (p q : Polynomial ℂ)
    (hq : q≠0) (hn : ¬∃c : ℂ,p=Polynomial.C c*q) :
    P.area {w | (p.eval (P.finiteCoordinate w : ℂ)/q.eval (P.finiteCoordinate w : ℂ)).im=0}=0:=by
  apply P.finiteCoordinate_area_zero_of_volume_zero {z : ℂ | (p.eval z/q.eval z).im=0}
  · exact measurableSet_eq_fun
      (Complex.continuous_im.measurable.comp (p.continuous.measurable.div q.continuous.measurable)) measurable_const
  · exact Auxiliary.Analysis.rational_real_locus_volume_zero p q hq hn

end LowDimensionalTopology.Geometry.Mobius
