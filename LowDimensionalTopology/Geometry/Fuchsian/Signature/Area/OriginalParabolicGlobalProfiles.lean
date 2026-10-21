/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.CornerCycle.OriginalRawEllipticOrderLists
public import LowDimensionalTopology.Geometry.Fuchsian.Signature.Area.OriginalCompletionWeightedEuler
public import LowDimensionalTopology.Geometry.Fuchsian.Covolume.FiniteAreaEllipticClasses
public import LowDimensionalTopology.Geometry.Fuchsian.CyclicClass.CyclicClassConjugacy
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.CornerCycle.OriginalRawCuspClasses
public import LowDimensionalTopology.Geometry.Fuchsian.Signature.CofiniteSignatures
public import LowDimensionalTopology.Geometry.Surfaces.Topology.Genus.CanonicalHandleSeparation
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open Set Topology
open scoped Complex.UnitDisc
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
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
open scoped Classical
local instance originalGlobalProfilesSphereMeasurable : MeasurableSpace Mobius.ExtendedComplex:=borel Mobius.ExtendedComplex
local instance originalGlobalProfilesSphereBorel : BorelSpace Mobius.ExtendedComplex:=⟨rfl⟩

/-- Any genuine original fundamental domain with finite area below pi and an actual parabolic has the complete original elliptic-order alternatives, without a normalized or convex-domain hypothesis. -/
theorem finite_area_parabolic_geometricDisc_elliptic_profiles
    {H : Subgroup Mobius.complexMobiusGroup}
    (D₀ : FuchsianDisc H) (F : Set (fuchsianGeometricDomain D₀).carrier)
    (hF : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain H (fuchsianGeometricDomain D₀).carrier (geometricModelArea D₀) F)
    (harea : geometricModelArea D₀ F≠⊤) (hsmall : (geometricModelArea D₀ F).toReal<Real.pi)
    (hpar : ∃f∈H,_root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic f) :
    let _originalGlobalProfilesActualFinite : Finite (FuchsianCyclicConjugacyClasses D₀ .elliptic):=
      finite_area_elliptic_classes_finite D₀ F hF harea
    ((∃q : ℕ,3≤q ∧ (fuchsianEllipticOrderList D₀).Perm [2,q]) ∨
      (∃q : ℕ,(q=3 ∨ q=4 ∨ q=5) ∧ (fuchsianEllipticOrderList D₀).Perm [3,q])) := by
  let _originalGlobalProfilesActualFinite : Finite (FuchsianCyclicConjugacyClasses D₀ .elliptic):=
    finite_area_elliptic_classes_finite D₀ F hF harea
  let P:=geometricDiscData D₀
  let q:=geometricDiscNormalizer D₀
  obtain ⟨w,hw,ha⟩:=finite_area_geometricDisc_dirichlet D₀ F hF harea
  have hD:=dirichletDomain_isConvexFuchsianPolygon P w hw
  have hA : P.area (dirichletDomain P w)=geometricModelArea D₀ F:=
    geometricDisc_fundamental_area_eq_original D₀ F hF hD.locallyFinite.fundamental
  have hsmall' : (P.area (dirichletDomain P w)).toReal<Real.pi:=by rwa [hA]
  obtain ⟨f,hfH,hf⟩:=hpar
  let f' : geometricDiscGroup D₀:=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugateEquivalence q H ⟨f,hfH⟩
  have hf' : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic f'.val:=
    (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusParabolic_isConj (isConj_iff.mpr ⟨q,rfl⟩)).mp hf
  let _originalGlobalProfilesNormalizedFinite : Finite (FuchsianCyclicConjugacyClasses P.asFuchsianDisc .elliptic):=
    finite_sided_polygon_elliptic_classes_finite hD (finite_area_polygon_finite_sides hD ha)
  let _originalGlobalProfilesConjugateFinite : Finite (FuchsianCyclicConjugacyClasses (D₀.nielsenConjugate q) .elliptic):=
    fuchsianCyclicClassConjugacyEquiv_finite D₀ .elliptic q
  have hperm : (fuchsianEllipticOrderList D₀).Perm (fuchsianEllipticOrderList P.asFuchsianDisc):=by
    have h:=fuchsianEllipticOrderList_global_conjugation D₀ q
    simpa only [P,geometricDiscData_asFuchsianDisc,q] using h
  have hp:=finite_area_parabolic_original_elliptic_profiles hD ha f' hf' hsmall'
  rcases hp with ⟨m,hm,hmp⟩|⟨m,hm,hmp⟩
  · exact Or.inl ⟨m,hm,hperm.trans hmp⟩
  · exact Or.inr ⟨m,hm,hperm.trans hmp⟩

end LowDimensionalTopology.Geometry.Fuchsian

/- BEGIN OWN ORIGINAL SMALL PARABOLIC SIGNATURE -/
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
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
open LowDimensionalTopology.Geometry.Surfaces.CyclicSurface
open LeanEval.Topology.ClassificationOfSurfaces.Moise
open scoped Classical
local instance originalSmallParabolicSphereMeasurable : MeasurableSpace Mobius.ExtendedComplex:=borel Mobius.ExtendedComplex
local instance originalSmallParabolicSphereBorel : BorelSpace Mobius.ExtendedComplex:=⟨rfl⟩

/-- The original group with a true finite-area domain below pi and a parabolic has its actual genus-zero, one-cusp signature and the complete elliptic-order alternatives. -/
theorem finite_area_parabolic_original_small_signature
    {H : Subgroup Mobius.complexMobiusGroup}
    (D₀ : FuchsianDisc H) (F : Set (fuchsianGeometricDomain D₀).carrier)
    (hF : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain H (fuchsianGeometricDomain D₀).carrier (geometricModelArea D₀) F)
    (harea : geometricModelArea D₀ F≠⊤) (hsmall : (geometricModelArea D₀ F).toReal<Real.pi)
    (hpar : ∃f∈H,_root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic f) :
    let _originalSmallParabolicActualFinite : Finite (FuchsianCyclicConjugacyClasses D₀ .elliptic):=
      finite_area_elliptic_classes_finite D₀ F hF harea
    HasCofiniteFuchsianSignature D₀ 0 (fuchsianEllipticOrderList D₀) 1 ∧
      ((∃q : ℕ,3≤q ∧ (fuchsianEllipticOrderList D₀).Perm [2,q]) ∨
        (∃q : ℕ,(q=3 ∨ q=4 ∨ q=5) ∧ (fuchsianEllipticOrderList D₀).Perm [3,q])) := by
  let originalSmallParabolicActualFinite : Finite (FuchsianCyclicConjugacyClasses D₀ .elliptic):=
    finite_area_elliptic_classes_finite D₀ F hF harea
  let P:=geometricDiscData D₀
  let q:=geometricDiscNormalizer D₀
  obtain ⟨w₀,hw₀,ha₀⟩:=finite_area_geometricDisc_dirichlet D₀ F hF harea
  obtain ⟨w,_hw,hL,ha,hparL⟩:=finite_area_exists_dirichlet_all_ideal_parabolic
    (dirichletDomain_fundamental P w₀ hw₀) ha₀
  have hA : P.area (dirichletDomain P w)=geometricModelArea D₀ F:=
    geometricDisc_fundamental_area_eq_original D₀ F hF hL.locallyFinite.fundamental
  have hsmallL : (P.area (dirichletDomain P w)).toReal<Real.pi:=by rwa [hA]
  obtain ⟨f,hfH,hf⟩:=hpar
  let f' : geometricDiscGroup D₀:=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugateEquivalence q H ⟨f,hfH⟩
  have hf' : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic f'.val:=
    (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusParabolic_isConj (isConj_iff.mpr ⟨q,rfl⟩)).mp hf
  obtain ⟨J,e,hc,hv,hs,g,hg,hg0,hzero,_horders⟩:=
    finite_area_parabolic_original_raw_profiles hL ha f' hf' hsmallL
  subst g
  obtain ⟨n,S,hr,_hint⟩:=finite_area_polygon_actual_cyclic_model hL ha
  have hgenus : _root_.LowDimensionalTopology.Geometry.Surfaces.HasTopologicalGenus (FuchsianCuspCompletion D₀) 0:=by
    obtain ⟨G⟩:=hg
    exact ⟨(originalCyclicCompletionHomeomorph D₀ hL ha J hc hv e hs S hr hparL).symm.trans G⟩
  have hcusps : 1=Nat.card (FuchsianCyclicConjugacyClasses D₀ .parabolic):=
    hzero.symm.trans (originalRawZeroClassCount_eq_cusps D₀ hL ha J hc hv e hs S hr hparL)
  refine ⟨⟨originalSmallParabolicActualFinite,finite_area_parabolic_classes_finite D₀ F hF harea,
    _root_.LowDimensionalTopology.Geometry.Surfaces.HandleSeparation.hasTopologicalGenus_compactSpace hgenus,hgenus,List.Perm.refl _,hcusps⟩,?_⟩
  exact finite_area_parabolic_geometricDisc_elliptic_profiles D₀ F hF harea hsmall ⟨f,hfH,hf⟩

end LowDimensionalTopology.Geometry.Fuchsian

/- Source: (printed 294; PDF 304). -/
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
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
open scoped Classical
attribute [local instance] originalSmallParabolicSphereMeasurable originalSmallParabolicSphereBorel

/-- The original actual area inequality alone gives the genuine small-area parabolic signature and its complete elliptic-order alternatives. -/
theorem small_area_parabolic_signature_classification
    {H : Subgroup Mobius.complexMobiusGroup}
    (D₀ : FuchsianDisc H) (F : Set (fuchsianGeometricDomain D₀).carrier)
    (hF : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain H (fuchsianGeometricDomain D₀).carrier (geometricModelArea D₀) F)
    (hsmall : geometricModelArea D₀ F<ENNReal.ofReal Real.pi)
    (hpar : ∃f∈H,_root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic f) :
    let _originalSmallAreaEllipticFinite : Finite (FuchsianCyclicConjugacyClasses D₀ .elliptic):=
      finite_area_elliptic_classes_finite D₀ F hF (ne_of_lt (hsmall.trans_le le_top))
    HasCofiniteFuchsianSignature D₀ 0 (fuchsianEllipticOrderList D₀) 1 ∧
      ((∃q : ℕ,3≤q ∧ (fuchsianEllipticOrderList D₀).Perm [2,q]) ∨
        (∃q : ℕ,(q=3 ∨ q=4 ∨ q=5) ∧ (fuchsianEllipticOrderList D₀).Perm [3,q])) := by
  have harea : geometricModelArea D₀ F≠⊤:=ne_of_lt (hsmall.trans_le le_top)
  have hreal : (geometricModelArea D₀ F).toReal<Real.pi:=by
    have h:=(ENNReal.toReal_lt_toReal harea ENNReal.ofReal_ne_top).mpr hsmall
    simpa only [ENNReal.toReal_ofReal Real.pi_pos.le] using h
  exact finite_area_parabolic_original_small_signature D₀ F hF harea hreal hpar

end LowDimensionalTopology.Geometry.Fuchsian
