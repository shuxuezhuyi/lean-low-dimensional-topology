/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.Boundary.FiniteAreaPolygonSides
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory
open scoped Complex.UnitDisc Topology UpperHalfPlane
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
local instance ellipseFinitenessSphereMeasurable : MeasurableSpace _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex := borel _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex
local instance ellipseFinitenessSphereBorel : BorelSpace _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex := ⟨rfl⟩

/-- An arbitrary original Fuchsian disc with a true finite-area fundamental domain has only finitely many actual maximal elliptic cyclic subgroup conjugacy classes. -/
theorem finite_area_elliptic_classes_finite {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D : FuchsianDisc H) (S : Set (fuchsianGeometricDomain D).carrier)
    (hS : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain H (fuchsianGeometricDomain
      D).carrier (geometricModelArea D) S)
    (harea : geometricModelArea D S≠⊤) :
    Finite (FuchsianCyclicConjugacyClasses D .elliptic) := by
  obtain ⟨w,hw,hareaW⟩:=finite_area_geometricDisc_dirichlet D S hS harea
  let P:=geometricDiscData D
  let q:=geometricDiscNormalizer D
  let e:=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugateEquivalence q H
  have hpoly:=dirichletDomain_isConvexFuchsianPolygon P w hw
  let X:=fuchsianCyclicFixedPoints D .elliptic
  let ι (p : X) : P.domain.carrier:=geometricDiscHomeomorph D ⟨p.val,p.property.1 rfl⟩
  have hι (g : H) (p : X) : ι (g•p)=e g•ι p:=by
    apply Subtype.ext
    change q.val (g.val.val p.val)=(q*g.val*q⁻¹).val (q.val p.val)
    change q•(g.val•p.val)=(q*g.val*q⁻¹)•(q•p.val)
    simp only [mul_smul,inv_smul_smul]
  have hi : Function.Injective ι:=by
    intro p r hpr
    apply Subtype.ext
    exact congrArg (fun z : (fuchsianGeometricDomain D).carrier=>z.val)
      ((geometricDiscHomeomorph D).injective hpr)
  let R : Set X:=ι ⁻¹' closure (dirichletDomain P w)
  have hR : R.Finite:=by
    apply ((finite_area_polygon_elliptic_centers_finite hpoly hareaW).preimage hi.injOn).subset
    intro p hp
    refine ⟨hp,?_⟩
    change ¬∀g : geometricDiscGroup D,g•ι p=ι p→g=1
    intro hfree
    obtain ⟨f,hfH,hf,hfix⟩:=p.property.2
    let g : H:=⟨f,hfH⟩
    have hgp : g•p=p:=Subtype.ext hfix
    have hfix' : e g•ι p=ι p:=(hι g p).symm.trans (congrArg ι hgp)
    have hge : g=1:=e.injective ((hfree (e g) hfix').trans e.map_one.symm)
    exact hf.1 (congrArg Subtype.val hge)
  have hrep (p : X) : ∃g : H,g•p∈R:=by
    have hp : ι p∈⋃g : geometricDiscGroup D,fuchsianDomainTile P (dirichletDomain P w) g:=by
      change ι p∈⋃g : geometricDiscGroup D,(fun x : P.domain.carrier=>g•x) '' closure (dirichletDomain P w)
      rw [hpoly.locallyFinite.fundamental.closure_cover]
      trivial
    obtain ⟨g,y,hy,hgy⟩:=mem_iUnion.mp hp
    change g•y=ι p at hgy
    refine ⟨e.symm g⁻¹,?_⟩
    change ι (e.symm g⁻¹•p)∈closure (dirichletDomain P w)
    have he : ι (e.symm g⁻¹•p)=y:=by
      calc
        _=e (e.symm g⁻¹)•ι p:=hι _ _
        _=g⁻¹•ι p:=congrArg (fun a : geometricDiscGroup D=>a•ι p) (e.apply_symm_apply _)
        _=y:=by rw [←hgy,inv_smul_smul]
    exact he.symm ▸ hy
  have : Finite (MulAction.orbitRel.Quotient H X):=
    finite_orbitQuotient_of_finite_representatives R hR hrep
  exact Finite.of_equiv _ (fuchsianCyclicConjugacyClassesEquiv D .elliptic).symm

/-- Both genuine maximal cyclic types have finitely many actual conjugacy classes at finite original quotient area. -/
theorem finite_area_cyclic_classes_finite {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D : FuchsianDisc H) (S : Set (fuchsianGeometricDomain D).carrier)
    (hS : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain H (fuchsianGeometricDomain
      D).carrier (geometricModelArea D) S)
    (harea : geometricModelArea D S≠⊤) (kind : FuchsianCyclicKind) :
    Finite (FuchsianCyclicConjugacyClasses D kind) := by
  cases kind
  · exact finite_area_elliptic_classes_finite D S hS harea
  · exact finite_area_parabolic_classes_finite D S hS harea


end LowDimensionalTopology.Geometry.Fuchsian
