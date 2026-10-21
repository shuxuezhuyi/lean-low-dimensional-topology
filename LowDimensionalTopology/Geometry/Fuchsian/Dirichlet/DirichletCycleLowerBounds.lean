/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Mobius.Circle.IdealBoundaryAction
public import LowDimensionalTopology.Geometry.Mobius.Circle.GeometricDisc
public import LowDimensionalTopology.Geometry.Hyperbolic.Models.Disc.ExtendedCarrier
public import LowDimensionalTopology.Geometry.Fuchsian.Elementary.CyclicOrbitCircles
public import LowDimensionalTopology.Geometry.Fuchsian.Dirichlet.DirichletGeometry
public import LowDimensionalTopology.Geometry.Fuchsian.Displacement.EllipticFree.EllipticFreeDisplacementBounds
@[expose] public section
noncomputable section
open Set
open scoped UpperHalfPlane MatrixGroups OnePoint
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Surfaces LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Inversive LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- The fixed genuine Cayley transformation sends the original disc to the whole half-plane. -/
theorem radius_cayley_inverse_image :
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius⁻¹).val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc=_root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet := by
  rw [←cayleyMobius_image_openHalfPlane,Set.image_image]
  change (fun z : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex=>_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius⁻¹•(_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius•z)) '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet=_root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet
  simp only [inv_smul_smul,Set.image_id']

/-- The native metric coordinate is exactly the genuine original sphere transformation. -/
theorem radius_coordinate_sphere {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (z : P.domain.carrier) :
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius⁻¹).val z.val=(((P.halfPlaneCoordinate z):ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) := by
  have hz : (((P.finiteCoordinate
    z:Complex.UnitDisc):ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)=z.val:=
    ((congrArg Subtype.val (_root_.LowDimensionalTopology.Geometry.Surfaces.discFiniteHomeomorph.symm_apply_apply
      z)).symm.trans
      (_root_.LowDimensionalTopology.Geometry.Surfaces.discFiniteHomeomorph_symm_coe (P.finiteCoordinate z))).symm
  apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius.val.injective
  change _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius.val (_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius.val.symm z.val)=_
  rw [Equiv.apply_symm_apply,_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius_apply,_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedCayley_halfPlane,P.halfPlaneCoordinate_cayley]
  exact hz.symm

/-- Conjugation of every original disc group element preserves the entire actual half-plane. -/
theorem radius_conjugate_preserves_halfPlane {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) :
    ∀f∈_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius⁻¹ H,
      f.val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet=_root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet := by
  rintro f ⟨g,hg,rfl⟩
  change (_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius⁻¹*g*(_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius⁻¹)⁻¹).val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet=_root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet
  rw [←radius_cayley_inverse_image,_root_.LowDimensionalTopology.Geometry.Mobius.stableAxis_conjugate_image,P.image_eq
    ⟨g,hg⟩,
    radius_cayley_inverse_image]

/-- Literal original orbit points map to literal orbit points of the conjugated group. -/
theorem radius_conjugate_orbit {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (z x : P.domain.carrier) (hx : x∈MulAction.orbit H z) :
    (((P.halfPlaneCoordinate x):ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)∈
      MulAction.orbit (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius⁻¹ H)
        (((P.halfPlaneCoordinate z):ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) := by
  obtain ⟨g,hg⟩:=hx
  refine ⟨⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius⁻¹*g.val*(_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius⁻¹)⁻¹,⟨g.val,g.property,rfl⟩⟩,?_⟩
  rw [←radius_coordinate_sphere P x,←radius_coordinate_sphere P z]
  change _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius⁻¹•(g.val•((_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius⁻¹)⁻¹•(_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius⁻¹•z.val)))=
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius⁻¹•x.val
  rw [inv_smul_smul]
  exact congrArg (_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius⁻¹).val (congrArg Subtype.val hg)

/-- The fully native original-disc cyclic circle obstruction, with all frame
changes constructed from the genuine Cayley map. -/
theorem cyclic_circle_three {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (hcyc : IsCyclic H) (hno :
      ∀f∈H,¬_root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic f)
    (z w x y u : P.domain.carrier) (r : ℝ)
    (hx : x∈MulAction.orbit H z) (hy : y∈MulAction.orbit H z) (hu : u∈MulAction.orbit H z)
    (hxd : P.hyperbolicDist w x=r) (hyd : P.hyperbolicDist w y=r) (hud : P.hyperbolicDist w u=r) :
    x=y ∨ x=u ∨ y=u := by
  let K:=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius⁻¹ H
  have hKcyc : IsCyclic K:=(_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugateEquivalence _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius⁻¹ H).isCyclic.mp hcyc
  have hKno : ∀f∈K,¬_root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic f:=by
    rintro f ⟨g,hg,rfl⟩
    change ¬_root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius⁻¹*g*(_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius⁻¹)⁻¹)
    rw [_root_.LowDimensionalTopology.Geometry.Mobius.mobiusElliptic_conjugation]
    exact hno g hg
  have h:=cyclicMobius_halfPlane_circle_three K hKcyc hKno (radius_conjugate_preserves_halfPlane P)
    (P.halfPlaneCoordinate z) (P.halfPlaneCoordinate w) (P.halfPlaneCoordinate x)
    (P.halfPlaneCoordinate y) (P.halfPlaneCoordinate u) r
    (radius_conjugate_orbit P z x hx) (radius_conjugate_orbit P z y hy) (radius_conjugate_orbit P z u hu)
    hxd hyd hud
  rcases h with h | h | h
  · exact Or.inl (P.halfPlaneCoordinate.injective h)
  · exact Or.inr (Or.inl (P.halfPlaneCoordinate.injective h))
  · exact Or.inr (Or.inr (P.halfPlaneCoordinate.injective h))

/-- The real lift of an actual conjugated original group map intertwines the
native hyperbolic coordinate exactly. -/
theorem radius_coordinate_action_lift {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (f : H) (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A=_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius⁻¹*f.val*(_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius⁻¹)⁻¹) (x : P.domain.carrier) :
    A•P.halfPlaneCoordinate x=P.halfPlaneCoordinate (f•x) := by
  apply UpperHalfPlane.ext
  apply OnePoint.coe_injective
  rw [←_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_action,hA,←radius_coordinate_sphere P
    (f•x),←radius_coordinate_sphere P x]
  change _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius⁻¹•(f.val•((_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius⁻¹)⁻¹•(_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius⁻¹•x.val)))=
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius⁻¹•(f•x).val
  rw [inv_smul_smul]
  rfl

/-- Restriction keeps the original geometric disc and its actual proper action. -/
theorem radius_restrict {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P :
  UnitDiscFuchsianGroup H)
    (K : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (hKH :
      K≤H) : UnitDiscFuchsianGroup K where
  invariant := fun g z hz=>P.invariant ⟨g.val,hKH g.property⟩ z hz
  discontinuous := by
    intro T hTc hTD
    let i : K→H:=fun g=>⟨g.val,hKH g.property⟩
    have hi : Function.Injective i:=by
      intro a b hab
      exact Subtype.ext (congrArg (fun x : H=>x.val) hab)
    change (i ⁻¹' {g : H | (g.val.val '' T ∩ T).Nonempty}).Finite
    exact Set.Finite.preimage hi.injOn (P.discontinuous T hTc hTD)

/-- Three distinct points on one actual circle force the generating pair to
be non-elementary; cyclicity is deduced, never supplied as a conclusion. -/
theorem radius_pair_nonElementary {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (hno : ∀f∈H,¬_root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic f)
    (z w : P.domain.carrier) (f g : H) (r : ℝ)
    (hz : P.hyperbolicDist w z=r) (hf : P.hyperbolicDist w (f•z)=r)
    (hg : P.hyperbolicDist w (g•z)=r)
    (hzf : z≠f•z) (hzg : z≠g•z) (hfg : f•z≠g•z) :
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure ({f.val,g.val}:Set _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)) := by
  let K:=Subgroup.closure ({f.val,g.val}:Set _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
  have hKH : K≤H:=(Subgroup.closure_le H).2 (by intro x hx;rcases hx with rfl|rfl;exact f.property;exact g.property)
  let PK:=radius_restrict P K hKH
  have hKno : ∀u∈K,¬_root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic u:=fun u hu=>hno u (hKH hu)
  intro he
  have hcyc : IsCyclic K:=_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.elementary_noElliptic_isCyclic PK.asFuchsianDisc he hKno
  let fK : K:=⟨f.val,Subgroup.subset_closure (by simp)⟩
  let gK : K:=⟨g.val,Subgroup.subset_closure (by simp)⟩
  have h:=cyclic_circle_three PK hcyc hKno z w z (f•z) (g•z) r
    ⟨1,one_smul _ _⟩ ⟨fK,rfl⟩ ⟨gK,rfl⟩ hz hf hg
  exact h.elim hzf (fun hh=>hh.elim hzg hfg)

/-- Elliptic freedom makes the original action free at every interior point. -/
theorem radius_stabilizer_trivial {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (hno : ∀f∈H,¬_root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic f)
    (z : P.domain.carrier) (g : H) (hfix : g•z=z) : g=1 := by
  by_contra hne
  exact hno g.val g.property (P.fixed_interior_elliptic z g hne hfix)

/-- The actual elliptic-free displacement product, in the original disc's
native coordinate, for every genuinely non-elementary generating pair. -/
theorem radius_pair_displacement {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (hno : ∀f∈H,¬_root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic f)
    (f g : H)
    (hPair : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure ({f.val,g.val}:Set
      _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)))
    (x : P.domain.carrier) :
    1≤Real.sinh (P.hyperbolicDist x (f•x)/2)*Real.sinh (P.hyperbolicDist x (g•x)/2) := by
  let q:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius⁻¹
  let K:=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q H
  have hKE : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsEllipticFree K:=(show
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsEllipticFree H from fun u=>hno u.val
    u.property).conjugation q
  have hLift : ∀u∈K,∃A : Matrix.SpecialLinearGroup (Fin 2) ℝ,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A=u:=by
    intro u hu
    exact mobius_preserves_halfPlane_exists_SL u (radius_conjugate_preserves_halfPlane P u hu)
  have hKD : _root_.LowDimensionalTopology.Geometry.Mobius.HasInvariantComplexDisc K:=
    ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet,by
      rw [←radius_cayley_inverse_image]
      exact _root_.LowDimensionalTopology.Geometry.DiscreteGroups.extendedUnitDisc_isComplexOpenDisc.image _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius⁻¹,
      fun u=>radius_conjugate_preserves_halfPlane P u.val u.property⟩
  have hfm : q*f.val*q⁻¹∈K:=⟨f.val,f.property,rfl⟩
  have hgm : q*g.val*q⁻¹∈K:=⟨g.val,g.property,rfl⟩
  obtain ⟨A,hAf⟩:=hLift _ hfm
  obtain ⟨B,hBg⟩:=hLift _ hgm
  have hPairK:=hPair.conjugation q
  rw [_root_.LowDimensionalTopology.Geometry.DiscreteGroups.jorgensen_generated_conjugation,←hAf,←hBg] at hPairK
  have hb:=hEllipticFree_displacement_bound K hKD hKE hLift A B (hAf ▸ hfm) (hBg ▸ hgm)
    hPairK (P.halfPlaneCoordinate x)
  rw [radius_coordinate_action_lift P f A hAf x,radius_coordinate_action_lift P g B hBg x] at hb
  exact hb

/-- Distinct original elements have distinct values at every interior point
of an elliptic-free group. -/
theorem radius_orbit_injective {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (hno : ∀f∈H,¬_root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic f)
    (z : P.domain.carrier) : Function.Injective (fun g : H=>g•z) := by
  intro a b hab
  change a•z=b•z at hab
  have hfix : (b⁻¹*a)•z=z:=by rw [mul_smul,hab,inv_smul_smul]
  have ho:=radius_stabilizer_trivial P hno z (b⁻¹*a) hfix
  calc
    a=b*(b⁻¹*a):=by group
    _=b:=by rw [ho,mul_one]

/-- A literal Dirichlet vertex has three distinct representatives in its
original orbit, all lying on the same genuine metric circle. -/
theorem radius_vertex_three {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (hno : ∀f∈H,¬_root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic f)
    (w x : P.domain.carrier) (hx : IsFuchsianPolygonVertex P (dirichletDomain P w) x) :
    ∃f g : H,x≠f•x ∧ x≠g•x ∧ f•x≠g•x ∧
      P.hyperbolicDist w (f•x)=P.hyperbolicDist w x ∧
      P.hyperbolicDist w (g•x)=P.hyperbolicDist w x := by
  obtain ⟨a,b,ha,hb,hab,he⟩:=hx
  have hT : x∈closure (dirichletDomain P w)∩fuchsianDomainTile P (dirichletDomain P w) a∩
      fuchsianDomainTile P (dirichletDomain P w) b:=by rw [he];exact mem_singleton x
  have hac : a⁻¹•x∈closure (dirichletDomain P w):=by
    obtain ⟨y,hy,hye⟩:=hT.1.2
    rw [←hye,inv_smul_smul]
    exact hy
  have hbc : b⁻¹•x∈closure (dirichletDomain P w):=by
    obtain ⟨y,hy,hye⟩:=hT.2
    rw [←hye,inv_smul_smul]
    exact hy
  have hxc : x∈fuchsianPolygonCycle P (dirichletDomain P w) x:=⟨hT.1.1,⟨1,one_smul _ _⟩⟩
  have hca : a⁻¹•x∈fuchsianPolygonCycle P (dirichletDomain P w) x:=⟨hac,⟨a⁻¹,rfl⟩⟩
  have hcb : b⁻¹•x∈fuchsianPolygonCycle P (dirichletDomain P w) x:=⟨hbc,⟨b⁻¹,rfl⟩⟩
  have hda:=dirichlet_cycle_distance_to_center_eq P w x hca hxc
  have hdb:=dirichlet_cycle_distance_to_center_eq P w x hcb hxc
  have hfree:=radius_orbit_injective P hno x
  refine ⟨a⁻¹,b⁻¹,?_,?_,?_,?_,?_⟩
  · intro hh
    have heq : (1:H)=a⁻¹:=hfree (by simpa using hh)
    exact ha (by simpa using congrArg Inv.inv heq.symm)
  · intro hh
    have heq : (1:H)=b⁻¹:=hfree (by simpa using hh)
    exact hb (by simpa using congrArg Inv.inv heq.symm)
  · intro hh
    exact hab (inv_injective (hfree hh))
  · rw [P.hyperbolicDist_comm w (a⁻¹•x),P.hyperbolicDist_comm w x]
    exact hda
  · rw [P.hyperbolicDist_comm w (b⁻¹•x),P.hyperbolicDist_comm w x]
    exact hdb

/--
For every actual finite Dirichlet vertex. The three
required orbit points are derived from the literal adjacent closed tiles.
-/
theorem sqrt_two_le_cosh_dirichlet_vertex_distance_of_ellipticFree {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (hno : ∀f∈H,¬_root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic f)
    (w x : P.domain.carrier) (hx : IsFuchsianPolygonVertex P (dirichletDomain P w) x) :
    Real.sqrt 2≤Real.cosh (P.hyperbolicDist w x) := by
  obtain ⟨f,g,hxf,hxg,hfg,hfd,hgd⟩:=radius_vertex_three P hno w x hx
  have hpair:=radius_pair_nonElementary P hno x w f g (P.hyperbolicDist w x) rfl hfd hgd hxf hxg hfg
  have hb:=radius_pair_displacement P hno f g hpair x
  have hfdist : P.hyperbolicDist x (f•x)/2≤P.hyperbolicDist w x:=by
    have ht:=P.hyperbolicDist_triangle x w (f•x)
    rw [P.hyperbolicDist_comm x w,hfd] at ht
    linarith
  have hgdist : P.hyperbolicDist x (g•x)/2≤P.hyperbolicDist w x:=by
    have ht:=P.hyperbolicDist_triangle x w (g•x)
    rw [P.hyperbolicDist_comm x w,hgd] at ht
    linarith
  have hs:=Real.sinh_le_sinh.mpr hfdist
  have ht:=Real.sinh_le_sinh.mpr hgdist
  have hnn : 0≤Real.sinh (P.hyperbolicDist w x):=
    Real.sinh_nonneg_iff.mpr (P.hyperbolicDist_nonneg w x)
  have hgnn : 0≤Real.sinh (P.hyperbolicDist x (g•x)/2):=
    Real.sinh_nonneg_iff.mpr (div_nonneg (P.hyperbolicDist_nonneg x (g•x)) (by norm_num))
  have hp:=mul_le_mul hs ht hgnn hnn
  have hsq : (Real.sinh (P.hyperbolicDist w x))^2≥1:=by nlinarith only [hb,hp]
  have hid:=Real.cosh_sq_sub_sinh_sq (P.hyperbolicDist w x)
  apply Real.sqrt_le_iff.mpr
  exact ⟨(Real.cosh_pos _).le,by nlinarith only [hsq,hid]⟩

end LowDimensionalTopology.Geometry.Fuchsian
