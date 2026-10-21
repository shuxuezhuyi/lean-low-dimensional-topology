/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Auxiliary.Topology.CoveringFiberCardinality
public import Mathlib.Analysis.Complex.UpperHalfPlane.FixedPoints
public import LowDimensionalTopology.Geometry.Polygon.Hyperbolic.Quotient.PolygonIdentifiedCover
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.NativeIsometryDiscontinuity
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Topology
open scoped UpperHalfPlane MatrixGroups
namespace LowDimensionalTopology.Geometry.Fuchsian

/-- A nonidentity actual positive-determinant native isometry has at most one
physical fixed point, by Mathlib's exact elliptic fixed-point classification. -/
theorem nativePositiveGL_fixedSet_subsingleton
    (f : ℍ≃ᵢℍ) (hf : f≠1)
    (A : Matrix.GeneralLinearGroup (Fin 2) ℝ) (hA : 0<A.val.det)
    (hAct : ∀z : ℍ,f z=A • z) : Set.Subsingleton {z : ℍ | f z=z} := by
  have hAc : A∉Subgroup.center (Matrix.GeneralLinearGroup (Fin 2) ℝ) := by
    intro hc
    apply hf
    apply DFunLike.ext
    intro z
    change f z=z
    exact (hAct z).trans ((UpperHalfPlane.forall_smul_eq_self_iff_mem_center.mpr hc) z)
  intro x hx y hy
  have hxA : A • x=x:=(hAct x).symm.trans hx
  have hyA : A • y=y:=(hAct y).symm.trans hy
  have he:=UpperHalfPlane.isElliptic_of_exists_smul_eq_self hA hAc ⟨x,hxA⟩
  exact ((UpperHalfPlane.gl_smul_eq_self_iff_eq_fixedPt hA he).mp hxA).trans
    ((UpperHalfPlane.gl_smul_eq_self_iff_eq_fixedPt hA he).mp hyA).symm

/-- In an actual discrete conformal native group, only finitely many points of
an actual compact set have a nontrivial stabilizer. This is false for reflections,
which are excluded by the genuine positive-determinant representation. -/
theorem nativePositiveGroup_compact_nonfree_finite
    (H : Subgroup (ℍ≃ᵢℍ)) [DiscreteTopology H]
    (hPos : ∀g : H,∃A : Matrix.GeneralLinearGroup (Fin 2) ℝ,
      0<A.val.det ∧∀z : ℍ,g.val z=A • z)
    (K : Set ℍ) (hK : IsCompact K) :
    (K∩{x : ℍ | ∃g : H,g≠1 ∧g • x=x}).Finite := by
  let F : Set H:={g | ((g • ·) '' K∩K).Nonempty}
  have hF : F.Finite:=nativeIsometrySubgroup_discontinuous H K hK
  have hEach (g : H) : {x : ℍ | x∈K ∧g≠1 ∧g • x=x}.Finite := by
    by_cases hg : g=1
    · simp only [hg,ne_eq,not_true_eq_false,false_and,and_false,ofPred_false]
      exact finite_empty
    · obtain ⟨A,hA,hAct⟩:=hPos g
      have hgv : g.val≠1:=fun h=>hg (Subtype.ext h)
      apply (nativePositiveGL_fixedSet_subsingleton g.val hgv A hA hAct).finite.subset
      intro x hx
      exact hx.2.2
  apply (hF.biUnion (fun g _=>hEach g)).subset
  rintro x ⟨hx,g,hg,hfix⟩
  refine mem_iUnion.mpr ⟨g,mem_iUnion.mpr ⟨?_,hx,hg,hfix⟩⟩
  exact ⟨x,⟨x,hx,hfix⟩,hx⟩

/-- Nontrivial actual stabilizers transport by genuine group conjugation. -/
theorem native_nonfree_smul (H : Subgroup (ℍ≃ᵢℍ)) {z : ℍ}
    (hz : ∃h : H,h≠1 ∧h • z=z) (g : H) :
    ∃h : H,h≠1 ∧h • (g • z)=g • z := by
  obtain ⟨h,hh,hfix⟩:=hz
  refine ⟨g*h*g⁻¹,?_,?_⟩
  · intro he
    apply hh
    have hc:=congrArg (fun a : H=>g⁻¹*a*g) he
    simpa only [mul_assoc,inv_mul_cancel_left,mul_inv_cancel_left,mul_one,one_mul,
      inv_mul_cancel] using hc
  · simp only [mul_smul,inv_smul_smul,hfix]

/-- If an actual compact set meets all original orbits of a discrete conformal
group, the actual quotient has only finitely many singular orbit classes. -/
theorem nativePositiveGroup_nonfree_orbit_image_finite
    (H : Subgroup (ℍ≃ᵢℍ)) [DiscreteTopology H]
    (hPos : ∀g : H,∃A : Matrix.GeneralLinearGroup (Fin 2) ℝ,
      0<A.val.det ∧∀z : ℍ,g.val z=A • z)
    (K : Set ℍ) (hK : IsCompact K)
    (hCover : ∀z : ℍ,∃g : H,g • z∈K) :
    (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitProjection H ℍ '' {z : ℍ | ∃g : H,g≠1 ∧g • z=z}).Finite := by
  apply ((nativePositiveGroup_compact_nonfree_finite H hPos K hK).image
    (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitProjection H ℍ)).subset
  rintro q ⟨z,hz,rfl⟩
  obtain ⟨g,hgz⟩:=hCover z
  exact ⟨g • z,⟨hgz,native_nonfree_smul H hz
    g⟩,_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitProjection_smul H ℍ g z⟩

/-- The true exceptional target consists only of original vertex orbits and
actual nontrivial-stabilizer orbits. The entire translated side boundary is not removed. -/
def nativePolygonExceptionalOrbitSet (H : Subgroup (ℍ≃ᵢℍ)) (V : Set ℍ) :
    Set (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitQuotient H ℍ):=
  (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitProjection H ℍ '' V)∪
    (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitProjection H ℍ '' {z : ℍ | ∃g : H,g≠1 ∧g • z=z})

/-- In the conformal case the actual exceptional target set is finite, with
no assumed finiteness of elliptic classes or of the branch locus. -/
theorem nativePositiveGroup_exceptionalOrbitSet_finite
    (H : Subgroup (ℍ≃ᵢℍ)) [DiscreteTopology H]
    (hPos : ∀g : H,∃A : Matrix.GeneralLinearGroup (Fin 2) ℝ,
      0<A.val.det ∧∀z : ℍ,g.val z=A • z)
    (K : Set ℍ) (hK : IsCompact K) (hCover : ∀z : ℍ,∃g : H,g • z∈K)
    (V : Set ℍ) (hV : V.Finite) : (nativePolygonExceptionalOrbitSet H V).Finite :=
  (hV.image (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitProjection H ℍ)).union
    (nativePositiveGroup_nonfree_orbit_image_finite H hPos K hK hCover)

/-- The true nonvertex free orbit locus is exactly the complement of the
actual exceptional target set, without deleting every translated polygon side. -/
theorem nativePolygonNonvertexFreeLocus_orbit_image
    (H : Subgroup (ℍ≃ᵢℍ)) (V : Set ℍ) :
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitProjection H ℍ '' _root_.LowDimensionalTopology.Geometry.Polygon.nativePolygonNonvertexFreeLocus H V=
      (nativePolygonExceptionalOrbitSet H V)ᶜ := by
  ext q
  constructor
  · rintro ⟨z,hz,rfl⟩ hbad
    rcases hbad with hv|he
    · obtain ⟨v,hv,hev⟩:=hv
      obtain ⟨g,hg⟩:=(Quotient.exact hev : MulAction.orbitRel H ℍ v z)
      change g • z=v at hg
      apply hz.2 g⁻¹
      exact ⟨v,hv,by change g⁻¹ • v=z;rw [←hg,inv_smul_smul]⟩
    · obtain ⟨w,⟨h,hh,hfix⟩,hew⟩:=he
      obtain ⟨g,hg⟩:=(Quotient.exact hew : MulAction.orbitRel H ℍ w z)
      change g • z=w at hg
      have hw : ∀a : H,a • w=w →a=1:=hg ▸ _root_.LowDimensionalTopology.Geometry.Polygon.native_free_smul H hz.1 g
      exact hh (hw h hfix)
  · intro hq
    obtain ⟨z,rfl⟩:=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitProjection_surjective H ℍ q
    refine ⟨z,⟨?_,?_⟩,rfl⟩
    · intro g hg
      by_contra hne
      exact hq (Or.inr ⟨z,⟨g,hne,hg⟩,rfl⟩)
    · intro g hgz
      obtain ⟨v,hv,hgv⟩:=hgz
      apply hq
      exact Or.inl ⟨v,hv,(_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitProjection_smul H ℍ g
        v).symm.trans
        (congrArg (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitProjection H ℍ) hgv)⟩

/-- For an actual compact original polygon whose generated native group is
conformal, the genuine covering misses only a derived finite exceptional set.
No local power-branch model at those exceptional points is asserted here. -/
theorem nativeJordan_identifiedPolygon_covering_off_finite_exceptional
    {P : _root_.LowDimensionalTopology.Geometry.Polygon.PoincarePolygon ℍ}
    (C : Set ℂ) (hC : _root_.LowDimensionalTopology.Geometry.Polygon.IsComplexJordanCurve C)
    (hbound : C⊆Metric.closedBall (0 : ℂ) 1)
    (hInside : P.interior=_root_.LowDimensionalTopology.Geometry.Polygon.nativeJordanInside C)
    (hBoundary : P.boundary=(fun z : ℍ=>(_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z : ℂ)) ⁻¹'
      C)
    (D : _root_.LowDimensionalTopology.Geometry.Polygon.NativeGeodesicSideIntervals P) (S :
      _root_.LowDimensionalTopology.Geometry.Polygon.PoincareSidePairing (ℍ≃ᵢℍ) P)
    [DiscreteTopology S.Generated] (hP : IsCompact P.carrier)
    (hOpp : ∀s : P.Side,∀p∈s.val,p∉D.vertices →S.OppositeSideNeighborhoods s p)
    (hPos : ∀g : S.Generated,∃A : Matrix.GeneralLinearGroup (Fin 2) ℝ,
      0<A.val.det ∧∀z : ℍ,g.val z=A • z) :
    (nativePolygonExceptionalOrbitSet S.Generated D.vertices).Finite ∧
    IsCoveringMapOn S.pointToOrbit (nativePolygonExceptionalOrbitSet S.Generated D.vertices)ᶜ := by
  let G:=_root_.LowDimensionalTopology.Geometry.Polygon.nativeJordan_sideIntervals_geometry C hC hbound hInside hBoundary D
  obtain ⟨k,hk,hAll⟩:=_root_.LowDimensionalTopology.Geometry.Polygon.nativeJordan_angularMultiplicity_positive_integer
    C hC hbound hInside hBoundary D S hP hOpp
  have hM : ∀z : ℍ,_root_.LowDimensionalTopology.Geometry.Polygon.nativePolygonAngularMultiplicity S.Generated P.carrier z≠0 := by
    intro z
    rw [←G.angularMultiplicity_interior_eq hP S.Generated z,(hAll z).1]
    exact_mod_cast hk.ne'
  have hCover : ∀z : ℍ,∃g : S.Generated,g • z∈P.carrier := by
    intro z
    obtain ⟨q,hq⟩:=S.evaluation_surjective_of_positive_angularMultiplicity hP hM z
    obtain ⟨a,ha⟩:=Quotient.exists_rep q
    change S.project a=q at ha
    have he : a.1 • a.2.val=z:=(congrArg S.evaluation ha).trans hq
    refine ⟨a.1⁻¹,?_⟩
    rw [←he,inv_smul_smul]
    exact a.2.property
  refine ⟨nativePositiveGroup_exceptionalOrbitSet_finite S.Generated hPos P.carrier hP
    hCover D.vertices (D.vertices_finite_of_compact G hP),?_⟩
  rw [←nativePolygonNonvertexFreeLocus_orbit_image]
  exact _root_.LowDimensionalTopology.Geometry.Polygon.nativeJordan_identifiedPolygon_coveringOn_nonvertex_free
    C hC hbound hInside hBoundary D S hP hOpp
/--
The genuine conformal original identified polygon has exactly the same
positive degree as over every point outside a derived finite
exceptional set. Actual local power branch charts remain a separate obligation.
-/
theorem nativeJordan_identifiedPolygon_finite_exceptional_degree
    {P : _root_.LowDimensionalTopology.Geometry.Polygon.PoincarePolygon ℍ}
    (C : Set ℂ) (hC : _root_.LowDimensionalTopology.Geometry.Polygon.IsComplexJordanCurve C)
    (hbound : C⊆Metric.closedBall (0 : ℂ) 1)
    (hInside : P.interior=_root_.LowDimensionalTopology.Geometry.Polygon.nativeJordanInside C)
    (hBoundary : P.boundary=(fun z : ℍ=>(_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z : ℂ)) ⁻¹'
      C)
    (D : _root_.LowDimensionalTopology.Geometry.Polygon.NativeGeodesicSideIntervals P) (S :
      _root_.LowDimensionalTopology.Geometry.Polygon.PoincareSidePairing (ℍ≃ᵢℍ) P)
    [DiscreteTopology S.Generated] (hP : IsCompact P.carrier)
    (hOpp : ∀s : P.Side,∀p∈s.val,p∉D.vertices →S.OppositeSideNeighborhoods s p)
    (hPos : ∀g : S.Generated,∃A : Matrix.GeneralLinearGroup (Fin 2) ℝ,
      0<A.val.det ∧∀z : ℍ,g.val z=A • z) :
    ∃k : ℕ,0<k ∧(nativePolygonExceptionalOrbitSet S.Generated D.vertices).Finite ∧
      IsCoveringMapOn S.pointToOrbit (nativePolygonExceptionalOrbitSet S.Generated D.vertices)ᶜ ∧
      ∀q∉nativePolygonExceptionalOrbitSet S.Generated D.vertices,
        Nat.card (S.pointToOrbit ⁻¹' {q})=k := by
  obtain ⟨k,hk,_,_,_,_,_,_,_,_,hDense,_,hDeg⟩:=
    _root_.LowDimensionalTopology.Geometry.Polygon.nativeJordan_identifiedPolygon_finite_open_cover_degree C hC hbound hInside hBoundary D S hP hOpp
  obtain ⟨hFinite,hCover⟩:=nativeJordan_identifiedPolygon_covering_off_finite_exceptional
    C hC hbound hInside hBoundary D S hP hOpp hPos
  exact ⟨k,hk,hFinite,hCover,_root_.LowDimensionalTopology.Geometry.Auxiliary.Topology.coveringOn_fiber_natCard_of_dense
    hCover hDense k hDeg⟩
end LowDimensionalTopology.Geometry.Fuchsian
