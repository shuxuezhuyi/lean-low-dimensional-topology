/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Hyperbolic.Models.Disc.ExtendedCarrier
public import LowDimensionalTopology.Geometry.Fuchsian.Displacement.EllipticFree.EllipticFreeCorollaries
public import LowDimensionalTopology.Geometry.Surfaces.Hyperbolic.QuotientMetric
public import LowDimensionalTopology.Geometry.Fuchsian.Basic.FuchsianElementary
public import LowDimensionalTopology.Geometry.Surfaces.Topology.TorusFundamentalGroup
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set
open scoped Topology UpperHalfPlane MatrixGroups OnePoint Complex.UnitDisc unitInterval
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
universe u

/-- The actual disc line integral bounds the native endpoint distance of every finite-piece curve. -/
theorem discPiecewiseC1Curve_dist_le_length
    {z w : 𝔻}
    (c : _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscPiecewiseC1Curve z w) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist z w≤c.length := by
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist_eq_halfPlane,←c.toHalfPlane_length]
  exact c.toHalfPlane.dist_le_length

/-- The original lifted curves, with their true integral lengths, obey the sharp length-product bound. -/
theorem disc_lifted_curves_sinh_length_bound
    (H : Subgroup Mobius.complexMobiusGroup) (hInv : ∀f:H,f.val.val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc=_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc)
    (hE : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsEllipticFree H) (f g : H)
    (hPair : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure ({f.val,g.val}:Set Mobius.complexMobiusGroup)))
    (z u v : 𝔻)
    (c : _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscPiecewiseC1Curve z u)
    (d : _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscPiecewiseC1Curve z v)
    (hfu : f.val.val ((z:ℂ):Mobius.ExtendedComplex)=((u:ℂ):Mobius.ExtendedComplex))
    (hgv : g.val.val ((z:ℂ):Mobius.ExtendedComplex)=((v:ℂ):Mobius.ExtendedComplex)) :
    1≤Real.sinh (c.length/2)*Real.sinh (d.length/2) := by
  have hb:=ellipticFree_disc_displacement_bound H hInv hE f g hPair z u v hfu hgv
  have hc : Real.sinh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist z u/2)≤Real.sinh (c.length/2):=
    Real.sinh_le_sinh.mpr (by linarith [discPiecewiseC1Curve_dist_le_length c])
  have hd : Real.sinh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist z v/2)≤Real.sinh (d.length/2):=
    Real.sinh_le_sinh.mpr (by linarith [discPiecewiseC1Curve_dist_le_length d])
  have hzn : 0≤Real.sinh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist z u/2) := by
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist_eq_halfPlane]
    exact Real.sinh_nonneg_iff.mpr (by positivity)
  have hwn : 0≤Real.sinh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist z v/2) := by
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist_eq_halfPlane]
    exact Real.sinh_nonneg_iff.mpr (by positivity)
  exact hb.trans (mul_le_mul hc hd hwn (hzn.trans hc))

/-- A literal lift of a finite-piece quotient curve: each original C1 piece projects pointwise,
and every genuine native piece is joined to the next at its actual endpoint. -/
inductive QuotientPiecewiseCurveLift {H : Subgroup Mobius.complexMobiusGroup}
    (hInv : ∀(g:H) z,z∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc→g•z∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc) :
    {x y : _root_.LowDimensionalTopology.Geometry.Surfaces.MobiusDomainQuotient (_root_.LowDimensionalTopology.Geometry.Surfaces.unitDiscMobiusInvariantDomain H hInv)}→
      _root_.LowDimensionalTopology.Geometry.Surfaces.DiscQuotientPiecewiseC1Curve hInv x y→{z w : 𝔻}→_root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscPiecewiseC1Curve z w→Prop
  | nil (x) (z : 𝔻) (hz : _root_.LowDimensionalTopology.Geometry.Surfaces.discQuotientProjection hInv z=x) :
      QuotientPiecewiseCurveLift hInv (.nil x) (.nil z)
  | cons (p : _root_.LowDimensionalTopology.Geometry.Surfaces.DiscQuotientC1CurvePiece hInv) (q : _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscC1CurvePiece)
      (ha : q.a=0) (hb : q.b=1)
      (hproj : ∀t:I,_root_.LowDimensionalTopology.Geometry.Surfaces.discQuotientProjection hInv (q.curve t)=p.curve t)
      {y} (tail : _root_.LowDimensionalTopology.Geometry.Surfaces.DiscQuotientPiecewiseC1Curve hInv (p.curve 1) y)
      {w : 𝔻} (liftTail : _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscPiecewiseC1Curve (q.curve q.b) w)
      (hlift : QuotientPiecewiseCurveLift hInv tail liftTail) :
      QuotientPiecewiseCurveLift hInv (.cons p tail) (.cons q liftTail)

/-- A genuine piecewise lift has exactly the original projected endpoints. -/
theorem QuotientPiecewiseCurveLift.endpoints
    {H : Subgroup Mobius.complexMobiusGroup}
    {hInv : ∀(g:H) z,z∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc→g•z∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc}
    {x y : _root_.LowDimensionalTopology.Geometry.Surfaces.MobiusDomainQuotient (_root_.LowDimensionalTopology.Geometry.Surfaces.unitDiscMobiusInvariantDomain H hInv)}
    {p : _root_.LowDimensionalTopology.Geometry.Surfaces.DiscQuotientPiecewiseC1Curve hInv x y}
    {z w : 𝔻}
    {c : _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscPiecewiseC1Curve z w}
    (hc : QuotientPiecewiseCurveLift hInv p c) :
    _root_.LowDimensionalTopology.Geometry.Surfaces.discQuotientProjection hInv z=x ∧ _root_.LowDimensionalTopology.Geometry.Surfaces.discQuotientProjection hInv w=y := by
  induction hc with
  | nil x z hz => exact ⟨hz,hz⟩
  | cons p q ha hb hproj tail liftTail hlift ih =>
    refine ⟨?_,ih.2⟩
    simpa [ha] using hproj 0

/-- The quotient length equals the actual weighted length in every genuine piecewise lift. -/
theorem QuotientPiecewiseCurveLift.length_eq
    {H : Subgroup Mobius.complexMobiusGroup}
    {hInv : ∀(g:H) z,z∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc→g•z∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc}
    (hD : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn H _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc) (hE : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsEllipticFree H)
    {x y : _root_.LowDimensionalTopology.Geometry.Surfaces.MobiusDomainQuotient (_root_.LowDimensionalTopology.Geometry.Surfaces.unitDiscMobiusInvariantDomain H hInv)}
    {p : _root_.LowDimensionalTopology.Geometry.Surfaces.DiscQuotientPiecewiseC1Curve hInv x y}
    {z w : 𝔻}
    {c : _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscPiecewiseC1Curve z w}
    (hc : QuotientPiecewiseCurveLift hInv p c) : p.length=c.length := by
  induction hc with
  | nil x z hz => rfl
  | cons p q ha hb hproj tail liftTail hlift ih =>
    change p.length+tail.length=q.length+liftTail.length
    rw [p.length_eq_of_lift hD (fun f hf _hne=>hE ⟨f,hf⟩) q ha hb hproj,ih]

/-- Every original finite-piece quotient curve has a genuine joined lift from each chosen
point over its source. The lift is constructed by actual disc-preserving deck transformations. -/
theorem quotientPiecewiseCurveLift_exists
    {H : Subgroup Mobius.complexMobiusGroup}
    (hInv : ∀(g:H) z,z∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc→g•z∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc)
    {x y : _root_.LowDimensionalTopology.Geometry.Surfaces.MobiusDomainQuotient (_root_.LowDimensionalTopology.Geometry.Surfaces.unitDiscMobiusInvariantDomain H hInv)}
    (p : _root_.LowDimensionalTopology.Geometry.Surfaces.DiscQuotientPiecewiseC1Curve hInv x y) (z : 𝔻)
    (hz : _root_.LowDimensionalTopology.Geometry.Surfaces.discQuotientProjection hInv z=x) :
    ∃(w : 𝔻)(c : _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscPiecewiseC1Curve z w),QuotientPiecewiseCurveLift hInv p c := by
  induction p generalizing z with
  | nil x => exact ⟨z,.nil z,.nil x z hz⟩
  | @cons p y tail ih =>
    have hp0 : _root_.LowDimensionalTopology.Geometry.Surfaces.discQuotientProjection hInv (p.lift.curve 0)=p.curve 0 := by
      simpa using p.lift_spec.2.2 0
    obtain ⟨g,hg⟩ := (_root_.LowDimensionalTopology.Geometry.Surfaces.discQuotientProjection_eq_iff hInv (p.lift.curve 0) z).mp
      (hp0.trans hz.symm)
    obtain ⟨a,c,hdet,hform⟩ := _root_.LowDimensionalTopology.Geometry.Hyperbolic.complexMobius_disc_normal_form g.val
      (_root_.LowDimensionalTopology.Geometry.Surfaces.mobiusInvariantDomain_image_eq (_root_.LowDimensionalTopology.Geometry.Surfaces.unitDiscMobiusInvariantDomain H hInv) g)
    let q := _root_.LowDimensionalTopology.Geometry.Surfaces.discC1PieceMap a c hdet p.lift
    have hqa : q.a=0 := p.lift_spec.1
    have hqb : q.b=1 := p.lift_spec.2.1
    have hqactual (t : ℝ) :
        g.val.val ((p.lift.curve t:ℂ):Mobius.ExtendedComplex)=((q.curve t:ℂ):Mobius.ExtendedComplex) :=
      _root_.LowDimensionalTopology.Geometry.Surfaces.discFractionalHomeomorph_actual g.val a c hdet hform (p.lift.curve t)
    have hqproj (t : I) : _root_.LowDimensionalTopology.Geometry.Surfaces.discQuotientProjection hInv (q.curve t)=p.curve t :=
      (_root_.LowDimensionalTopology.Geometry.Surfaces.discQuotientProjection_eq_of_mobius hInv g (p.lift.curve t) (q.curve t)
        (hqactual t)).trans (p.lift_spec.2.2 t)
    have hstart : q.curve q.a=z := by
      rw [hqa]
      exact Complex.UnitDisc.coe_injective (OnePoint.coe_injective ((hqactual 0).symm.trans hg))
    have hend : _root_.LowDimensionalTopology.Geometry.Surfaces.discQuotientProjection hInv (q.curve q.b)=p.curve 1 := by
      simpa [hqb] using hqproj 1
    obtain ⟨w,liftTail,hLiftTail⟩ := ih (q.curve q.b) hend
    subst z
    exact ⟨w,.cons q liftTail,.cons p q hqa hqb hqproj tail liftTail hLiftTail⟩

/-- A based quotient loop has an actual deck endpoint and a genuine integral-length lift. -/
theorem quotientClosedCurve_monodromy {H : Subgroup Mobius.complexMobiusGroup}
    (hInv : ∀(g:H) z,z∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc→g•z∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc)
    {x : _root_.LowDimensionalTopology.Geometry.Surfaces.MobiusDomainQuotient (_root_.LowDimensionalTopology.Geometry.Surfaces.unitDiscMobiusInvariantDomain H hInv)}
    (p : _root_.LowDimensionalTopology.Geometry.Surfaces.DiscQuotientPiecewiseC1Curve hInv x x) (z : 𝔻)
    (hz : _root_.LowDimensionalTopology.Geometry.Surfaces.discQuotientProjection hInv z=x) :
    ∃(f : H)(w : 𝔻)(c : _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscPiecewiseC1Curve z w),
      QuotientPiecewiseCurveLift hInv p c ∧
      f.val.val ((z:ℂ):Mobius.ExtendedComplex)=((w:ℂ):Mobius.ExtendedComplex) := by
  obtain ⟨w,c,hc⟩ := quotientPiecewiseCurveLift_exists hInv p z hz
  obtain ⟨f,hf⟩ := (_root_.LowDimensionalTopology.Geometry.Surfaces.discQuotientProjection_eq_iff hInv z w).mp
    (hz.trans hc.endpoints.2.symm)
  exact ⟨f,w,c,hc,hf⟩

/-- The true lengths of two original based quotient loops obey the product bound whenever
their actual lifted endpoint transformations generate a non-elementary subgroup. -/
theorem quotient_closed_curves_sinh_length_bound
    {H : Subgroup Mobius.complexMobiusGroup}
    (hInv : ∀(g:H) z,z∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc→g•z∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc)
    (hD : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn H _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc) (hE : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsEllipticFree H)
    {x : _root_.LowDimensionalTopology.Geometry.Surfaces.MobiusDomainQuotient (_root_.LowDimensionalTopology.Geometry.Surfaces.unitDiscMobiusInvariantDomain H hInv)}
    (p q : _root_.LowDimensionalTopology.Geometry.Surfaces.DiscQuotientPiecewiseC1Curve hInv x x) (z u v : 𝔻)
    (c : _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscPiecewiseC1Curve z u)
    (d : _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscPiecewiseC1Curve z v)
    (hc : QuotientPiecewiseCurveLift hInv p c) (hd : QuotientPiecewiseCurveLift hInv q d)
    (f g : H)
    (hfu : f.val.val ((z:ℂ):Mobius.ExtendedComplex)=((u:ℂ):Mobius.ExtendedComplex))
    (hgv : g.val.val ((z:ℂ):Mobius.ExtendedComplex)=((v:ℂ):Mobius.ExtendedComplex))
    (hPair : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure ({f.val,g.val}:Set Mobius.complexMobiusGroup))) :
    1≤Real.sinh (p.length/2)*Real.sinh (q.length/2) := by
  rw [hc.length_eq hD hE,hd.length_eq hD hE]
  exact disc_lifted_curves_sinh_length_bound H
    (_root_.LowDimensionalTopology.Geometry.Surfaces.mobiusInvariantDomain_image_eq (_root_.LowDimensionalTopology.Geometry.Surfaces.unitDiscMobiusInvariantDomain H hInv)) hE f g hPair z u v c d hfu hgv

/-- Original based closed curves have genuine monodromy generators; either these generate
an elementary subgroup or their actual quotient integral lengths satisfy the sharp bound. -/
theorem quotient_closed_curves_elementary_or_sinh_length_bound
    {H : Subgroup Mobius.complexMobiusGroup}
    (hInv : ∀(g:H) z,z∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc→g•z∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc)
    (hD : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn H _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc) (hE : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsEllipticFree H)
    {x : _root_.LowDimensionalTopology.Geometry.Surfaces.MobiusDomainQuotient (_root_.LowDimensionalTopology.Geometry.Surfaces.unitDiscMobiusInvariantDomain H hInv)}
    (p q : _root_.LowDimensionalTopology.Geometry.Surfaces.DiscQuotientPiecewiseC1Curve hInv x x) (z : 𝔻)
    (hz : _root_.LowDimensionalTopology.Geometry.Surfaces.discQuotientProjection hInv z=x) :
    ∃(f g : H)(u v : 𝔻)(c : _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscPiecewiseC1Curve z u)(d : _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscPiecewiseC1Curve z v),
      QuotientPiecewiseCurveLift hInv p c ∧ QuotientPiecewiseCurveLift hInv q d ∧
      f.val.val ((z:ℂ):Mobius.ExtendedComplex)=((u:ℂ):Mobius.ExtendedComplex) ∧
      g.val.val ((z:ℂ):Mobius.ExtendedComplex)=((v:ℂ):Mobius.ExtendedComplex) ∧
      (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsElementary (Subgroup.closure ({f.val,g.val}:Set Mobius.complexMobiusGroup)) ∨
        1≤Real.sinh (p.length/2)*Real.sinh (q.length/2)) := by
  classical
  obtain ⟨f,u,c,hc,hfu⟩ := quotientClosedCurve_monodromy hInv p z hz
  obtain ⟨g,v,d,hd,hgv⟩ := quotientClosedCurve_monodromy hInv q z hz
  refine ⟨f,g,u,v,c,d,hc,hd,hfu,hgv,?_⟩
  by_cases hPair : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsElementary (Subgroup.closure ({f.val,g.val}:Set Mobius.complexMobiusGroup))
  · exact Or.inl hPair
  · exact Or.inr (quotient_closed_curves_sinh_length_bound hInv hD hE p q z u v c d hc hd f g hfu hgv hPair)

/-- Finite concatenations of genuine C1 curves on the original Riemann surface. -/
inductive SurfacePiecewiseC1Curve {X : Type u} [TopologicalSpace X]
    {R : _root_.LowDimensionalTopology.Geometry.Surfaces.RiemannSurface X} (M : _root_.LowDimensionalTopology.Geometry.Surfaces.HyperbolicSurfaceModel R) : X→X→Type u
  | nil (x : X) : SurfacePiecewiseC1Curve M x x
  | cons (p : _root_.LowDimensionalTopology.Geometry.Surfaces.HyperbolicSurfaceC1CurvePiece M) {y : X}
      (tail : SurfacePiecewiseC1Curve M (p.curve 1) y) :
      SurfacePiecewiseC1Curve M (p.curve 0) y

/-- Transport every original piece by the specified actual conformal quotient presentation. -/
def SurfacePiecewiseC1Curve.toQuotient {X : Type*} [TopologicalSpace X]
    {R : _root_.LowDimensionalTopology.Geometry.Surfaces.RiemannSurface X}
    {M : _root_.LowDimensionalTopology.Geometry.Surfaces.HyperbolicSurfaceModel R}
    {x y : X} :
    SurfacePiecewiseC1Curve M x y→
      _root_.LowDimensionalTopology.Geometry.Surfaces.DiscQuotientPiecewiseC1Curve M.invariant (M.homeomorph x) (M.homeomorph y)
  | .nil x => .nil (M.homeomorph x)
  | .cons p tail => .cons p.toQuotient tail.toQuotient

/-- Length is the sum of the genuine coordinate-independent weighted integrals of its pieces. -/
def SurfacePiecewiseC1Curve.length {X : Type*} [TopologicalSpace X]
    {R : _root_.LowDimensionalTopology.Geometry.Surfaces.RiemannSurface X}
    {M : _root_.LowDimensionalTopology.Geometry.Surfaces.HyperbolicSurfaceModel R}
    {x y : X} :
    SurfacePiecewiseC1Curve M x y→ℝ
  | .nil _ => 0
  | .cons p tail => p.length+tail.length

/-- Finite-piece curves are actual continuous paths on the original surface. -/
def SurfacePiecewiseC1Curve.toPath {X : Type*} [TopologicalSpace X]
    {R : _root_.LowDimensionalTopology.Geometry.Surfaces.RiemannSurface X}
    {M : _root_.LowDimensionalTopology.Geometry.Surfaces.HyperbolicSurfaceModel R}
    {x y : X} :
    SurfacePiecewiseC1Curve M x y→Path x y
  | .nil x => Path.refl x
  | .cons p tail => p.toPath.trans tail.toPath

/-- Every piece contributes a nonnegative genuine integral length. -/
theorem SurfacePiecewiseC1Curve.length_nonneg {X : Type*} [TopologicalSpace X]
    {R : _root_.LowDimensionalTopology.Geometry.Surfaces.RiemannSurface X}
    {M : _root_.LowDimensionalTopology.Geometry.Surfaces.HyperbolicSurfaceModel R}
    {x y : X}
    (p : SurfacePiecewiseC1Curve M x y) : 0≤p.length := by
  induction p with
  | nil x => exact le_rfl
  | cons p tail ih => exact add_nonneg p.length_nonneg ih

/-- The conformal presentation preserves actual piecewise lengths term by term. -/
theorem SurfacePiecewiseC1Curve.toQuotient_length {X : Type*} [TopologicalSpace X]
    {R : _root_.LowDimensionalTopology.Geometry.Surfaces.RiemannSurface X}
    {M : _root_.LowDimensionalTopology.Geometry.Surfaces.HyperbolicSurfaceModel R}
    {x y : X}
    (p : SurfacePiecewiseC1Curve M x y) : p.toQuotient.length=p.length := by
  induction p with
  | nil x => rfl
  | cons p tail ih => exact congrArg (p.length+·) ih

/-- The closed-curve consequence on the original surface, for arbitrary genuine finite-piece
curves: the exceptional case is exactly an elementary subgroup of actual lifted generators. -/
theorem surface_closed_curves_elementary_or_sinh_length_bound
    {X : Type*} [TopologicalSpace X] {R : _root_.LowDimensionalTopology.Geometry.Surfaces.RiemannSurface X}
    (M : _root_.LowDimensionalTopology.Geometry.Surfaces.HyperbolicSurfaceModel R)
    {x : X} (p q : SurfacePiecewiseC1Curve M x x) (z : 𝔻)
    (hz : _root_.LowDimensionalTopology.Geometry.Surfaces.discQuotientProjection M.invariant z=M.homeomorph x) :
    ∃(f g : M.group)(u v : 𝔻)(c : _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscPiecewiseC1Curve z u)(d : _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscPiecewiseC1Curve z v),
      QuotientPiecewiseCurveLift M.invariant p.toQuotient c ∧
      QuotientPiecewiseCurveLift M.invariant q.toQuotient d ∧
      f.val.val ((z:ℂ):Mobius.ExtendedComplex)=((u:ℂ):Mobius.ExtendedComplex) ∧
      g.val.val ((z:ℂ):Mobius.ExtendedComplex)=((v:ℂ):Mobius.ExtendedComplex) ∧
      (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsElementary (Subgroup.closure ({f.val,g.val}:Set Mobius.complexMobiusGroup)) ∨
        1≤Real.sinh (p.length/2)*Real.sinh (q.length/2)) := by
  have hE : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsEllipticFree M.group := by
    intro f
    exact fun hf=>M.no_elliptic f.val f.property hf.1 hf
  simpa only [_root_.LowDimensionalTopology.Geometry.Fuchsian.SurfacePiecewiseC1Curve.toQuotient_length] using
    quotient_closed_curves_elementary_or_sinh_length_bound M.invariant M.discontinuous hE
      p.toQuotient q.toQuotient z hz

/-- A genuine piecewise lift realizes an actual continuous path whose projection is the
entire original path, including the concatenation parametrization. -/
theorem QuotientPiecewiseCurveLift.exists_path
    {H : Subgroup Mobius.complexMobiusGroup}
    {hInv : ∀(g:H) z,z∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc→g•z∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc}
    {x y : _root_.LowDimensionalTopology.Geometry.Surfaces.MobiusDomainQuotient (_root_.LowDimensionalTopology.Geometry.Surfaces.unitDiscMobiusInvariantDomain H hInv)}
    {p : _root_.LowDimensionalTopology.Geometry.Surfaces.DiscQuotientPiecewiseC1Curve hInv x y}
    {z w : 𝔻}
    {c : _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscPiecewiseC1Curve z w}
    (hc : QuotientPiecewiseCurveLift hInv p c) :
    ∃Γ : Path z w,∀t:I,_root_.LowDimensionalTopology.Geometry.Surfaces.discQuotientProjection hInv (Γ t)=p.toPath t := by
  induction hc with
  | nil x z hz => exact ⟨Path.refl z,fun _=>hz⟩
  | cons p q ha hb hproj tail liftTail hlift ih =>
    obtain ⟨Γ,hΓ⟩ := ih
    let α : Path (q.curve q.a) (q.curve q.b) := {
      toFun:=fun t=>q.curve t
      continuous_toFun:=q.continuous_curve.comp_continuous continuous_subtype_val (by
        intro t
        simpa only [ha,hb] using t.property)
      source':=by simp [ha]
      target':=by simp [hb] }
    refine ⟨α.trans Γ,?_⟩
    intro t
    simp only [_root_.LowDimensionalTopology.Geometry.Surfaces.DiscQuotientPiecewiseC1Curve.toPath,Path.trans_apply]
    split_ifs with ht
    · exact hproj _
    · exact hΓ _

/-- The actual reciprocal is a genuine order-two elliptic map. -/
theorem curveException_reciprocal_elliptic : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusReciprocal := by
  apply _root_.LowDimensionalTopology.Geometry.Mobius.mobius_finite_order_elliptic
  · intro h
    have he := congrArg (fun f : Mobius.complexMobiusGroup=>f.val ((0:ℂ):Mobius.ExtendedComplex)) h
    simp only [_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusReciprocal_zero] at he
    change (∞:Mobius.ExtendedComplex)=((0:ℂ):Mobius.ExtendedComplex) at he
    exact OnePoint.infty_ne_coe (0:ℂ) he
  · exact isOfFinOrder_iff_pow_eq_one.mpr ⟨2,by decide,by simpa only [pow_two] using _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusReciprocal_mul_self⟩

/-- An actual discrete elementary disc group with no elliptics is cyclic. -/
theorem FuchsianDisc.elementary_ellipticFree_isCyclic
    {H : Subgroup Mobius.complexMobiusGroup}
    (D : FuchsianDisc H)
    (hE : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsEllipticFree H)
    (he : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsElementary H) : IsCyclic H := by
  rcases D.elementary_classification he with hc | ⟨u,d,_hi,_hd,hK⟩
  · exact hc
  · have hflip : fuchsianDihedralFlip∈_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate u H := by
      rw [hK]
      exact Subgroup.subset_closure (by simp)
    obtain ⟨f,hf,heq⟩ := (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff u H _).mp hflip
    have hflipE : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic fuchsianDihedralFlip := by
      rw [←fuchsianQuarterRotation_reciprocal,_root_.LowDimensionalTopology.Geometry.Mobius.mobiusElliptic_conjugation]
      exact curveException_reciprocal_elliptic
    exact False.elim (hE ⟨f,hf⟩ ((_root_.LowDimensionalTopology.Geometry.Mobius.mobiusElliptic_conjugation f u).mp (heq ▸ hflipE)))

/-- The true compact-hit condition passes to every actual subgroup. -/
theorem curveException_subgroup_discontinuous
    {H K : Subgroup Mobius.complexMobiusGroup}
    (hle : K≤H)
    {S : Set Mobius.ExtendedComplex}
    (hD : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn H S) :
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn K S := by
  intro C hC hCS
  let i : K→H := fun g=>⟨g.val,hle g.property⟩
  have hi : Function.Injective i := by
    intro a b hab
    exact Subtype.ext (congrArg (fun g:H=>g.val) hab)
  exact Set.Finite.preimage (f:=i) hi.injOn (hD C hC hCS)

/-- The actual elementary subgroup represented by two based loops is cyclic. -/
theorem quotient_curve_elementary_pair_isCyclic
    {H : Subgroup Mobius.complexMobiusGroup}
    (hInv : ∀(g:H) z,z∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc→g•z∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc)
    (hD : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn H _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc) (hE : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsEllipticFree H)
    (f g : H) (he : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsElementary (Subgroup.closure ({f.val,g.val}:Set Mobius.complexMobiusGroup))) :
    IsCyclic (Subgroup.closure ({f.val,g.val}:Set Mobius.complexMobiusGroup)) := by
  let K := Subgroup.closure ({f.val,g.val}:Set Mobius.complexMobiusGroup)
  have hle : K≤H := (Subgroup.closure_le H).mpr (by
    rintro a (rfl|rfl)
    · exact f.property
    · exact g.property)
  let D : FuchsianDisc K := {
    carrier:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc
    isDisc:=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.extendedUnitDisc_isComplexOpenDisc
    invariant:=fun g z hz=>hInv ⟨g.val,hle g.property⟩ z hz
    discontinuous:=curveException_subgroup_discontinuous hle hD }
  exact D.elementary_ellipticFree_isCyclic (fun g=>hE ⟨g.val,hle g.property⟩) he


/-- The actual universal disc covering identifies based homotopy classes with the opposite
of the genuine deck group, with the specified fibre point fixing the convention. -/
def quotientLoopFundamentalGroupEquiv {H : Subgroup Mobius.complexMobiusGroup}
    (hInv : ∀(g:H) z,z∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc→g•z∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc)
    (hD : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn H _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc) (hE : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsEllipticFree H)
    (x : _root_.LowDimensionalTopology.Geometry.Surfaces.MobiusDomainQuotient (_root_.LowDimensionalTopology.Geometry.Surfaces.unitDiscMobiusInvariantDomain H hInv)) (z : 𝔻)
    (hz : _root_.LowDimensionalTopology.Geometry.Surfaces.discQuotientProjection hInv z=x) :
    FundamentalGroup (_root_.LowDimensionalTopology.Geometry.Surfaces.MobiusDomainQuotient (_root_.LowDimensionalTopology.Geometry.Surfaces.unitDiscMobiusInvariantDomain H hInv)) x≃*Hᵐᵒᵖ := by
  let D:=_root_.LowDimensionalTopology.Geometry.Surfaces.unitDiscMobiusInvariantDomain H hInv
  letI : SimplyConnectedSpace D.carrier := _root_.LowDimensionalTopology.Geometry.Surfaces.discRiemannSurface_simplyConnected
  exact (_root_.LowDimensionalTopology.Geometry.Surfaces.mobiusDomain_noElliptic_covering D hD (fun f hf _hne=>hE ⟨f,hf⟩)).fundamentalGroupEquiv
    ⟨_root_.LowDimensionalTopology.Geometry.Surfaces.discFiniteHomeomorph.symm z,hz⟩

/-- Its value on the original loop is exactly the actual deck element at the lifted endpoint. -/
theorem quotientLoopFundamentalGroupEquiv_apply
    {H : Subgroup Mobius.complexMobiusGroup}
    (hInv : ∀(g:H) z,z∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc→g•z∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc)
    (hD : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn H _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc) (hE : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsEllipticFree H)
    {x : _root_.LowDimensionalTopology.Geometry.Surfaces.MobiusDomainQuotient (_root_.LowDimensionalTopology.Geometry.Surfaces.unitDiscMobiusInvariantDomain H hInv)}
    (p : _root_.LowDimensionalTopology.Geometry.Surfaces.DiscQuotientPiecewiseC1Curve hInv x x) (z w : 𝔻)
    (hz : _root_.LowDimensionalTopology.Geometry.Surfaces.discQuotientProjection hInv z=x)
    (c : _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscPiecewiseC1Curve z w)
    (hc : QuotientPiecewiseCurveLift hInv p c) (f : H)
    (hf : f.val.val ((z:ℂ):Mobius.ExtendedComplex)=((w:ℂ):Mobius.ExtendedComplex)) :
    quotientLoopFundamentalGroupEquiv hInv hD hE x z hz (.of (.mk p.toPath))=MulOpposite.op f := by
  let D:=_root_.LowDimensionalTopology.Geometry.Surfaces.unitDiscMobiusInvariantDomain H hInv
  let : SimplyConnectedSpace D.carrier := _root_.LowDimensionalTopology.Geometry.Surfaces.discRiemannSurface_simplyConnected
  let hp:=_root_.LowDimensionalTopology.Geometry.Surfaces.mobiusDomain_noElliptic_covering D hD (fun f hf _hne=>hE ⟨f,hf⟩)
  let e : (_root_.LowDimensionalTopology.Geometry.Surfaces.mobiusDomainProjection D) ⁻¹' {x}:=⟨_root_.LowDimensionalTopology.Geometry.Surfaces.discFiniteHomeomorph.symm z,hz⟩
  obtain ⟨Γ,hΓ⟩ := hc.exists_path
  let Δ : C(I,D.carrier) := ⟨fun t=>_root_.LowDimensionalTopology.Geometry.Surfaces.discFiniteHomeomorph.symm (Γ t),
    _root_.LowDimensionalTopology.Geometry.Surfaces.discFiniteHomeomorph.symm.continuous.comp Γ.continuous⟩
  change hp.fundamentalGroupToMulOpposite e (.of (.mk p.toPath))=MulOpposite.op f
  apply hp.fundamentalGroupToMulOpposite_apply_mk_eq (Γ:=Δ)
  · funext t
    exact hΓ t
  · change _root_.LowDimensionalTopology.Geometry.Surfaces.discFiniteHomeomorph.symm (Γ 0)=_root_.LowDimensionalTopology.Geometry.Surfaces.discFiniteHomeomorph.symm z
    rw [Γ.source]
  · apply Subtype.ext
    change (_root_.LowDimensionalTopology.Geometry.Surfaces.discFiniteHomeomorph.symm (Γ 1)).val=f.val.val (_root_.LowDimensionalTopology.Geometry.Surfaces.discFiniteHomeomorph.symm z).val
    rw [Γ.target, _root_.LowDimensionalTopology.Geometry.Surfaces.discFiniteHomeomorph_symm_coe,
      _root_.LowDimensionalTopology.Geometry.Surfaces.discFiniteHomeomorph_symm_coe]
    exact hf.symm

/-- In the elementary exception the original loops, as actual based homotopy classes,
are powers of one class. No abstract generator is substituted for their genuine monodromy. -/
theorem quotient_closed_curves_elementary_common_powers
    {H : Subgroup Mobius.complexMobiusGroup}
    (hInv : ∀(g:H) z,z∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc→g•z∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc)
    (hD : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn H _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc) (hE : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsEllipticFree H)
    {x : _root_.LowDimensionalTopology.Geometry.Surfaces.MobiusDomainQuotient (_root_.LowDimensionalTopology.Geometry.Surfaces.unitDiscMobiusInvariantDomain H hInv)}
    (p q : _root_.LowDimensionalTopology.Geometry.Surfaces.DiscQuotientPiecewiseC1Curve hInv x x) (z u v : 𝔻)
    (hz : _root_.LowDimensionalTopology.Geometry.Surfaces.discQuotientProjection hInv z=x)
    (c : _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscPiecewiseC1Curve z u)
    (d : _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscPiecewiseC1Curve z v)
    (hc : QuotientPiecewiseCurveLift hInv p c) (hd : QuotientPiecewiseCurveLift hInv q d)
    (f g : H)
    (hfu : f.val.val ((z:ℂ):Mobius.ExtendedComplex)=((u:ℂ):Mobius.ExtendedComplex))
    (hgv : g.val.val ((z:ℂ):Mobius.ExtendedComplex)=((v:ℂ):Mobius.ExtendedComplex))
    (he : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsElementary (Subgroup.closure ({f.val,g.val}:Set Mobius.complexMobiusGroup))) :
    ∃γ : FundamentalGroup (_root_.LowDimensionalTopology.Geometry.Surfaces.MobiusDomainQuotient (_root_.LowDimensionalTopology.Geometry.Surfaces.unitDiscMobiusInvariantDomain H hInv)) x,
      ∃m n : ℤ, (.of (.mk p.toPath))=γ^m ∧ (.of (.mk q.toPath))=γ^n := by
  classical
  let K:=Subgroup.closure ({f.val,g.val}:Set Mobius.complexMobiusGroup)
  let : IsCyclic K := quotient_curve_elementary_pair_isCyclic hInv hD hE f g he
  have hfK : f.val∈K:=Subgroup.subset_closure (by simp)
  have hgK : g.val∈K:=Subgroup.subset_closure (by simp)
  obtain ⟨a,ha⟩ := exists_zpow_surjective K
  obtain ⟨m,hm⟩ := ha ⟨f.val,hfK⟩
  obtain ⟨n,hn⟩ := ha ⟨g.val,hgK⟩
  have hle : K≤H := (Subgroup.closure_le H).mpr (by
    rintro b (rfl|rfl)
    · exact f.property
    · exact g.property)
  let aH : H:=⟨a.val,hle a.property⟩
  have hmH : aH^m=f := Subtype.ext (congrArg (fun b:K=>b.val) hm)
  have hnH : aH^n=g := Subtype.ext (congrArg (fun b:K=>b.val) hn)
  let e:=quotientLoopFundamentalGroupEquiv hInv hD hE x z hz
  refine ⟨e.symm (MulOpposite.op aH),m,n,?_,?_⟩
  · apply e.injective
    rw [map_zpow,e.apply_symm_apply]
    exact (quotientLoopFundamentalGroupEquiv_apply hInv hD hE p z u hz c hc f hfu).trans
      (by rw [←hmH,MulOpposite.op_zpow])
  · apply e.injective
    rw [map_zpow,e.apply_symm_apply]
    exact (quotientLoopFundamentalGroupEquiv_apply hInv hD hE q z v hz d hd g hgv).trans
      (by rw [←hnH,MulOpposite.op_zpow])

/-- Every genuine based homotopy class has an actual continuous closed-curve representative. -/
theorem curveException_exists_loop_representative {X : Type*} [TopologicalSpace X]
    {x : X} (γ : FundamentalGroup X x) :
    ∃Γ : Path x x, FundamentalGroup.fromPath (.mk Γ)=γ := by
  obtain ⟨Γ,hΓ⟩ := Path.Homotopic.Quotient.mk_surjective γ.asHom
  exact ⟨Γ,congrArg FundamentalGroup.fromPath hΓ⟩

/-- The complete closed-curve consequence on the genuine quotient: the sharp length bound,
or both original based homotopy classes are integral powers of one actual closed curve. -/
theorem quotient_closed_curves_length_bound_or_common_loop
    {H : Subgroup Mobius.complexMobiusGroup}
    (hInv : ∀(g:H) z,z∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc→g•z∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc)
    (hD : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn H _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc) (hE : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsEllipticFree H)
    {x : _root_.LowDimensionalTopology.Geometry.Surfaces.MobiusDomainQuotient (_root_.LowDimensionalTopology.Geometry.Surfaces.unitDiscMobiusInvariantDomain H hInv)}
    (p q : _root_.LowDimensionalTopology.Geometry.Surfaces.DiscQuotientPiecewiseC1Curve hInv x x) :
    (1≤Real.sinh (p.length/2)*Real.sinh (q.length/2)) ∨
    ∃Γ : Path x x,∃m n : ℤ,
      FundamentalGroup.fromPath (.mk p.toPath)=(FundamentalGroup.fromPath (.mk Γ))^m ∧
      FundamentalGroup.fromPath (.mk q.toPath)=(FundamentalGroup.fromPath (.mk Γ))^n := by
  obtain ⟨z,hz⟩ := _root_.LowDimensionalTopology.Geometry.Surfaces.discQuotientProjection_surjective hInv x
  obtain ⟨f,g,u,v,c,d,hc,hd,hfu,hgv,he|hbound⟩ :=
    quotient_closed_curves_elementary_or_sinh_length_bound hInv hD hE p q z hz
  · obtain ⟨γ,m,n,hm,hn⟩ :=
      quotient_closed_curves_elementary_common_powers hInv hD hE p q z u v hz c d hc hd f g hfu hgv he
    obtain ⟨Γ,hΓ⟩ := curveException_exists_loop_representative γ
    exact Or.inr ⟨Γ,m,n,by simpa only [hΓ] using hm,by simpa only [hΓ] using hn⟩
  · exact Or.inl hbound

/-- The original surface curve and its conformal quotient image have the same literal path. -/
theorem SurfacePiecewiseC1Curve.toQuotient_path {X : Type*} [TopologicalSpace X]
    {R : _root_.LowDimensionalTopology.Geometry.Surfaces.RiemannSurface X}
    {M : _root_.LowDimensionalTopology.Geometry.Surfaces.HyperbolicSurfaceModel R}
    {x y : X}
    (p : SurfacePiecewiseC1Curve M x y) :
    p.toQuotient.toPath=p.toPath.map M.homeomorph.continuous := by
  induction p with
  | nil x => rfl
  | cons p tail ih =>
    change p.toQuotient.toPath.trans tail.toQuotient.toPath=
      (p.toPath.trans tail.toPath).map M.homeomorph.continuous
    rw [Path.map_trans,ih]
    rfl

/-- The full length consequence on the original Riemann surface, including the elementary
exception as powers of an actual based closed curve, rather than powers of abstract deck maps. -/
theorem surface_closed_curves_length_bound_or_common_loop
    {X : Type*} [TopologicalSpace X] {R : _root_.LowDimensionalTopology.Geometry.Surfaces.RiemannSurface X}
    (M : _root_.LowDimensionalTopology.Geometry.Surfaces.HyperbolicSurfaceModel R)
    {x : X} (p q : SurfacePiecewiseC1Curve M x x) :
    (1≤Real.sinh (p.length/2)*Real.sinh (q.length/2)) ∨
    ∃Γ : Path x x,∃m n : ℤ,
      FundamentalGroup.fromPath (.mk p.toPath)=(FundamentalGroup.fromPath (.mk Γ))^m ∧
      FundamentalGroup.fromPath (.mk q.toPath)=(FundamentalGroup.fromPath (.mk Γ))^n := by
  have hE : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsEllipticFree M.group := fun f hf=>M.no_elliptic f.val f.property hf.1 hf
  rcases quotient_closed_curves_length_bound_or_common_loop M.invariant M.discontinuous hE
    p.toQuotient q.toQuotient with hb | ⟨Γ,m,n,hm,hn⟩
  · exact Or.inl (by simpa only [_root_.LowDimensionalTopology.Geometry.Fuchsian.SurfacePiecewiseC1Curve.toQuotient_length] using hb)
  · let e:=_root_.LowDimensionalTopology.Geometry.Surfaces.fundamentalGroupHomeomorphMulEquiv M.homeomorph x
    have hepath (r : Path x x) : e (FundamentalGroup.fromPath (.mk r))=
        FundamentalGroup.fromPath (.mk (r.map M.homeomorph.continuous)) := by
      rfl
    obtain ⟨Δ,hΔ⟩ := curveException_exists_loop_representative
      (e.symm (FundamentalGroup.fromPath (.mk Γ)))
    refine Or.inr ⟨Δ,m,n,?_,?_⟩
    · apply e.injective
      rw [map_zpow,hΔ,e.apply_symm_apply]
      rw [hepath]
      simpa only [_root_.LowDimensionalTopology.Geometry.Fuchsian.SurfacePiecewiseC1Curve.toQuotient_path] using hm
    · apply e.injective
      rw [map_zpow,hΔ,e.apply_symm_apply]
      rw [hepath]
      simpa only [_root_.LowDimensionalTopology.Geometry.Fuchsian.SurfacePiecewiseC1Curve.toQuotient_path] using hn

/-- Identity monodromy is equivalent to actual nullhomotopy of the original based loop. -/
theorem quotient_closed_curve_nullhomotopic_iff
    {H : Subgroup Mobius.complexMobiusGroup}
    (hInv : ∀(g:H) z,z∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc→g•z∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc)
    (hD : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn H _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc) (hE : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsEllipticFree H)
    {x : _root_.LowDimensionalTopology.Geometry.Surfaces.MobiusDomainQuotient (_root_.LowDimensionalTopology.Geometry.Surfaces.unitDiscMobiusInvariantDomain H hInv)}
    (p : _root_.LowDimensionalTopology.Geometry.Surfaces.DiscQuotientPiecewiseC1Curve hInv x x) (z w : 𝔻)
    (hz : _root_.LowDimensionalTopology.Geometry.Surfaces.discQuotientProjection hInv z=x)
    (c : _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscPiecewiseC1Curve z w)
    (hc : QuotientPiecewiseCurveLift hInv p c) (f : H)
    (hf : f.val.val ((z:ℂ):Mobius.ExtendedComplex)=((w:ℂ):Mobius.ExtendedComplex)) :
    p.toPath.Homotopic (Path.refl x) ↔ f=1 := by
  let e:=quotientLoopFundamentalGroupEquiv hInv hD hE x z hz
  have he:=quotientLoopFundamentalGroupEquiv_apply hInv hD hE p z w hz c hc f hf
  constructor
  · intro h
    have hclass : FundamentalGroup.fromPath (.mk p.toPath)=1 :=
      congrArg FundamentalGroup.fromPath (Quotient.sound h)
    have hop := congrArg e hclass
    rw [he,map_one] at hop
    exact MulOpposite.op_injective hop
  · intro h
    have hclass : FundamentalGroup.fromPath (.mk p.toPath)=1 := by
      apply e.injective
      rw [he,h,map_one]
      rfl
    exact Quotient.exact (congrArg (fun a : FundamentalGroup _ x=>a.asHom) hclass)

end LowDimensionalTopology.Geometry.Fuchsian
