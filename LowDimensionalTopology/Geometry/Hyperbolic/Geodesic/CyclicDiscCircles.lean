/- Released under Apache 2.0 license as described in the file LICENSE. -/
/- Conjugation between actual unit-disc cyclic orbits and native upper-half-plane coordinates, with restriction to actual subgroups. -/
module
public import LowDimensionalTopology.Geometry.Mobius.Circle.IdealBoundaryAction
public import LowDimensionalTopology.Geometry.Hyperbolic.Isometry.CyclicOrbitCircles
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.GeneralizedFundamentalDomains
@[expose] public section
noncomputable section
open Set
open scoped UpperHalfPlane MatrixGroups OnePoint
namespace LowDimensionalTopology.Geometry.Hyperbolic
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

theorem cyclicDisc_coordinate_sphere {H : Subgroup Mobius.complexMobiusGroup}
    (P : Fuchsian.UnitDiscFuchsianGroup H) (z : P.domain.carrier) :
    (cayleyMobius⁻¹).val z.val=(((P.halfPlaneCoordinate z : ℍ) : ℂ) : Mobius.ExtendedComplex):=
  (P.halfPlaneCoordinate_extended z).symm

/-- Conjugation of every original disc group element preserves the entire actual half-plane. -/
theorem cyclicDisc_conjugate_preserves_halfPlane {H : Subgroup Mobius.complexMobiusGroup}
    (P : Fuchsian.UnitDiscFuchsianGroup H) :
    ∀f∈DiscreteGroups.Action.Actions.subgroupConjugate cayleyMobius⁻¹ H,
      f.val '' openHalfPlaneSet=openHalfPlaneSet := by
  rintro f ⟨g,hg,rfl⟩
  change (cayleyMobius⁻¹*g*(cayleyMobius⁻¹)⁻¹).val '' openHalfPlaneSet=openHalfPlaneSet
  rw [←Fuchsian.cayleyInverse_unitDisc_image,Mobius.stableAxis_conjugate_image,P.image_eq ⟨g,hg⟩,
    Fuchsian.cayleyInverse_unitDisc_image]

/-- Literal original orbit points map to literal orbit points of the conjugated group. -/
theorem cyclicDisc_conjugate_orbit {H : Subgroup Mobius.complexMobiusGroup}
    (P : Fuchsian.UnitDiscFuchsianGroup H) (z x : P.domain.carrier) (hx : x∈MulAction.orbit H z) :
    (((P.halfPlaneCoordinate x):ℂ):Mobius.ExtendedComplex)∈
      MulAction.orbit (DiscreteGroups.Action.Actions.subgroupConjugate cayleyMobius⁻¹ H)
        (((P.halfPlaneCoordinate z):ℂ):Mobius.ExtendedComplex) := by
  obtain ⟨g,hg⟩:=hx
  refine ⟨⟨cayleyMobius⁻¹*g.val*(cayleyMobius⁻¹)⁻¹,⟨g.val,g.property,rfl⟩⟩,?_⟩
  rw [←cyclicDisc_coordinate_sphere P x,←cyclicDisc_coordinate_sphere P z]
  change cayleyMobius⁻¹•(g.val•((cayleyMobius⁻¹)⁻¹•(cayleyMobius⁻¹•z.val)))=
    cayleyMobius⁻¹•x.val
  rw [inv_smul_smul]
  exact congrArg (cayleyMobius⁻¹).val (congrArg Subtype.val hg)

theorem cyclicDisc_restrict {H : Subgroup Mobius.complexMobiusGroup} (P : Fuchsian.UnitDiscFuchsianGroup H)
    (K : Subgroup Mobius.complexMobiusGroup) (hKH : K≤H) : Fuchsian.UnitDiscFuchsianGroup K where
  invariant := fun g z hz=>P.invariant ⟨g.val,hKH g.property⟩ z hz
  discontinuous := by
    intro T hTc hTD
    let i : K→H:=fun g=>⟨g.val,hKH g.property⟩
    have hi : Function.Injective i:=by
      intro a b hab
      exact Subtype.ext (congrArg (fun x : H=>x.val) hab)
    change (i ⁻¹' {g : H | (g.val.val '' T ∩ T).Nonempty}).Finite
    exact Set.Finite.preimage hi.injOn (P.discontinuous T hTc hTD)

/-- The original native disc circle obstruction holds for cyclic groups
with elliptics as well: the true Dirichlet center has trivial stabilizer. -/
theorem cyclicDisc_circle_three_free_center {H : Subgroup Mobius.complexMobiusGroup}
    (P : Fuchsian.UnitDiscFuchsianGroup H) (hcyc : IsCyclic H)
    (w : P.domain.carrier) (hw : Fuchsian.IsDirichletCenter P w)
    (z x y u : P.domain.carrier) (r : ℝ)
    (hx : x∈MulAction.orbit H z) (hy : y∈MulAction.orbit H z) (hu : u∈MulAction.orbit H z)
    (hxd : P.hyperbolicDist w x=r) (hyd : P.hyperbolicDist w y=r) (hud : P.hyperbolicDist w u=r) :
    x=y ∨ x=u ∨ y=u := by
  let q:=cayleyMobius⁻¹
  let K:=DiscreteGroups.Action.Actions.subgroupConjugate q H
  have hKcyc : IsCyclic K:=(DiscreteGroups.Action.Actions.subgroupConjugateEquivalence q H).isCyclic.mp hcyc
  have hfree : ∀f∈K,f.val (((P.halfPlaneCoordinate w:ℍ):ℂ):Mobius.ExtendedComplex)=
      (((P.halfPlaneCoordinate w:ℍ):ℂ):Mobius.ExtendedComplex)→f=1:=by
    rintro f ⟨g,hg,rfl⟩ hfix
    rw [←cyclicDisc_coordinate_sphere P w] at hfix
    change (q*g*q⁻¹)•(q•w.val)=q•w.val at hfix
    have hgfix : g.val w.val=w.val:=q.val.injective (by
      change q•(g•w.val)=q•w.val
      simpa only [mul_smul,inv_smul_smul] using hfix)
    have hg1 : g=1:=congrArg Subtype.val (hw ⟨g,hg⟩ (Subtype.ext hgfix))
    change q*g*q⁻¹=1
    rw [hg1,mul_one,mul_inv_cancel]
  have hh:=cyclicMobius_halfPlane_circle_three_free_center K hKcyc
    (cyclicDisc_conjugate_preserves_halfPlane P) (P.halfPlaneCoordinate z) (P.halfPlaneCoordinate w)
    (P.halfPlaneCoordinate x) (P.halfPlaneCoordinate y) (P.halfPlaneCoordinate u) r hfree
    (cyclicDisc_conjugate_orbit P z x hx) (cyclicDisc_conjugate_orbit P z y hy)
    (cyclicDisc_conjugate_orbit P z u hu) hxd hyd hud
  rcases hh with hh|hh|hh
  · exact Or.inl (P.halfPlaneCoordinate.injective hh)
  · exact Or.inr (Or.inl (P.halfPlaneCoordinate.injective hh))
  · exact Or.inr (Or.inr (P.halfPlaneCoordinate.injective hh))

/-- Three actual distinct original orbit points on the Dirichlet circle
exclude the cyclic branch of their original generated subgroup, without
excluding elliptic transformations from the group. -/
theorem cyclicDisc_pair_not_cyclic {H : Subgroup Mobius.complexMobiusGroup}
    (P : Fuchsian.UnitDiscFuchsianGroup H) (w : P.domain.carrier) (hw : Fuchsian.IsDirichletCenter P w)
    (z : P.domain.carrier) (f g : H) (r : ℝ)
    (hz : P.hyperbolicDist w z=r) (hf : P.hyperbolicDist w (f•z)=r)
    (hg : P.hyperbolicDist w (g•z)=r)
    (hzf : z≠f•z) (hzg : z≠g•z) (hfg : f•z≠g•z) :
    ¬IsCyclic (Subgroup.closure ({f.val,g.val}:Set Mobius.complexMobiusGroup)) := by
  let K:=Subgroup.closure ({f.val,g.val}:Set Mobius.complexMobiusGroup)
  have hKH : K≤H:=(Subgroup.closure_le H).2
    (by intro x hx;rcases hx with rfl|rfl;exact f.property;exact g.property)
  let PK:=cyclicDisc_restrict P K hKH
  have hwK : Fuchsian.IsDirichletCenter PK w:=by
    intro k hk
    have heH : (⟨k.val,hKH k.property⟩:H)=1:=hw ⟨k.val,hKH k.property⟩ hk
    have heval : k.val=1:=congrArg (fun u:H=>u.val) heH
    exact Subtype.ext heval
  intro hcyc
  let fK : K:=⟨f.val,Subgroup.subset_closure (by simp)⟩
  let gK : K:=⟨g.val,Subgroup.subset_closure (by simp)⟩
  have hh:=cyclicDisc_circle_three_free_center PK hcyc w hwK z z (f•z) (g•z) r
    ⟨1,one_smul _ _⟩ ⟨fK,rfl⟩ ⟨gK,rfl⟩ hz hf hg
  exact hh.elim hzf (fun h=>h.elim hzg hfg)


end LowDimensionalTopology.Geometry.Hyperbolic
