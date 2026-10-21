/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.Ford.HorocyclicFanTriangles
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.NativeFuchsianPolygons
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.Vertex.PolygonAngles
public import LowDimensionalTopology.Geometry.Fuchsian.Ford.FordEllipticHeights
public import Mathlib.Data.Fintype.Sort
@[expose] public section
noncomputable section
open Set Filter MeasureTheory
open scoped Topology OnePoint Pointwise UpperHalfPlane Complex.UnitDisc BigOperators
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Surfaces LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
/-- At a vertex of a finite interval fan, sum its actual incident triangle contributions. -/
def intervalFanCornerContribution {n : ℕ} (θ : Fin n→ℝ) (i : Fin (n+1)) : ℝ:=
  Fin.lastCases (motive:=fun _=>ℝ) (0:ℝ) θ i + Fin.cases (motive:=fun _=>ℝ) (0:ℝ) θ i

/-- Each genuine triangle contributes once at each of its two finite endpoints. -/
theorem intervalFanCornerContribution_sum {n : ℕ} (θ : Fin n→ℝ) :
    ∑i,intervalFanCornerContribution θ i=2*∑i,θ i := by
  unfold intervalFanCornerContribution
  rw [Finset.sum_add_distrib]
  have hright : ∑i,Fin.lastCases (motive:=fun _=>ℝ) (0:ℝ) θ i=∑i,θ i:=by
    rw [Fin.sum_univ_castSucc]
    simp
  have hleft : ∑i,Fin.cases (motive:=fun _=>ℝ) (0:ℝ) θ i=∑i,θ i:=by
    rw [Fin.sum_univ_succ]
    simp
  rw [hright,hleft]
  ring

/-- Actual base angles of the ordered one-ideal fan. -/
def horocyclicFanBaseAngle {n : ℕ} (p : Fin (n+1)→ℍ)
    (hx : StrictMono (fun i=>(p i).re)) (i : Fin n) : ℝ:=
  (horocyclicFanTriangle (p i.castSucc) (p i.succ) (hx i.castSucc_lt_succ)).alpha

/-- One actual finite base angle fits inside its containing original sector. -/
theorem horocyclicFanTriangle_alpha_le (z w : ℍ) (hx : z.re<w.re)
    (S : Set ℍ) (hS : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HConvex S) (hclosed : IsClosed S) (hz : z∈S) (hw
      : w∈S)
    (hi : _root_.LowDimensionalTopology.Geometry.Hyperbolic.twoIdealInfiniteEndpoint∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneClosedModelClosure S) :
    (horocyclicFanTriangle z w hx).alpha≤
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.discSubtendedAngle (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc '' S) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z) :=
  cycle_triangle_angle_le _ _ _ (horocyclicFanTriangle_a z w hx)
    (horocyclicFanTriangle_finiteCarrier_subset z w hx S hS hclosed hz hw hi)

/-- The other actual finite base angle has the corresponding genuine sector bound. -/
theorem horocyclicFanTriangle_beta_le (z w : ℍ) (hx : z.re<w.re)
    (S : Set ℍ) (hS : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HConvex S) (hclosed : IsClosed S) (hz : z∈S) (hw
      : w∈S)
    (hi : _root_.LowDimensionalTopology.Geometry.Hyperbolic.twoIdealInfiniteEndpoint∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneClosedModelClosure S) :
    (horocyclicFanTriangle z w hx).beta≤
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.discSubtendedAngle (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc '' S) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc w) := by
  let T:=horocyclicFanTriangle z w hx
  apply cycle_triangle_angle_le T.cycle _ _ (horocyclicFanTriangle_b z w hx)
  rw [T.cycle.finiteCarrier_eq_closure,T.cycle_interior,←T.finiteCarrier_eq_closure]
  exact horocyclicFanTriangle_finiteCarrier_subset z w hx S hS hclosed hz hw hi

/-- Every actual original fan vertex has exactly its geometrically incident
base angles, bounded by the original containing region's measured sector. -/
theorem horocyclicFanCornerContribution_le {n : ℕ} (p : Fin (n+1)→ℍ)
    (hx : StrictMono (fun i=>(p i).re)) (hy : ∀i j,(p i).im=(p j).im)
    (S : Set ℍ) (hS : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HConvex S) (hclosed : IsClosed S) (hp : ∀i,p
      i∈S)
    (hi : _root_.LowDimensionalTopology.Geometry.Hyperbolic.twoIdealInfiniteEndpoint∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneClosedModelClosure S) (i : Fin (n+1)) :
    intervalFanCornerContribution (horocyclicFanBaseAngle p hx) i≤
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.discSubtendedAngle (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc '' S) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (p i)) := by
  cases n with
  | zero =>
      have hz : intervalFanCornerContribution (horocyclicFanBaseAngle p hx) i=0:=by
        fin_cases i
        change Fin.lastCases (motive:=fun _=>ℝ) (0:ℝ) (horocyclicFanBaseAngle p hx) (Fin.last 0)+
          Fin.cases (motive:=fun _=>ℝ) (0:ℝ) (horocyclicFanBaseAngle p hx) 0=0
        rw [Fin.lastCases_last,Fin.cases_zero,add_zero]
      rw [hz]
      unfold _root_.LowDimensionalTopology.Geometry.Hyperbolic.discSubtendedAngle
      positivity
  | succ k =>
      refine Fin.cases ?_ (fun j=>?_) i
      · have h:=horocyclicFanTriangle_alpha_le (p (0:Fin (k+1)).castSucc)
          (p (0:Fin (k+1)).succ) (hx (0:Fin (k+1)).castSucc_lt_succ)
          S hS hclosed (hp _) (hp _) hi
        change Fin.lastCases (motive:=fun _=>ℝ) (0:ℝ) (horocyclicFanBaseAngle p hx) (0:Fin (k+1)).castSucc+0≤_
        rw [Fin.lastCases_castSucc,add_zero]
        exact h
      · refine Fin.lastCases ?_ (fun j=>?_) j
        · have h:=horocyclicFanTriangle_beta_le (p (Fin.last k).castSucc) (p (Fin.last k).succ)
            (hx (Fin.last k).castSucc_lt_succ) S hS hclosed (hp _) (hp _) hi
          rw [←horocyclicFanTriangle_alpha_eq_beta _ _ _ (hy _ _)] at h
          have hout : Fin.lastCases (motive:=fun _=>ℝ) (0:ℝ) (horocyclicFanBaseAngle p hx) (Fin.last k).succ=0:=by
            change Fin.lastCases (motive:=fun _=>ℝ) (0:ℝ) (horocyclicFanBaseAngle p hx) (Fin.last (k+1))=0
            rw [Fin.lastCases_last]
          change Fin.lastCases (motive:=fun _=>ℝ) (0:ℝ) (horocyclicFanBaseAngle p hx) (Fin.last k).succ+
            horocyclicFanBaseAngle p hx (Fin.last k)≤_
          rw [hout,zero_add]
          exact h
        · have h:=horocyclicFanTriangle_adjacent_angle_le (p j.castSucc.castSucc)
            (p j.castSucc.succ) (p j.succ.succ)
            (hx j.castSucc.castSucc_lt_succ) (hx (by simp))
            S hS hclosed (hp _) (hp _) (hp _) hi
          rw [←horocyclicFanTriangle_alpha_eq_beta _ _ _ (hy _ _)] at h
          simp only [intervalFanCornerContribution,Fin.succ_castSucc,Fin.lastCases_castSucc]
          rw [add_comm]
          exact h



/-- The literal original half-plane Ford cycle and the actual conjugate
fundamental-polygon cycle correspond under the genuine Cayley coordinate. -/
theorem parabolicFord_cycle_cayley {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : HalfPlaneFuchsianGroup H) (z : ℍ) :
    fuchsianPolygonCycle P.cayleyData (P.cayleyCoordinate '' parabolicFordDomain H)
        (P.cayleyCoordinate z)=
      P.cayleyCoordinate '' _root_.LowDimensionalTopology.Geometry.Fuchsian.mobiusFordVertexCycle H 0 z := by
  let parabolicFordCycleHalfPlaneAction:=P.nativeAction
  let e:=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugateEquivalence _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius H
  ext x
  constructor
  · rintro ⟨hxC,g,hgx⟩
    rw [←P.cayleyCoordinate.image_closure] at hxC
    obtain ⟨u,hu,rfl⟩:=hxC
    have hgu : e.symm g • z=u:=by
      apply P.cayleyCoordinate.injective
      rw [P.cayleyCoordinate_equivariant,e.apply_symm_apply]
      exact hgx
    refine ⟨u,⟨?_,⟨e.symm g,?_⟩⟩,rfl⟩
    · rwa [←parabolicFordDomain_eq_mobiusFordDomain H]
    · change (e.symm g).val.val ((z:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)=((u:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)
      change (e.symm g).val.val (_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint
        z)=_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint u
      rw [P.nativeAction_boundary,hgu]
  · rintro ⟨u,⟨hu,g,hgu⟩,rfl⟩
    have hgn : g•z=u:=by
      apply _root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint_injective
      rw [←P.nativeAction_boundary]
      exact hgu
    refine ⟨?_,⟨e g,?_⟩⟩
    · rw [←P.cayleyCoordinate.image_closure]
      apply mem_image_of_mem
      rwa [parabolicFordDomain_eq_mobiusFordDomain H]
    · change _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugateEquivalence _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius H g • P.cayleyCoordinate z=_
      rw [←P.cayleyCoordinate_equivariant,hgn]

/-- A true primitive parabolic Ford cycle is finite, using the genuine
fundamental polygon and the actual original orbit. -/
theorem parabolicFord_cycle_finite {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : HalfPlaneFuchsianGroup H) (hprim : IsPrimitive H
      (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1)) (z : ℍ) :
    (_root_.LowDimensionalTopology.Geometry.Fuchsian.mobiusFordVertexCycle H 0 z).Finite := by
  have hP:=primitive_unitTranslation_Ford_polygon P hprim
  have hh:=hP.locallyFinite.cycle_finite (P.cayleyCoordinate z)
  rw [parabolicFord_cycle_cayley] at hh
  exact hh.of_finite_image P.cayleyCoordinate.injective.injOn

/-- Real coordinate is injective on the literal actual Ford cycle because
all of its points have the same original height. -/
theorem parabolicFord_cycle_re_injective {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : HalfPlaneFuchsianGroup H) (z : ℍ) (hz : z∈closure (parabolicFordDomain H)) :
    InjOn UpperHalfPlane.re (_root_.LowDimensionalTopology.Geometry.Fuchsian.mobiusFordVertexCycle H 0 z) := by
  have hpres : ∀f∈H,f.val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet=_root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet:=fun f hf=>P.preserves ⟨f,hf⟩
  have hz' : z∈closure (_root_.LowDimensionalTopology.Geometry.Fuchsian.mobiusFordDomain H 0):=by
    rwa [←parabolicFordDomain_eq_mobiusFordDomain H]
  intro u hu v hv he
  have hU:=_root_.LowDimensionalTopology.Geometry.Fuchsian.mobiusFordVertexCycle_horizontal H hpres 0 z hz' hu
  have hV:=_root_.LowDimensionalTopology.Geometry.Fuchsian.mobiusFordVertexCycle_horizontal H hpres 0 z hz' hv
  apply UpperHalfPlane.ext
  exact Complex.ext he (hU.trans hV.symm)

/-- A finite genuine horizontal cycle has an increasing enumeration that
retains each original native point, rather than replacing it by scalar data. -/
theorem parabolicFord_cycle_order {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : HalfPlaneFuchsianGroup H) (hprim : IsPrimitive H
      (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1))
    (z : ℍ) (hz : z∈closure (parabolicFordDomain H)) :
    let s:=(parabolicFord_cycle_finite P hprim z).toFinset
    ∃e : Fin s.card≃s,StrictMono (fun i=>((e i).val).re) := by
  classical
  let s:=(parabolicFord_cycle_finite P hprim z).toFinset
  let f : s→ℝ:=fun x=>x.val.re
  have hi : Function.Injective f:=by
    intro x y he
    apply Subtype.ext
    exact parabolicFord_cycle_re_injective P z hz
      ((parabolicFord_cycle_finite P hprim z).mem_toFinset.mp x.property)
      ((parabolicFord_cycle_finite P hprim z).mem_toFinset.mp y.property) he
  let parabolicFordCycleRealLinearOrder : LinearOrder s:=LinearOrder.lift' f hi
  let e : Fin s.card≃o s:=monoEquivOfFin s (Fintype.card_coe s)
  refine ⟨e.toEquiv,?_⟩
  intro i j hij
  exact e.strictMono hij

/-- The genuine base-angle sum is bounded by half the original containing
region's actual vertex-angle sum. -/
theorem horocyclicFanBaseAngle_sum_le {n : ℕ} (p : Fin (n+1)→ℍ)
    (hx : StrictMono (fun i=>(p i).re)) (hy : ∀i j,(p i).im=(p j).im)
    (S : Set ℍ) (hS : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HConvex S) (hclosed : IsClosed S) (hp : ∀i,p
      i∈S)
    (hi : _root_.LowDimensionalTopology.Geometry.Hyperbolic.twoIdealInfiniteEndpoint∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneClosedModelClosure S) :
    2*(∑i,horocyclicFanBaseAngle p hx i)≤
      ∑i,_root_.LowDimensionalTopology.Geometry.Hyperbolic.discSubtendedAngle (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc '' S) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (p i)) := by
  have h:=Finset.sum_le_sum (fun i (_ : i∈(Finset.univ:Finset (Fin (n+1))))=>
    horocyclicFanCornerContribution_le p hx hy S hS hclosed hp hi i)
  rwa [intervalFanCornerContribution_sum] at h

/-- The angle at the actual conjugate Ford polygon is exactly the true
native angle of the original half-plane Ford closure. -/
theorem parabolicFord_native_polygon_angle {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : HalfPlaneFuchsianGroup H) (z : ℍ) :
    fuchsianPolygonAngle P.cayleyData (P.cayleyCoordinate '' parabolicFordDomain H)
        (P.cayleyCoordinate z)=
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.discSubtendedAngle (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc '' closure (parabolicFordDomain H))
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z) := by
  have he : P.cayleyData.finiteCoordinate '' closure (P.cayleyCoordinate '' parabolicFordDomain H)=
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc '' closure (parabolicFordDomain H):=by
    rw [←P.cayleyCoordinate.image_closure,image_image]
    exact image_congr (fun u _=>P.cayleyCoordinate_finite u)
  change _root_.LowDimensionalTopology.Geometry.Hyperbolic.discSubtendedAngle
    (P.cayleyData.finiteCoordinate '' closure (P.cayleyCoordinate '' parabolicFordDomain H))
    (P.cayleyData.finiteCoordinate (P.cayleyCoordinate z))=_
  rw [he,P.cayleyCoordinate_finite]

/-- The finite actual Ford fan uses only the original polygon's true angles. -/
theorem parabolicFordFanBaseAngle_sum_le {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : HalfPlaneFuchsianGroup H) (hT : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1∈H) {n
      : ℕ}
    (p : Fin (n+1)→ℍ) (hx : StrictMono (fun i=>(p i).re))
    (hy : ∀i j,(p i).im=(p j).im) (hp : ∀i,p i∈closure (parabolicFordDomain H)) :
    2*(∑i,horocyclicFanBaseAngle p hx i)≤
      ∑i,fuchsianPolygonAngle P.cayleyData (P.cayleyCoordinate '' parabolicFordDomain H)
        (P.cayleyCoordinate (p i)) := by
  have hp' : ∀i,p i∈parabolicFordClosedStrip H:=by
    intro i
    simpa only [closure_parabolicFordDomain H P.discrete hT] using hp i
  have h:=horocyclicFanBaseAngle_sum_le p hx hy (parabolicFordClosedStrip H)
    (parabolicFordClosedStrip_hConvex H P.discrete hT) (parabolicFordClosedStrip_isClosed H) hp'
    (parabolicFordClosedStrip_infty_mem_closedModelClosure H P.discrete hT)
  rw [←closure_parabolicFordDomain H P.discrete hT] at h
  simpa only [parabolicFord_native_polygon_angle] using h

/-- The full original cycle supplies the finite fan budget; it is proved
from the genuine fundamental polygon and original orbit, never supplied
as an independent hypothesis. -/
theorem parabolicFord_cycle_fan_angle_budget {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : HalfPlaneFuchsianGroup H) (hprim : IsPrimitive H
      (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1))
    (z : ℍ) {n : ℕ} (p : Fin (n+1)→ℍ) (hx : StrictMono (fun i=>(p i).re))
    (hy : ∀i j,(p i).im=(p j).im) (hrange : range
      p=_root_.LowDimensionalTopology.Geometry.Fuchsian.mobiusFordVertexCycle H 0 z) :
    (∑i,horocyclicFanBaseAngle p hx i)≤
      Real.pi/(fuchsianPointOrder P.cayleyData (P.cayleyCoordinate z):ℝ) := by
  classical
  let Q:=P.cayleyData
  let D:=P.cayleyCoordinate '' parabolicFordDomain H
  have hD:=primitive_unitTranslation_Ford_polygon P hprim
  let s:=(hD.locallyFinite.cycle_finite (P.cayleyCoordinate z)).toFinset
  have hpC (i : Fin (n+1)) : P.cayleyCoordinate (p i)∈s:=by
    apply (Set.Finite.mem_toFinset _).mpr
    rw [parabolicFord_cycle_cayley]
    apply mem_image_of_mem
    rw [←hrange]
    exact mem_range_self i
  let e : Fin (n+1)≃s:=Equiv.ofBijective (fun i=>⟨P.cayleyCoordinate (p i),hpC i⟩) (by
    constructor
    · intro i j he
      exact hx.injective (congrArg UpperHalfPlane.re
        (P.cayleyCoordinate.injective (congrArg Subtype.val he)))
    · intro y
      have hyC:=(Set.Finite.mem_toFinset _).mp y.property
      rw [parabolicFord_cycle_cayley] at hyC
      obtain ⟨u,hu,he⟩:=hyC
      rw [←hrange] at hu
      obtain ⟨i,rfl⟩:=hu
      exact ⟨i,Subtype.ext he⟩)
  have hp (i : Fin (n+1)) : p i∈closure (parabolicFordDomain H):=by
    have hpi : p i∈_root_.LowDimensionalTopology.Geometry.Fuchsian.mobiusFordVertexCycle H 0 z:=hrange ▸ mem_range_self i
    simpa only [←parabolicFordDomain_eq_mobiusFordDomain H] using hpi.1
  have hbudget:=parabolicFordFanBaseAngle_sum_le P hprim.mem p hx hy hp
  have hangles : (∑i,fuchsianPolygonAngle Q D (P.cayleyCoordinate (p i)))=
      2*Real.pi/(fuchsianPointOrder Q (P.cayleyCoordinate z):ℝ):=by
    calc
      _=∑y:s,fuchsianPolygonAngle Q D y.val:=Equiv.sum_comp e _
      _=∑y∈s,fuchsianPolygonAngle Q D y:=Finset.sum_coe_sort _ _
      _=2*Real.pi/(fuchsianPointOrder Q (P.cayleyCoordinate z):ℝ):=
        sum_cycle_angles_eq_two_pi_div_pointOrder hD (P.cayleyCoordinate z)
  change 2*(∑i,horocyclicFanBaseAngle p hx i)≤∑i,fuchsianPolygonAngle Q D _ at hbudget
  rw [hangles] at hbudget
  have he : 2*Real.pi/(fuchsianPointOrder Q (P.cayleyCoordinate z):ℝ)=
      2*(Real.pi/(fuchsianPointOrder Q (P.cayleyCoordinate z):ℝ)):=by ring
  rw [he] at hbudget
  linarith only [hbudget]

/-- Choosing an original cycle point on the first strip edge also puts its
actual unit translate on the second edge of the same literal cycle. -/
theorem parabolicFord_cycle_endpoint_pair {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : HalfPlaneFuchsianGroup H) (hT : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1∈H) (z
      : ℍ)
    (hz : z∈closure (parabolicFordDomain H)) (hre : z.re=0) :
    z∈_root_.LowDimensionalTopology.Geometry.Fuchsian.mobiusFordVertexCycle H 0 z ∧
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1•z∈_root_.LowDimensionalTopology.Geometry.Fuchsian.mobiusFordVertexCycle H 0 z := by
  have hzS : z∈parabolicFordClosedStrip H:=by
    rwa [closure_parabolicFordDomain H P.discrete hT] at hz
  have ht : (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1•z).re=z.re+1:=by
    change ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1•z:ℍ):ℂ).re=z.re+1
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL_coe]
    simp
  have hExt : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1•z∈_root_.LowDimensionalTopology.Geometry.Fuchsian.mobiusFordExterior H:=by
    simpa only [Int.cast_one] using parabolicFordExterior_integer_translate H hT z hzS.2.2 1
  constructor
  · refine ⟨?_,⟨1,?_⟩⟩
    · rwa [←parabolicFordDomain_eq_mobiusFordDomain H]
    · rfl
  · refine ⟨?_,⟨⟨_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1,hT⟩,?_⟩⟩
    · rw [←parabolicFordDomain_eq_mobiusFordDomain H,closure_parabolicFordDomain H P.discrete hT]
      refine ⟨?_,?_,hExt⟩ <;> rw [ht,hre] <;> norm_num
    · change (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation
      1).val ((z:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)=_
      rw [←_root_.LowDimensionalTopology.Geometry.Fuchsian.realSLMobius_unitTranslation,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_action]

/-- Both actual period endpoints are distinct, so the augmented original
cycle has at least two points. -/
theorem parabolicFord_cycle_card_ge_two {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : HalfPlaneFuchsianGroup H) (hprim : IsPrimitive H
      (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1)) (z : ℍ)
    (hz : z∈closure (parabolicFordDomain H)) (hre : z.re=0) :
    2≤(parabolicFord_cycle_finite P hprim z).toFinset.card := by
  obtain ⟨h0,h1⟩:=parabolicFord_cycle_endpoint_pair P hprim.mem z hz hre
  have hne : z≠_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1•z:=by
    intro he
    have h:=congrArg UpperHalfPlane.re he
    change z.re=((_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1•z:ℍ):ℂ).re at h
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL_coe] at h
    simp at h
  have hcard:=Finset.one_lt_card.mpr
    ⟨z,(parabolicFord_cycle_finite P hprim z).mem_toFinset.mpr h0,
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1•z,(parabolicFord_cycle_finite P hprim
        z).mem_toFinset.mpr h1,hne⟩
  omega

/-- All finite fan vertices, their genuine order, equal heights and actual
period endpoints are constructed from the original primitive Ford cycle. -/
theorem parabolicFord_cycle_ordered_fan {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : HalfPlaneFuchsianGroup H) (hprim : IsPrimitive H
      (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1)) (z : ℍ)
    (hz : z∈closure (parabolicFordDomain H)) (hre : z.re=0) :
    ∃(n : ℕ) (p : Fin (n+1)→ℍ), 0<n ∧
      n+1=(parabolicFord_cycle_finite P hprim z).toFinset.card ∧
      StrictMono (fun i=>(p i).re) ∧
      range p=_root_.LowDimensionalTopology.Geometry.Fuchsian.mobiusFordVertexCycle H 0 z ∧
      (∀i,(p i).im=z.im) ∧ p 0=z ∧ p (Fin.last n)=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1•z := by
  classical
  let C:=_root_.LowDimensionalTopology.Geometry.Fuchsian.mobiusFordVertexCycle H 0 z
  let s:=(parabolicFord_cycle_finite P hprim z).toFinset
  have hc : 2≤s.card:=parabolicFord_cycle_card_ge_two P hprim z hz hre
  obtain ⟨e,he⟩:=parabolicFord_cycle_order P hprim z hz
  let n:=s.card-1
  have hn : 0<n:=by dsimp [n];omega
  have hnC : n+1=s.card:=by dsimp [n];omega
  let p : Fin (n+1)→ℍ:=fun i=>(e (finCongr hnC i)).val
  have hx : StrictMono (fun i=>(p i).re):=by
    intro i j hij
    exact he hij
  have hrange : range p=C:=by
    ext u
    constructor
    · rintro ⟨i,rfl⟩
      exact (parabolicFord_cycle_finite P hprim z).mem_toFinset.mp (e (finCongr hnC i)).property
    · intro hu
      have hus : u∈s:=(parabolicFord_cycle_finite P hprim z).mem_toFinset.mpr hu
      refine ⟨(finCongr hnC).symm (e.symm ⟨u,hus⟩),?_⟩
      simp [p]
  have hpC (i : Fin (n+1)) : p i∈C:=hrange ▸ mem_range_self i
  have hpres : ∀f∈H,f.val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet=_root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet:=fun f hf=>P.preserves ⟨f,hf⟩
  have hz' : z∈closure (_root_.LowDimensionalTopology.Geometry.Fuchsian.mobiusFordDomain H 0):=by
    rwa [←parabolicFordDomain_eq_mobiusFordDomain H]
  have hy (i : Fin (n+1)) : (p i).im=z.im:=
    _root_.LowDimensionalTopology.Geometry.Fuchsian.mobiusFordVertexCycle_horizontal H hpres 0 z hz' (hpC i)
  have hsub (i : Fin (n+1)) : 0≤(p i).re ∧ (p i).re≤1:=by
    have hh:=(hpC i).1
    rw [←parabolicFordDomain_eq_mobiusFordDomain H,closure_parabolicFordDomain H P.discrete hprim.mem] at hh
    exact ⟨hh.1,hh.2.1⟩
  obtain ⟨hzero,hone⟩:=parabolicFord_cycle_endpoint_pair P hprim.mem z hz hre
  change z∈C at hzero
  change _root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1•z∈C at hone
  rw [←hrange] at hzero hone
  obtain ⟨i0,hi0⟩:=hzero
  obtain ⟨i1,hi1⟩:=hone
  have hfirst : p 0=z:=by
    apply UpperHalfPlane.ext
    apply Complex.ext
    · change (p 0).re=z.re
      rw [hre]
      have hle:=hx.monotone (Fin.zero_le i0)
      rw [hi0,hre] at hle
      exact le_antisymm hle (hsub 0).1
    · exact hy 0
  have hlast : p (Fin.last n)=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1•z:=by
    apply UpperHalfPlane.ext
    apply Complex.ext
    · change (p (Fin.last n)).re=(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1•z).re
      have hge:=hx.monotone (Fin.le_last i1)
      rw [hi1] at hge
      have ht : (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1•z).re=1:=by
        change ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1•z:ℍ):ℂ).re=1
        rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL_coe]
        change z.re+1=1
        rw [hre,zero_add]
      rw [ht] at hge ⊢
      exact le_antisymm (hsub _).2 hge
    · change (p (Fin.last n)).im=((_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1•z:ℍ):ℂ).im
      rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL_coe]
      simpa using hy (Fin.last n)
  exact ⟨n,p,hn,hnC,hx,hrange,hy,hfirst,hlast⟩

/-- Actual source one-period acute-angle data are all constructed from the
original primitive Ford group and original cycle, including the exact
horizontal projection and the proved true cycle-angle budget. -/
theorem parabolicFord_cycle_angle_partition {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : HalfPlaneFuchsianGroup H) (hprim : IsPrimitive H
      (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1)) (z : ℍ)
    (hz : z∈closure (parabolicFordDomain H)) (hre : z.re=0) :
    ∃(n : ℕ) (θ : Fin n→ℝ), 0<n ∧
      n+1=(parabolicFord_cycle_finite P hprim z).toFinset.card ∧
      (∀i,θ i∈Ioo (0:ℝ) (Real.pi/2)) ∧
      (∑i,θ i)≤Real.pi/(fuchsianPointOrder P.cayleyData (P.cayleyCoordinate z):ℝ) ∧
      (∑i,z.im*Real.cot (θ i))=1/2 := by
  obtain ⟨n,p,hn,hnC,hx,hrange,hy,hfirst,hlast⟩:=parabolicFord_cycle_ordered_fan P hprim z hz hre
  let hstep : ∀i:Fin n,(p i.castSucc).re<(p i.succ).re:=fun i=>hx i.castSucc_lt_succ
  let θ:=horocyclicPartitionAngles p hstep
  have hy' : ∀i,(p i).im=(p 0).im:=by intro i;rw [hy i,hfirst]
  have he (i : Fin n) : θ i=horocyclicFanBaseAngle p hx i:=by
    symm
    exact horocyclicFanTriangle_alpha _ _ _
  have hbudget:=parabolicFord_cycle_fan_angle_budget P hprim z p hx
    (fun i j=>(hy i).trans (hy j).symm) hrange
  have hwidth : (p (Fin.last n)).re=(p 0).re+1:=by
    rw [hfirst,hlast]
    change ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1•z:ℍ):ℂ).re=z.re+1
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL_coe]
    simp
  have hproj:=horocyclicPartitionAngles_projection p hstep hy' hwidth
  rw [hfirst] at hproj
  refine ⟨n,θ,hn,hnC,horocyclicPartitionAngles_acute p hstep hy',?_,hproj⟩
  simpa only [he] using hbudget

/-- The exact finite height inequality is now derived from the original
normalized Ford cycle, rather than from supplied numerical angle data.
The real tangent expression is used only away from its pole. -/
theorem parabolicFord_normalized_cycle_height_bound {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : HalfPlaneFuchsianGroup H) (hprim : IsPrimitive H
      (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1)) (z : ℍ)
    (hz : z∈closure (parabolicFordDomain H)) (hre : z.re=0)
    (hqn : 2<fuchsianPointOrder P.cayleyData (P.cayleyCoordinate z)*
      ((_root_.LowDimensionalTopology.Geometry.Fuchsian.mobiusFordVertexCycle H 0 z).ncard-1)) :
    z.im≤cycleHeightBound (fuchsianPointOrder P.cayleyData (P.cayleyCoordinate z))
      ((_root_.LowDimensionalTopology.Geometry.Fuchsian.mobiusFordVertexCycle H 0 z).ncard-1) := by
  obtain ⟨n,θ,hn,hnC,hθ,hbudget,hproj⟩:=parabolicFord_cycle_angle_partition P hprim z hz hre
  have hncard : n=(_root_.LowDimensionalTopology.Geometry.Fuchsian.mobiusFordVertexCycle H 0 z).ncard-1:=by
    rw [Set.ncard_eq_toFinset_card _ (parabolicFord_cycle_finite P hprim z)]
    omega
  rw [←hncard] at hqn ⊢
  exact horocyclic_height_bound_from_angle_partition hn (P.cayleyData.pointOrder_pos _) hqn
    θ z hθ hbudget hproj

/-- The conjugate polygon point order is exactly the original group's
independently defined boundary-point stabilizer order. -/
theorem parabolicFord_cayley_pointOrder {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : HalfPlaneFuchsianGroup H) (z : ℍ) :
    fuchsianPointOrder P.cayleyData (P.cayleyCoordinate z)=fordPointOrder H z := by
  have hcoord : (P.cayleyCoordinate z).val=_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius.val ((z:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex):=by
    have he:=_root_.LowDimensionalTopology.Geometry.Surfaces.discFiniteHomeomorph_symm_coe (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z)
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius_apply,_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedCayley_halfPlane]
    exact he
  calc
    fuchsianPointOrder P.cayleyData (P.cayleyCoordinate z)=
        Nat.card (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusBoundaryStabilizer
          (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate
          _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius H)
          (P.cayleyCoordinate z).val):=
      Nat.card_congr (P.cayleyData.stabilizerEquivBoundary (P.cayleyCoordinate z)).toEquiv
    _=Nat.card (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius
        (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusBoundaryStabilizer H ((z:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex))):=by
      rw [hcoord,primitive_boundaryStabilizer_conjugation]
    _=fordPointOrder H z:=
      (Nat.card_congr (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugateEquivalence
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius
        (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusBoundaryStabilizer H
          ((z:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex))).toEquiv).symm

/-- The genuine normalized original Ford-cycle height inequality, expressed
with its original group's actual point order and actual one-period length. -/
theorem parabolicFord_original_cycle_height_bound {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : HalfPlaneFuchsianGroup H) (hprim : IsPrimitive H
      (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1)) (z : ℍ)
    (hz : z∈closure (parabolicFordDomain H)) (hre : z.re=0)
    (hqn : 2<fordPointOrder H z*((_root_.LowDimensionalTopology.Geometry.Fuchsian.mobiusFordVertexCycle H 0
      z).ncard-1)) :
    z.im≤cycleHeightBound (fordPointOrder H z) ((_root_.LowDimensionalTopology.Geometry.Fuchsian.mobiusFordVertexCycle H 0 z).ncard-1) := by
  have hqn' : 2<fuchsianPointOrder P.cayleyData (P.cayleyCoordinate z)*
      ((_root_.LowDimensionalTopology.Geometry.Fuchsian.mobiusFordVertexCycle H 0 z).ncard-1):=by
    simpa only [parabolicFord_cayley_pointOrder] using hqn
  simpa only [parabolicFord_cayley_pointOrder] using
    parabolicFord_normalized_cycle_height_bound P hprim z hz hre hqn'

end LowDimensionalTopology.Geometry.Fuchsian
