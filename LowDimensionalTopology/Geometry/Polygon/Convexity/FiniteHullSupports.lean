module
public import LowDimensionalTopology.Geometry.Euclidean.Convexity.FiniteHull
public import LowDimensionalTopology.Geometry.Hyperbolic.Models.Klein.Closed
public import LowDimensionalTopology.Geometry.Polygon.Support.CenteredDiscPolygonSupports
public import LowDimensionalTopology.Geometry.Polygon.Support.CyclicDiscPolygonSupports
public import Mathlib.Tactic.Push

/-!
# Supporting half-planes of finite hyperbolic hulls.

Supporting directions of a finite convex hull give the half-planes used in hyperbolic
polygon constructions. Klein coordinates connect the hyperbolic and Euclidean hulls.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
open Set
open scoped Complex.UnitDisc UpperHalfPlane Topology

namespace LowDimensionalTopology.Geometry.Polygon

/-- Finite extreme points in the closed model produce cyclic support data, without
a supplied cyclic ordering, support family or Jordan curve. -/
theorem finite_extreme_cyclic_support_data (V : Finset ℂ) (hcard : 3≤V.card)
    (hext : ∀u∈V,u∈(convexHull ℝ (V:Set ℂ)).extremePoints ℝ)
    (hdisc : ∀u∈V,‖u‖≤1) :
    ∃n : ℕ,∃S : CyclicDiscPolygonSupportData n,
      (∀i,Hyperbolic.closedKleinCoordinate (S.vertices i)∈V) ∧
      ∀u∈V,∀i,inner ℝ (S.normals i) u≤S.offsets i := by
  classical
  have hthird (v w : ℂ) : ∃u∈V,u≠v ∧ u≠w:=by
    by_contra hn
    push Not at hn
    have hsub : V⊆{v,w}:=by
      intro u hu
      by_cases huv : u=v
      · simp only [Finset.mem_insert,Finset.mem_singleton]
        exact Or.inl huv
      · simp only [Finset.mem_insert,Finset.mem_singleton]
        exact Or.inr (hn u hu huv)
    have hpair : ({v,w} : Finset ℂ).card≤2:=by by_cases h : v=w <;> simp [h]
    have hle:=(Finset.card_le_card hsub).trans hpair
    omega
  have hVne : V.Nonempty:=Finset.card_pos.mp (by omega)
  let : Nonempty V:=⟨⟨hVne.choose,hVne.choose_spec⟩⟩
  have hstep (x : V) : ∃y : V,Nonempty (Euclidean.OrientedFiniteHullEdge V x.val y.val):=by
    obtain ⟨u,hu,huv,huw⟩:=hthird x.val x.val
    obtain ⟨w,⟨E⟩⟩:=Euclidean.exists_oriented_finite_hull_edge V hext x.val x.property ⟨u,hu,huv⟩
    exact ⟨⟨w,E.right_mem⟩,⟨E⟩⟩
  choose f hfe using hstep
  let E (x : V) : Euclidean.OrientedFiniteHullEdge V x.val (f x).val:=Classical.choice (hfe x)
  have hfixed (x : V) : f x≠x:=by
    intro he
    exact (E x).ne (congrArg Subtype.val he).symm
  have htwo (x : V) : f (f x)≠x:=by
    intro he
    have F : Euclidean.OrientedFiniteHullEdge V (f x).val x.val:=
      Eq.mp (congrArg (fun y : V=>Euclidean.OrientedFiniteHullEdge V (f x).val y.val) he) (E (f x))
    exact Euclidean.oriented_finite_hull_edge_not_reverse (E x) F (hthird x.val (f x).val)
  obtain ⟨n,hn,v,hinj,hnext⟩:=Euclidean.finite_selfmap_nontrivial_cycle f hfixed htwo
  let q (i : Fin n) : 𝕔𝔻:=
    Hyperbolic.closedKleinToPoincare (Complex.UnitClosedDisc.mk (v i).val (hdisc _ (v i).property))
  have hq (i : Fin n) : Hyperbolic.closedKleinCoordinate (q i)=(v i).val:=by
    change (Hyperbolic.closedPoincareToKlein (Hyperbolic.closedKleinToPoincare _):ℂ)=(v i).val
    rw [Hyperbolic.closedPoincareToKlein_closedKleinToPoincare]
    rfl
  have hqinj : Function.Injective q:=by
    intro i j he
    apply hinj
    apply Subtype.ext
    exact (hq i).symm.trans ((congrArg Hyperbolic.closedKleinCoordinate he).trans (hq j))
  let S : CyclicDiscPolygonSupportData n:={
    three_le:=hn
    vertices:=q
    vertices_injective:=hqinj
    normals:=fun i=>(E (v i)).normal
    normal_norm:=fun i=>(E (v i)).normal_norm
    offsets:=fun i=>inner ℝ (E (v i)).normal (v i).val
    incident:=by
      intro i
      rw [hq i,hq (finRotate n i),hnext i]
      exact ⟨rfl,(E (v i)).incident⟩
    nonincident:=by
      intro i j hji hjnext
      rw [hq j]
      apply (E (v i)).nonincident _ (v j).property
      · intro he
        exact hji (hinj (Subtype.ext he))
      · intro he
        have hh : v j=v (finRotate n i):=by
          rw [hnext i]
          exact Subtype.ext he
        exact hjnext (hinj hh)
  }
  refine ⟨n,S,?_,?_⟩
  · intro i
    change Hyperbolic.closedKleinCoordinate (q i)∈V
    rw [hq]
    exact (v i).property
  · intro u hu i
    change inner ℝ (E (v i)).normal u≤ inner ℝ (E (v i)).normal (v i).val
    by_cases huv : u=(v i).val
    · exact (congrArg (fun z : ℂ=>inner ℝ (E (v i)).normal z) huv).le
    by_cases huw : u=(f (v i)).val
    · exact ((congrArg (fun z : ℂ=>inner ℝ (E (v i)).normal z) huw).trans (E (v i)).incident).le
    · exact ((E (v i)).nonincident u hu huv huw).le

/-- The genuine cyclic supporting-half-plane body is exactly the convex hull of its actual cyclic vertices. -/
theorem cyclic_support_region_eq_convexHull {n : ℕ} (S : CyclicDiscPolygonSupportData n) :
    S.toCenteredData.kleinRegion=convexHull ℝ (range (fun i=>Hyperbolic.closedKleinCoordinate (S.vertices i))) := by
  let V:=range (fun i=>Hyperbolic.closedKleinCoordinate (S.vertices i))
  have hV : V.Finite:=finite_range _
  apply subset_antisymm
  · intro z hz
    by_contra hnot
    obtain ⟨f,t,hft,htz⟩:=geometric_hahn_banach_closed_point (convex_convexHull ℝ V)
      (hV.isClosed_convexHull ℝ) hnot
    let a : ℂ:=(InnerProductSpace.toDual ℝ ℂ).symm f
    have ha (u : ℂ) : inner ℝ a u=f u:=InnerProductSpace.toDual_symm_apply
    have hne : (Finset.univ : Finset (Fin n)).Nonempty:=by
      have hn : 0<n:=by have hh:=S.three_le;omega
      exact ⟨⟨0,hn⟩,Finset.mem_univ _⟩
    obtain ⟨i,hi,hmax⟩:=Finset.exists_max_image Finset.univ
      (fun i=>inner ℝ a (Hyperbolic.closedKleinCoordinate (S.vertices i))) hne
    have hmax' (j : Fin n) : inner ℝ a (Hyperbolic.closedKleinCoordinate (S.vertices j))≤
        inner ℝ a (Hyperbolic.closedKleinCoordinate (S.vertices i)):=hmax j (Finset.mem_univ _)
    obtain ⟨b,c,hb,hc,he⟩:=S.maximal_functional_nonnegative_normals a i hmax'
    let prev:=(finRotate n).symm i
    have hp : inner ℝ (S.normals prev) (Hyperbolic.closedKleinCoordinate (S.vertices i))=S.offsets prev:=by
      simpa only [prev,Equiv.apply_symm_apply] using (S.incident prev).2
    have hbound : inner ℝ a z≤ inner ℝ a (Hyperbolic.closedKleinCoordinate (S.vertices i)):=by
      rw [he,inner_add_left,inner_add_left,real_inner_smul_left,real_inner_smul_left,
        real_inner_smul_left,real_inner_smul_left,hp,(S.incident i).1]
      exact add_le_add (mul_le_mul_of_nonneg_left (hz prev) hb)
        (mul_le_mul_of_nonneg_left (hz i) hc)
    rw [ha,ha] at hbound
    have hh:=hft _ (subset_convexHull ℝ V (mem_range_self i))
    exact (not_lt_of_ge hbound) (hh.trans htz)
  · apply convexHull_min _ S.toCenteredData.kleinRegion_convex
    rintro z ⟨i,rfl⟩
    exact S.toCenteredData.vertex_mem_region i

end LowDimensionalTopology.Geometry.Polygon
