/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Fuchsian.Axis.SimpleAxisExample
public import LowDimensionalTopology.Geometry.Fuchsian.Dirichlet.DirichletGeometry
@[expose] public section
noncomputable section
set_option autoImplicit false
open Set Topology
open scoped Pointwise
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon
local instance nielsenEvaluationAction {X : Type*} [MetricSpace X] : MulAction (X≃ᵢX) X where
  smul g x:=g x
  one_smul _:=rfl
  mul_smul _ _ _:=rfl

/-- Moving disjoint open pieces independently along their actual orbits preserves
wandering. This is the two-piece move used by the Nielsen quadrilateral change. -/
theorem two_piece_reassembly_wandering {X : Type*} [MetricSpace X]
    (H : Subgroup (X ≃ᵢ X)) (D A B : Set X) (hAD : A⊆D) (hBD : B⊆D)
    (hAB : Disjoint A B)
    (hpack : ∀h∈H,h≠1→Disjoint (h • D) D)
    (g : X ≃ᵢ X) (hg : g∈H) (h : X ≃ᵢ X) (hh : h∈H) (hne : h≠1) :
    Disjoint (h • (A∪g • B)) (A∪g • B) := by
  have huniq (k : X≃ᵢX) (hk : k∈H) (x y : X) (hx : x∈D) (hy : y∈D)
      (hxy : k x=y) : k=1 ∧ x=y := by
    by_cases he : k=1
    · refine ⟨he,?_⟩
      subst k
      exact hxy
    · exact False.elim (disjoint_left.mp (hpack k hk he) ⟨x,hx,hxy⟩ hy)
  apply disjoint_left.mpr
  rintro _ ⟨x,hx,rfl⟩ hy
  rcases hx with hx|⟨b,hb,rfl⟩ <;> rcases hy with hy|⟨c,hc,hcEq⟩
  · exact hne (huniq h hh x (h x) (hAD hx) (hAD hy) rfl).1
  · have he : (g⁻¹*h) x=c := by
      change g.symm (h x)=c
      change g c=h x at hcEq
      exact (congrArg g.symm hcEq).symm.trans (g.symm_apply_apply c)
    have hu:=huniq (g⁻¹*h) (H.mul_mem (H.inv_mem hg) hh) x c (hAD hx) (hBD hc) he
    exact disjoint_left.mp hAB hx (hu.2.symm ▸ hc)
  · have he : (h*g) b=h (g b) := rfl
    have hu:=huniq (h*g) (H.mul_mem hh hg) b (h (g b)) (hBD hb) (hAD hy) he
    exact disjoint_left.mp hAB (hu.2.symm ▸ hy) hb
  · have he : (g⁻¹*h*g) b=c := by
      change g.symm (h (g b))=c
      change g c=h (g b) at hcEq
      exact (congrArg g.symm hcEq).symm.trans (g.symm_apply_apply c)
    have hu:=huniq (g⁻¹*h*g) (H.mul_mem (H.mul_mem (H.inv_mem hg) hh) hg)
      b c (hBD hb) (hBD hc) he
    apply hne
    calc
      h=g*(g⁻¹*h*g)*g⁻¹ := by group
      _=1 := by rw [hu.1];group

/-- The actual open regularization of a two-piece Nielsen move remains wandering. -/
theorem two_piece_reassembly_regularized_wandering {X : Type*} [MetricSpace X]
    (H : Subgroup (X ≃ᵢ X)) (D A B : Set X) (hA : IsOpen A) (hB : IsOpen B)
    (hAD : A⊆D) (hBD : B⊆D) (hAB : Disjoint A B)
    (hpack : ∀h∈H,h≠1→Disjoint (h • D) D)
    (g : X ≃ᵢ X) (hg : g∈H) (h : X ≃ᵢ X) (hh : h∈H) (hne : h≠1) :
    Disjoint (h • interior (closure (A∪g • B))) (interior (closure (A∪g • B))) := by
  exact Fuchsian.open_closure_wandering H (A∪g • B) _
    (hA.union (g.toHomeomorph.isOpenMap _ hB)) isOpen_interior interior_subset
    (two_piece_reassembly_wandering H D A B hAD hBD hAB hpack g hg) h hh hne


/-- Regularizing an open set does not alter its closure. -/
theorem nielsen_regularization_closure {X : Type*} [TopologicalSpace X]
    (U : Set X) (hU : IsOpen U) : closure (interior (closure U))=closure U := by
  apply subset_antisymm
  · exact isClosed_closure.closure_subset_iff.mpr interior_subset
  · exact closure_mono (hU.subset_interior_iff.mpr subset_closure)

/-- Every old orbit representative remains represented in the closure after the
actual two-piece move; only the old cut, not a desired new cover, is an input. -/
theorem two_piece_reassembly_closure_meetsEveryOrbit {X : Type*} [MetricSpace X]
    (H : Subgroup (X≃ᵢX)) (D A B : Set X) (hA : IsOpen A) (hB : IsOpen B)
    (hcut : closure (A∪B)=closure D)
    (hcover : DiscreteGroups.Action.MeetsEveryOrbit H X (closure D))
    (g : X≃ᵢX) (hg : g∈H) :
    DiscreteGroups.Action.MeetsEveryOrbit H X (closure (interior (closure (A∪g • B)))) := by
  intro x
  obtain ⟨h,hh⟩:=hcover x
  rw [←hcut,closure_union] at hh
  have hopen : IsOpen (A∪g • B):=hA.union (g.toHomeomorph.isOpenMap _ hB)
  rw [nielsen_regularization_closure _ hopen,closure_union]
  rcases hh with hh|hh
  · exact ⟨h,Or.inl hh⟩
  · refine ⟨(⟨g,hg⟩:H)*h,Or.inr ?_⟩
    change g (h • x)∈closure (g • B)
    change g (h • x)∈closure (g '' B)
    exact map_mem_closure g.continuous hh (fun _ hz=>mem_image_of_mem g hz)

/--
The actual two-piece Nielsen move preserves the geometric fundamental-domain
condition once the new convex region's connectedness and geometric null boundary
have been checked. Neither orbit covering nor orbit uniqueness is assumed for it.
-/
theorem two_piece_reassembly_fundamentalDomain {X : Type*} [MetricSpace X]
    [MeasurableSpace X] (H : Subgroup (X≃ᵢX)) (μ : MeasureTheory.Measure X)
    (D A B : Set X) (hD : DiscreteGroups.Action.IsFundamentalDomain H X μ D)
    (hA : IsOpen A) (hB : IsOpen B) (hAD : A⊆D) (hBD : B⊆D)
    (hAB : Disjoint A B) (hcut : closure (A∪B)=closure D)
    (hpack : ∀h∈H,h≠1→Disjoint (h • D) D)
    (g : X≃ᵢX) (hg : g∈H)
    (hconn : IsConnected (interior (closure (A∪g • B))))
    (hnull : μ (frontier (interior (closure (A∪g • B))))=0) :
    DiscreteGroups.Action.IsFundamentalDomain H X μ (interior (closure (A∪g • B))) := by
  refine ⟨isOpen_interior,hconn,?_,hnull⟩
  apply exists_fundamentalSet_between _ _ subset_closure
    (two_piece_reassembly_closure_meetsEveryOrbit H D A B hA hB hcut
      (hD.closure_meetsEveryOrbit H X) g hg)
  intro x hx y hy hxy
  obtain ⟨h,hh⟩:=(Quotient.exact hxy : MulAction.orbitRel H X x y)
  change h.val y=x at hh
  by_cases he : h.val=1
  · have hxy : y=x := by
      rw [he] at hh
      exact hh
    exact hxy.symm
  · exact False.elim (disjoint_left.mp
      (two_piece_reassembly_regularized_wandering H D A B hA hB hAD hBD hAB hpack
        g hg h.val h.property he) ⟨y,hy,hh⟩ hx)

end LowDimensionalTopology.Geometry.Fuchsian
