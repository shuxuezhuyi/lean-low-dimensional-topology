module
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.Vertex.PolygonInfiniteVertices
public import Mathlib.Topology.Order.Compact

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Topology MeasureTheory Function
open scoped Complex.UnitDisc Pointwise
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
  LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Polygon

/-- Every genuine compact connected proper subset of the unit circle is a literal closed angular arc. -/
theorem circle_compact_connected_proper_arc {S : Set Circle}
    (hS : IsConnected S) (hK : IsCompact S) (hn : S.Nontrivial) (hp : S ≠ univ) :
    ∃ a b : ℝ, a < b ∧ b-a < 2*Real.pi ∧ S = Circle.exp '' Icc a b := by
  classical
  have hh : ¬ ∀ u : Circle, u ∈ S := fun h => hp (Set.eq_univ_of_forall h)
  obtain ⟨u,hu⟩ := not_forall.mp hh
  let c := AddCircle.homeomorphCircle'
  let K := c.symm '' S
  obtain ⟨a,_ha,hau⟩ := AddCircle.eq_coe_Ico (c.symm u)
  let e := AddCircle.openPartialHomeomorphCoe (2*Real.pi) a
  have hKt : K ⊆ e.target := by
    rintro v ⟨s,hs,rfl⟩
    change c.symm s ≠ (a : AddCircle (2*Real.pi))
    intro he
    have hsu : s = u := c.symm.injective (he.trans hau)
    exact hu (hsu ▸ hs)
  have hf : ContinuousOn e.symm K := e.continuousOn_symm.mono hKt
  have hKC : IsConnected K := hS.image c.symm c.symm.continuous.continuousOn
  have hKK : IsCompact K := hK.image c.symm.continuous
  let J := e.symm '' K
  have hJC : IsConnected J := hKC.image e.symm hf
  have hJK : IsCompact J := hKK.image_of_continuousOn hf
  have hJN : J.Nontrivial :=
    (hn.image c.symm.injective).image_of_injOn (e.symm.injOn.mono hKt)
  have hJ : J = Icc (sInf J) (sSup J) := eq_Icc_of_connected_compact hJC hJK
  have hJsub : J ⊆ Ioo a (a+2*Real.pi) := by
    rintro x ⟨v,hv,rfl⟩
    exact e.map_target (hKt hv)
  have hlr : sInf J < sSup J := by
    by_contra h
    obtain ⟨x,hx,y,hy,hxy⟩ := hJN
    rw [hJ] at hx hy
    have hrle := le_of_not_gt h
    apply hxy
    linarith [hx.1,hx.2,hy.1,hy.2]
  have hl : sInf J ∈ J := (Set.ext_iff.mp hJ (sInf J)).mpr (left_mem_Icc.mpr hlr.le)
  have hr : sSup J ∈ J := (Set.ext_iff.mp hJ (sSup J)).mpr (right_mem_Icc.mpr hlr.le)
  have hKe : e '' J = K := by
    apply Set.Subset.antisymm
    · rintro _ ⟨x,⟨v,hv,hvx⟩,rfl⟩
      rw [← hvx,e.right_inv (hKt hv)]
      exact hv
    · intro v hv
      exact ⟨e.symm v,mem_image_of_mem e.symm hv,e.right_inv (hKt hv)⟩
  have hcK : c '' K = S := by
    change c '' (c.symm '' S) = S
    simp only [image_image,Homeomorph.apply_symm_apply,image_id']
  refine ⟨sInf J,sSup J,hlr,by linarith [(hJsub hl).1,(hJsub hr).2],?_⟩
  calc
    S = c '' K := hcK.symm
    _ = c '' (e '' J) := by rw [hKe]
    _ = Circle.exp '' J := by
      rw [image_image]
      rfl
    _ = Circle.exp '' Icc (sInf J) (sSup J) := congrArg (fun T => Circle.exp '' T) hJ

/-- The whole genuine unit circle is the literal image of one full closed angular interval. -/
theorem circle_exp_image_full_interval :
    Circle.exp '' Icc (0 : ℝ) (2*Real.pi) = univ := by
  calc
    _ = AddCircle.homeomorphCircle' ''
        ((fun t : ℝ => (t : AddCircle (2*Real.pi))) '' Icc 0 (0+2*Real.pi)) := by
      simp only [image_image,zero_add,AddCircle.homeomorphCircle'_apply_mk]
    _ = univ := by
      rw [AddCircle.coe_image_Icc_eq]
      rw [image_univ]
      exact AddCircle.homeomorphCircle'.toEquiv.range_eq_univ

/-- Every genuine nondegenerate compact connected circle set is a closed angular interval of length at most2π. -/
theorem circle_compact_connected_arc {S : Set Circle}
    (hS : IsConnected S) (hK : IsCompact S) (hn : S.Nontrivial) :
    ∃ a b : ℝ, a < b ∧ b-a ≤ 2*Real.pi ∧ S = Circle.exp '' Icc a b := by
  by_cases hp : S = univ
  · refine ⟨0,2*Real.pi,by positivity,by simp,?_⟩
    rw [hp,circle_exp_image_full_interval]
  · obtain ⟨a,b,hab,hlen,he⟩ := circle_compact_connected_proper_arc hS hK hn hp
    exact ⟨a,b,hab,hlen.le,he⟩

/-- The geometric actual free sides are literal closed nondegenerate intervals on the original unit circle. -/
theorem IsFuchsianFreeSide.closed_arc {H : Subgroup Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} {D : Set P.domain.carrier} {S : Set Circle}
    (hS : IsFuchsianFreeSide P D S) :
    ∃ a b : ℝ, a < b ∧ b-a ≤ 2*Real.pi ∧ S = Circle.exp '' Icc a b :=
  circle_compact_connected_arc hS.isConnected hS.isClosed.isCompact hS.nontrivial

end LowDimensionalTopology.Geometry.Fuchsian
