/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Fuchsian.Dirichlet.DirichletDomains
public import Mathlib.Data.Set.Finite.Lemmas
@[expose] public section
open Set Filter
open scoped Topology OnePoint UpperHalfPlane Complex.UnitDisc
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Surfaces LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.Euclidean
noncomputable section

theorem UnitDiscFuchsianGroup.hyperbolicDist_left_continuous {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (w : P.domain.carrier) : Continuous (fun x=>P.hyperbolicDist x w):=
  P.halfPlaneCoordinate.continuous.dist continuous_const

theorem UnitDiscFuchsianGroup.hyperbolicClosedBall_isCompact {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (w : P.domain.carrier) (r : ℝ) :
    IsCompact {x | P.hyperbolicDist x w≤r} :=
  P.halfPlaneCoordinate.isCompact_preimage.mpr (isCompact_closedBall (P.halfPlaneCoordinate w) r)

/-- The original discontinuous action gives actual finite compact orbit-label sets, including stabilizers. -/
theorem UnitDiscFuchsianGroup.compact_orbit_labels {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (x : P.domain.carrier) (K : Set P.domain.carrier) (hK : IsCompact K) :
    {g : H | g • x∈K}.Finite := by
  let : ProperlyDiscontinuousSMul H P.domain.carrier:=_root_.LowDimensionalTopology.Geometry.Surfaces.mobiusDomain_properlyDiscontinuous P.domain P.discontinuous
  have hf:=finite_disjoint_inter_image (Γ:=H) (isCompact_singleton (x:=x)) hK
  apply hf.subset
  intro g hg
  exact ⟨g • x,⟨x,mem_singleton x,rfl⟩,hg⟩

theorem UnitDiscFuchsianGroup.bounded_orbit_labels {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (x w : P.domain.carrier) (r : ℝ) :
    {g : H | P.hyperbolicDist (g • x) w≤r}.Finite:=
  P.compact_orbit_labels x _ (P.hyperbolicClosedBall_isCompact w r)

/-- A genuine closest representative is obtained from finite actual compact orbit intersections. -/
theorem UnitDiscFuchsianGroup.closest_orbit_representative {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (x w : P.domain.carrier) :
    ∃g : H,∀h : H,P.hyperbolicDist (g • x) w≤P.hyperbolicDist (h • x) w := by
  let F:={g : H | P.hyperbolicDist (g • x) w≤P.hyperbolicDist x w}
  have hf : F.Finite:=P.bounded_orbit_labels x w _
  obtain ⟨g,hg,hmin⟩:=Set.exists_min_image F (fun g=>P.hyperbolicDist (g • x) w) hf
    ⟨1,by change P.hyperbolicDist ((1 : H) • x) w≤P.hyperbolicDist x w;simp⟩
  refine ⟨g,fun h=>?_⟩
  by_cases hh : h∈F
  · exact hmin h hh
  · exact hg.trans (not_le.mp hh).le

theorem UnitDiscFuchsianGroup.compact_hyperbolicDist_bound {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (w : P.domain.carrier) (K : Set P.domain.carrier) (hK : IsCompact K) :
    ∃r : ℝ,∀x∈K,P.hyperbolicDist x w≤r := by
  obtain ⟨r,hr⟩:=(hK.image (P.hyperbolicDist_left_continuous w)).bddAbove
  exact ⟨r,fun x hx=>hr (mem_image_of_mem _ hx)⟩

/-- The local-finiteness assertion used in concerns the actual original bisector labels. -/
theorem dirichletBisectors_compact_hits_finite {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (w : P.domain.carrier) (K : Set P.domain.carrier) (hK : IsCompact K) :
    {g : H | g≠1 ∧ (dirichletBisector P w g∩K).Nonempty}.Finite := by
  obtain ⟨r,hr⟩:=P.compact_hyperbolicDist_bound w K hK
  apply (P.bounded_orbit_labels w w (2*r)).subset
  rintro g ⟨_,z,hz,hzK⟩
  change P.hyperbolicDist z w=P.hyperbolicDist z (g • w) at hz
  change P.hyperbolicDist (g • w) w≤2*r
  have ht:=P.hyperbolicDist_triangle w z (g • w)
  rw [P.hyperbolicDist_comm w z,←hz,P.hyperbolicDist_comm w (g • w)] at ht
  exact ht.trans (by linarith [hr z hzK])

/-- Infinite intersection openness is proved from actual compact orbit finiteness. -/
theorem dirichletDomain_isOpen {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (w : P.domain.carrier) : IsOpen (dirichletDomain P w) := by
  rw [isOpen_iff_mem_nhds]
  intro z hz
  let J:={g : H | g≠1 ∧ P.hyperbolicDist (g • w) w≤2*(P.hyperbolicDist w z+1)}
  have hJ : J.Finite:=(P.bounded_orbit_labels w w _).subset (fun _ h=>h.2)
  have hV : (⋂g∈J,dirichletHalfPlane P w g)∈𝓝 z:=
    (biInter_mem hJ).mpr (fun g hg=>(dirichletHalfPlane_isOpen P w g).mem_nhds (hz g hg.1))
  have hB : {u | P.hyperbolicDist u z<1}∈𝓝 z:=by
    apply (isOpen_lt (P.hyperbolicDist_left_continuous z) continuous_const).mem_nhds
    change P.hyperbolicDist z z<1
    rw [P.hyperbolicDist_self]
    norm_num
  apply Filter.mem_of_superset (inter_mem hB hV)
  rintro u ⟨huB,huV⟩ g hg
  by_cases hgJ : g∈J
  · exact mem_iInter₂.mp huV g hgJ
  · have hfar : 2*(P.hyperbolicDist w z+1)<P.hyperbolicDist (g • w) w:=
      not_le.mp (fun hle=>hgJ ⟨hg,hle⟩)
    change P.hyperbolicDist u z<1 at huB
    have hwu:=P.hyperbolicDist_triangle w z u
    rw [P.hyperbolicDist_comm z u] at hwu
    have ht:=P.hyperbolicDist_triangle w u (g • w)
    rw [P.hyperbolicDist_comm w (g • w)] at ht
    have hc:=P.hyperbolicDist_comm w u
    change P.hyperbolicDist u w<P.hyperbolicDist u (g • w)
    linarith

end
end LowDimensionalTopology.Geometry.Fuchsian
