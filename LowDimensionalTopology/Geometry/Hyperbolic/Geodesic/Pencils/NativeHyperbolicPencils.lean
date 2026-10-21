/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Hyperbolic.Geodesic.Pencils.HyperbolicPencilTransport
@[expose] public section
open Set
open scoped UpperHalfPlane MatrixGroups Complex.UnitDisc OnePoint
namespace LowDimensionalTopology.Geometry.Hyperbolic
open LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
  LowDimensionalTopology.Geometry.Mobius LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Inversive
noncomputable section

def IsDiscHypercycleBranch (axis : DiscLine) (S : Set 𝔻) : Prop :=
  ∃C : Mobius.ComplexGeneralizedCircle,C.val∩extendedDiscIdealBoundary=axis.idealEndpoints ∧
    S=nativeDiscCircleCarrier C ∧ S.Nonempty

def discHyperbolicPencil (axis : DiscLine) : Set DiscLine := {L | L.Orthogonal axis}

theorem IsHHypercycleBranch.cayley_image {axis : HalfPlaneLine} {S : Set ℍ}
    (hS : IsHHypercycleBranch axis S) : IsDiscHypercycleBranch axis.toDiscLine (halfPlaneToDisc '' S) := by
  obtain ⟨C,hC,rfl,hne⟩:=hS
  refine ⟨C.image cayleyMobius,?_,(nativeDiscCircleCarrier_cayley_image C).symm,hne.image _⟩
  change (cayleyMobius.val '' C.val)∩extendedDiscIdealBoundary=axis.toDiscLine.idealEndpoints
  rw [←image_inter_preimage,cayley_preimage_idealBoundary,hC,DiscLine.idealEndpoints_eq_cayley_image,
    axis.toDiscLine_toHalfPlane]
  rfl

theorem IsDiscHypercycleBranch.cayley_inverse_image {axis : DiscLine} {S : Set 𝔻}
    (hS : IsDiscHypercycleBranch axis S) : IsHHypercycleBranch axis.toHalfPlane (discToHalfPlane '' S) := by
  obtain ⟨C,hC,rfl,hne⟩:=hS
  refine ⟨C.image cayleyMobius⁻¹,?_,(halfPlaneCircleCarrier_cayley_inverse_image C).symm,hne.image _⟩
  change ((cayleyMobius⁻¹).val '' C.val)∩halfPlaneIdealBoundary=axis.toHalfPlane.idealEndpoints
  rw [←image_inter_preimage,cayley_inverse_preimage_idealBoundary,hC,axis.idealEndpoints_eq_cayley_image]
  change extendedCayley.symm '' (extendedCayley '' axis.toHalfPlane.idealEndpoints)=_
  rw [image_image]
  simp only [extendedCayley.symm_apply_apply,image_id']

theorem isDiscHypercycleBranch_iff_halfPlane (axis : DiscLine) (S : Set 𝔻) :
    IsDiscHypercycleBranch axis S ↔ IsHHypercycleBranch axis.toHalfPlane (discToHalfPlane '' S) := by
  refine ⟨fun h=>h.cayley_inverse_image,?_⟩
  intro h
  have hh:=h.cayley_image
  rwa [axis.toHalfPlane_spec,cayley_image_inverse_image] at hh

theorem mem_discHyperbolicPencil_iff_halfPlane (axis L : DiscLine) :
    L∈discHyperbolicPencil axis ↔ L.toHalfPlane∈hHyperbolicPencil axis.toHalfPlane :=
  L.orthogonal_iff_halfPlane axis

/-- Original native P1 for all actual individual complementary branches, including the axis. -/
theorem existsUnique_discHypercycleBranch_through (axis : DiscLine) (z : 𝔻) :
    ∃!S : Set 𝔻,IsDiscHypercycleBranch axis S ∧ z∈S := by
  obtain ⟨S,⟨hS,hz⟩,hunique⟩:=existsUnique_hHypercycleBranch_through axis.toHalfPlane (discToHalfPlane z)
  refine ⟨halfPlaneToDisc '' S,⟨?_,discToHalfPlane z,hz,halfPlaneToDisc_discToHalfPlane z⟩,?_⟩
  · have hh:=hS.cayley_image
    rwa [axis.toHalfPlane_spec] at hh
  · rintro T ⟨hT,hzT⟩
    have he : discToHalfPlane '' T=S:=hunique _ ⟨hT.cayley_inverse_image,mem_image_of_mem _ hzT⟩
    have hh:=congrArg (fun U : Set ℍ => halfPlaneToDisc '' U) he
    rwa [cayley_image_inverse_image] at hh

/-- Original native P2 has no exceptional point. -/
theorem existsUnique_discHyperbolicPencil_through (axis : DiscLine) (z : 𝔻) :
    ∃!L : DiscLine,L∈discHyperbolicPencil axis ∧ z∈L.carrier := by
  obtain ⟨L,⟨hL,hz⟩,hunique⟩:=existsUnique_hHyperbolicPencil_through axis.toHalfPlane (discToHalfPlane z)
  refine ⟨L.toDiscLine,⟨?_,?_⟩,?_⟩
  · rw [mem_discHyperbolicPencil_iff_halfPlane,L.toDiscLine_toHalfPlane]
    exact hL
  · rw [DiscLine.mem_carrier,L.toDiscLine_toHalfPlane]
    exact hz
  · rintro M ⟨hM,hzM⟩
    apply DiscLine.toHalfPlane_injective
    rw [L.toDiscLine_toHalfPlane]
    exact hunique M.toHalfPlane ⟨(mem_discHyperbolicPencil_iff_halfPlane axis M).mp hM,(M.mem_carrier z).mp hzM⟩

/-- Native P3 retains genuine Euclidean generalized-circle normal orthogonality. -/
theorem discHypercycleBranch_orthogonal (axis : DiscLine) {L : DiscLine}
    (hL : L∈discHyperbolicPencil axis) {S : Set 𝔻} (hS : IsDiscHypercycleBranch axis S) :
    ∃C : Mobius.ComplexGeneralizedCircle,S=nativeDiscCircleCarrier C ∧ Mobius.ComplexCirclesOrthogonal L.val C := by
  obtain ⟨C,hC,ho⟩:=hHypercycleBranch_orthogonal axis.toHalfPlane
    ((mem_discHyperbolicPencil_iff_halfPlane axis L).mp hL) hS.cayley_inverse_image
  refine ⟨C.image cayleyMobius,?_,?_⟩
  · rw [nativeDiscCircleCarrier_cayley_image,←hC,cayley_image_inverse_image]
  · have he : L.toHalfPlane.extendedCircle.image cayleyMobius=L.val := by
      change L.toHalfPlane.toDiscLine.val=L.val
      rw [L.toHalfPlane_spec]
    rw [←he]
    exact ho.image _ _ _

/-- Native P4 uses the actual generalized-circle reflection. -/
theorem discHypercycleBranch_reflection (axis : DiscLine) {L : DiscLine}
    (hL : L∈discHyperbolicPencil axis) {S : Set 𝔻} (hS : IsDiscHypercycleBranch axis S) : L.reflection '' S=S := by
  have hh:=hHypercycleBranch_reflection axis.toHalfPlane
    ((mem_discHyperbolicPencil_iff_halfPlane axis L).mp hL) hS.cayley_inverse_image
  have he:=congrArg (fun T : Set ℍ => halfPlaneToDisc '' T) hh
  rw [cayley_image_inverse_image] at he
  calc
    L.reflection '' S=halfPlaneToDisc '' (L.toHalfPlane.reflection '' (discToHalfPlane '' S)) := by
      rw [image_image,image_image]
      rfl
    _=S := he

/-- Native P5 realizes the actual infimum over genuine native curve-point pairs. -/
theorem discHypercycleBranch_equidistance (axis : DiscLine) {S T : Set 𝔻}
    (hS : IsDiscHypercycleBranch axis S) (hT : IsDiscHypercycleBranch axis T) (p : 𝔻) (hp : p∈S) :
    ∃q : 𝔻,q∈T ∧ discPathDist p q=discCurveDistance S T ∧
      ∃L : DiscLine,L∈discHyperbolicPencil axis ∧ p∈L.carrier ∧ q∈L.carrier := by
  obtain ⟨q,hq,hd,L,hL,hpL,hqL⟩:=hHypercycleBranch_equidistance axis.toHalfPlane
    hS.cayley_inverse_image hT.cayley_inverse_image (discToHalfPlane p) (mem_image_of_mem _ hp)
  obtain ⟨v,hv,rfl⟩:=hq
  refine ⟨v,hv,?_,L.toDiscLine,?_,?_,?_⟩
  · rw [discPathDist_eq_halfPlane,discCurveDistance_eq_halfPlane]
    exact hd
  · rw [mem_discHyperbolicPencil_iff_halfPlane,L.toDiscLine_toHalfPlane]
    exact hL
  · rw [DiscLine.mem_carrier,L.toDiscLine_toHalfPlane]
    exact hpL
  · rw [DiscLine.mem_carrier,L.toDiscLine_toHalfPlane]
    exact hqL

theorem common_discHypercycleBranch_iff_halfPlane (axis : DiscLine) (a b : 𝔻) :
    (∃S : Set 𝔻,IsDiscHypercycleBranch axis S ∧ a∈S ∧ b∈S) ↔
      ∃T : Set ℍ,IsHHypercycleBranch axis.toHalfPlane T ∧ discToHalfPlane a∈T ∧ discToHalfPlane b∈T := by
  constructor
  · rintro ⟨S,hS,ha,hb⟩
    exact ⟨discToHalfPlane '' S,hS.cayley_inverse_image,mem_image_of_mem _ ha,mem_image_of_mem _ hb⟩
  · rintro ⟨T,hT,ha,hb⟩
    refine ⟨halfPlaneToDisc '' T,?_,⟨discToHalfPlane a,ha,halfPlaneToDisc_discToHalfPlane a⟩,
      discToHalfPlane b,hb,halfPlaneToDisc_discToHalfPlane b⟩
    have hh:=hT.cayley_image
    rwa [axis.toHalfPlane_spec] at hh

/-- Native P6 uses the actual geometric perpendicular bisector. -/
theorem discHyperbolicPencil_perpendicularBisector_iff (axis : DiscLine) {a b : 𝔻} (hab : a≠b)
    {N : DiscLine} (hN : IsDiscPerpendicularBisector N a b) :
    N∈discHyperbolicPencil axis ↔ ∃S : Set 𝔻,IsDiscHypercycleBranch axis S ∧ a∈S ∧ b∈S := by
  rw [mem_discHyperbolicPencil_iff_halfPlane,common_discHypercycleBranch_iff_halfPlane]
  exact hHyperbolicPencil_perpendicularBisector_iff axis.toHalfPlane (discToHalfPlane_injective.ne hab)
    ((isDiscPerpendicularBisector_iff_halfPlane N a b).mp hN)

/-- The actual native curve closure has exactly the two true ideal ends of its actual axis. -/
theorem IsDiscHypercycleBranch.idealEndpoints {axis : DiscLine} {S : Set 𝔻} (hS : IsDiscHypercycleBranch axis S) :
    discTraceIdealEndpoints S=axis.idealEndpoints := by
  calc
    discTraceIdealEndpoints S=discTraceIdealEndpoints (halfPlaneToDisc '' (discToHalfPlane '' S)) := by
      rw [cayley_image_inverse_image]
    _=extendedCayley '' hTraceIdealEndpoints (discToHalfPlane '' S):=discTraceIdealEndpoints_cayley_image _
    _=axis.idealEndpoints := by
      rw [hS.cayley_inverse_image.idealEndpoints,←axis.idealEndpoints_eq_cayley_image]


theorem concentric_lines_hDisjoint (r s : ℝ) (hr : 0<r) (hs : 0<s) (hrs : r≠s) :
    (HalfPlaneLine.circle 0 r hr).HDisjoint (.circle 0 s hs) := by
  refine ⟨?_,?_,?_⟩
  · intro he
    cases he
    exact hrs rfl
  · let f : ℝ → OnePoint ℂ:=fun x => ((x : ℂ) : OnePoint ℂ)
    have hf : Function.Injective f:=by
      intro x y he
      exact Complex.ofReal_injective (OnePoint.coe_injective he)
    have hR : (HalfPlaneLine.circle 0 r hr).idealEndpoints=f '' {-r,r}:=by
      rw [circle_idealEndpoints,image_insert_eq,image_singleton]
      simp [f]
    have hS : (HalfPlaneLine.circle 0 s hs).idealEndpoints=f '' {-s,s}:=by
      rw [circle_idealEndpoints,image_insert_eq,image_singleton]
      simp [f]
    rw [hR,hS,Set.disjoint_image_iff hf]
    apply Set.disjoint_left.mpr
    intro x hx hy
    simp only [mem_insert_iff,mem_singleton_iff] at hx hy
    rcases hx with hx | hx <;> rcases hy with hy | hy
    all_goals
      apply hrs
      linarith
  · apply Set.disjoint_left.mpr
    intro z hz hw
    change ‖(z : ℂ)-(0 : ℂ)‖=r at hz
    change ‖(z : ℂ)-(0 : ℂ)‖=s at hw
    exact hrs (hz.symm.trans hw)

theorem hHyperbolicPencil_members_hDisjoint (axis : HalfPlaneLine) {L M : HalfPlaneLine}
    (hL : L∈hHyperbolicPencil axis) (hM : M∈hHyperbolicPencil axis) (hne : L≠M) : L.HDisjoint M := by
  obtain ⟨g,hg,rfl⟩:=exists_hHyperbolicChart axis
  obtain ⟨r,hr,rfl⟩:=(mem_hHyperbolicPencil_chart_iff g L).mp hL
  obtain ⟨s,hs,rfl⟩:=(mem_hHyperbolicPencil_chart_iff g M).mp hM
  have hrs : r≠s:=by intro he; subst s; exact hne rfl
  exact (HalfPlaneLine.circle 0 r hr).hDisjoint_realGL_image (.circle 0 s hs) _ _ g hg
    ((HalfPlaneLine.circle 0 r hr).realGLMap_carrier g).symm
    ((HalfPlaneLine.circle 0 s hs).realGLMap_carrier g).symm (concentric_lines_hDisjoint r s hr hs hrs)

theorem discHyperbolicPencil_members_hDisjoint (axis : DiscLine) {L M : DiscLine}
    (hL : L∈discHyperbolicPencil axis) (hM : M∈discHyperbolicPencil axis) (hne : L≠M) : L.HDisjoint M := by
  apply (L.hDisjoint_iff_halfPlane M).mpr
  exact hHyperbolicPencil_members_hDisjoint axis.toHalfPlane
    ((mem_discHyperbolicPencil_iff_halfPlane axis L).mp hL)
    ((mem_discHyperbolicPencil_iff_halfPlane axis M).mp hM) (DiscLine.toHalfPlane_injective.ne hne)

theorem DiscLine.axis_isHypercycleBranch (axis : DiscLine) : IsDiscHypercycleBranch axis axis.carrier := by
  have hh:=axis.toHalfPlane.axis_isHypercycleBranch.cayley_image
  rw [axis.toHalfPlane_spec,←axis.carrier_eq_cayley_image_halfPlane] at hh
  exact hh

theorem IsDiscHypercycleBranch.pointDist_eq {axis : DiscLine} {S : Set 𝔻}
    (hS : IsDiscHypercycleBranch axis S) {z w : 𝔻} (hz : z∈S) (hw : w∈S) : axis.pointDist z=axis.pointDist w := by
  rw [axis.pointDist_eq_halfPlane,axis.pointDist_eq_halfPlane]
  exact hS.cayley_inverse_image.pointDist_eq (mem_image_of_mem _ hz) (mem_image_of_mem _ hw)

theorem DiscLine.distance_level_eq_cayley (axis : DiscLine) (r : ℝ) :
    {z : 𝔻 | axis.pointDist z=r}=halfPlaneToDisc '' {z : ℍ | axis.toHalfPlane.pointDist z=r} := by
  ext z
  constructor
  · intro hz
    refine ⟨discToHalfPlane z,?_,halfPlaneToDisc_discToHalfPlane z⟩
    change axis.toHalfPlane.pointDist (discToHalfPlane z)=r
    rwa [←axis.pointDist_eq_halfPlane]
  · rintro ⟨w,hw,rfl⟩
    change axis.pointDist (halfPlaneToDisc w)=r
    rwa [axis.pointDist_eq_halfPlane,discToHalfPlane_halfPlaneToDisc]

theorem DiscLine.distanceSublevel_frontier (axis : DiscLine) (r : ℝ) (hr : 0<r) :
    frontier (axis.distanceSublevel r)={z : 𝔻 | axis.pointDist z=r} := by
  rw [axis.distanceSublevel_eq_cayley]
  change frontier (cayleyHomeomorph '' axis.toHalfPlane.distanceSublevel r)=_
  rw [←cayleyHomeomorph.image_frontier,axis.toHalfPlane.distanceSublevel_frontier r hr,
    axis.distance_level_eq_cayley]
  rfl

theorem DiscLine.distance_level_two_hypercycleBranches (axis : DiscLine) (r : ℝ) (hr : 0<r) :
    ∃S T : Set 𝔻,IsDiscHypercycleBranch axis S ∧ IsDiscHypercycleBranch axis T ∧
      Disjoint S T ∧ S≠T ∧ {z : 𝔻 | axis.pointDist z=r}=S∪T := by
  obtain ⟨S,T,hS,hT,hdisj,hne,hlevel⟩:=axis.toHalfPlane.distance_level_two_hypercycleBranches r hr
  have hS' : IsDiscHypercycleBranch axis (halfPlaneToDisc '' S):=by
    have hh:=hS.cayley_image
    rwa [axis.toHalfPlane_spec] at hh
  have hT' : IsDiscHypercycleBranch axis (halfPlaneToDisc '' T):=by
    have hh:=hT.cayley_image
    rwa [axis.toHalfPlane_spec] at hh
  refine ⟨halfPlaneToDisc '' S,halfPlaneToDisc '' T,hS',hT',?_,?_,?_⟩
  · exact (Set.disjoint_image_iff cayleyHomeomorph.injective).mpr hdisj
  · exact cayleyHomeomorph.injective.image_injective.ne hne
  · rw [axis.distance_level_eq_cayley,hlevel,image_union]

theorem IsDiscHypercycleBranch.axis_or_actual_hypercycle {axis : DiscLine} {S : Set 𝔻}
    (hS : IsDiscHypercycleBranch axis S) :
    S=axis.carrier ∨ ∃r : ℝ,0<r ∧ IsDiscHypercyclicRegion (axis.distanceSublevel r) ∧
      S⊆discHypercycle (axis.distanceSublevel r) := by
  rcases hS.cayley_inverse_image.axis_or_actual_hypercycle with he | ⟨r,hr,hregion,hsub⟩
  · left
    have hh:=congrArg (fun T : Set ℍ => halfPlaneToDisc '' T) he
    rwa [cayley_image_inverse_image,←axis.carrier_eq_cayley_image_halfPlane] at hh
  · right
    refine ⟨r,hr,axis.distanceSublevel_hypercyclic r hr,?_⟩
    intro z hz
    have hh:=hsub (mem_image_of_mem discToHalfPlane hz)
    change discToHalfPlane z∈frontier (axis.toHalfPlane.distanceSublevel r) at hh
    rw [axis.toHalfPlane.distanceSublevel_frontier r hr] at hh
    change z∈frontier (axis.distanceSublevel r)
    rw [axis.distanceSublevel_frontier r hr]
    change axis.pointDist z=r
    rwa [axis.pointDist_eq_halfPlane]

theorem DiscLine.hypercycle_frontier_two_branches (axis : DiscLine) (r : ℝ) (hr : 0<r) :
    ∃S T : Set 𝔻,IsDiscHypercycleBranch axis S ∧ IsDiscHypercycleBranch axis T ∧
      Disjoint S T ∧ S≠T ∧ discHypercycle (axis.distanceSublevel r)=S∪T := by
  change ∃S T : Set 𝔻,IsDiscHypercycleBranch axis S ∧ IsDiscHypercycleBranch axis T ∧
    Disjoint S T ∧ S≠T ∧ frontier (axis.distanceSublevel r)=S∪T
  rw [axis.distanceSublevel_frontier r hr]
  exact axis.distance_level_two_hypercycleBranches r hr

end
end LowDimensionalTopology.Geometry.Hyperbolic
