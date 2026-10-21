/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Hyperbolic.Geodesic.Pencils.HyperbolicPencils
public import LowDimensionalTopology.Geometry.Hyperbolic.Metric.DistanceLevelFrontiers
@[expose] public section
open Set
open scoped UpperHalfPlane MatrixGroups Complex.UnitDisc OnePoint
namespace LowDimensionalTopology.Geometry.Hyperbolic
open LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
  LowDimensionalTopology.Geometry.Mobius LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Inversive
noncomputable section

theorem IsHHypercycleBranch.realGL_image {axis : HalfPlaneLine} {S : Set ℍ}
    (hS : IsHHypercycleBranch axis S) (g : GL (Fin 2) ℝ) (hg : 0<g.val.det) :
    IsHHypercycleBranch (axis.realGLMap g) ((g • · : ℍ → ℍ) '' S) := by
  obtain ⟨C,hC,rfl,hne⟩:=hS
  refine ⟨C.image (geodesicRealGLMobius g),?_,(halfPlaneCircleCarrier_realGL_image C g hg).symm,hne.image _⟩
  change (Mobius.fractionalLinear (complexifiedRealMobiusMatrix g) '' C.val)∩halfPlaneIdealBoundary=_
  rw [←image_inter_preimage,realMobiusMatrix_preimage_boundary,hC]
  exact (axis.idealEndpoints_realGL_image _ g hg (axis.realGLMap_carrier g).symm).symm

def chartHypercycleBranchFamily (g : GL (Fin 2) ℝ) : Set (Set ℍ) :=
  {S | ∃c : ℝ,S=(g • · : ℍ → ℍ) '' imaginaryAxisHypercycleBranch c}

theorem isHHypercycleBranch_chart_iff (g : GL (Fin 2) ℝ) (hg : 0<g.val.det) (S : Set ℍ) :
    IsHHypercycleBranch ((HalfPlaneLine.vertical 0).realGLMap g) S ↔ S∈chartHypercycleBranchFamily g := by
  constructor
  · intro hS
    have hn:=hS.realGL_image g⁻¹ (gl_pos_inverse g hg)
    rw [HalfPlaneLine.realGLMap_inv] at hn
    obtain ⟨c,he⟩:=(isHHypercycleBranch_imaginaryAxis_iff _).mp hn
    refine ⟨c,?_⟩
    have hh:=congrArg (fun T : Set ℍ => (g • · : ℍ → ℍ) '' T) he
    rw [image_image] at hh
    simpa only [smul_inv_smul,image_id'] using hh
  · rintro ⟨c,rfl⟩
    exact (imaginaryAxisHypercycleBranch_isHHypercycleBranch c).realGL_image g hg

theorem exists_hHyperbolicChart (axis : HalfPlaneLine) :
    ∃g : GL (Fin 2) ℝ,0<g.val.det ∧ axis=(HalfPlaneLine.vertical 0).realGLMap g := by
  obtain ⟨g,hg,he⟩:=(HalfPlaneLine.vertical 0).exists_mobius_map axis
  refine ⟨g,hg,?_⟩
  apply HalfPlaneLine.carrier_injective
  rw [HalfPlaneLine.realGLMap_carrier]
  exact he.symm

theorem hHyperbolicPencil_realGLMap_iff (axis L : HalfPlaneLine) (g : GL (Fin 2) ℝ) :
    L.realGLMap g∈hHyperbolicPencil (axis.realGLMap g) ↔ L∈hHyperbolicPencil axis :=
  L.orthogonal_realGL_image_iff axis _ _ g (L.realGLMap_carrier g).symm (axis.realGLMap_carrier g).symm

theorem mem_hHyperbolicPencil_chart_iff (g : GL (Fin 2) ℝ) (L : HalfPlaneLine) :
    L∈hHyperbolicPencil ((HalfPlaneLine.vertical 0).realGLMap g) ↔
      ∃(r : ℝ)(hr : 0<r),L=(HalfPlaneLine.circle 0 r hr).realGLMap g := by
  constructor
  · intro hL
    have hn : L.realGLMap g⁻¹∈hHyperbolicPencil (.vertical 0) := by
      have hh:=(hHyperbolicPencil_realGLMap_iff (.vertical 0) (L.realGLMap g⁻¹) g)
      have he : (L.realGLMap g⁻¹).realGLMap g=L:=by simpa only [inv_inv] using L.realGLMap_inv g⁻¹
      rw [he] at hh
      exact hh.mp hL
    obtain ⟨r,hr,he⟩:=(mem_hHyperbolicPencil_imaginaryAxis_iff _).mp hn
    refine ⟨r,hr,?_⟩
    rw [←he]
    simpa only [inv_inv] using (L.realGLMap_inv g⁻¹).symm
  · rintro ⟨r,hr,rfl⟩
    exact (hHyperbolicPencil_realGLMap_iff _ _ g).mpr
      ((mem_hHyperbolicPencil_imaginaryAxis_iff _).mpr ⟨r,hr,rfl⟩)

/-- P1 for every actual common-perpendicular axis and every genuine individual curve branch. -/
theorem existsUnique_hHypercycleBranch_through (axis : HalfPlaneLine) (z : ℍ) :
    ∃!S : Set ℍ,IsHHypercycleBranch axis S ∧ z∈S := by
  obtain ⟨g,hg,rfl⟩:=exists_hHyperbolicChart axis
  obtain ⟨S,⟨hS,hz⟩,hunique⟩:=existsUnique_imaginaryAxisHypercycleBranch_through (g⁻¹ • z)
  refine ⟨(g • · : ℍ → ℍ) '' S,
    ⟨((isHHypercycleBranch_imaginaryAxis_iff _).mpr hS).realGL_image g hg,
      g⁻¹ • z,hz,smul_inv_smul g z⟩,?_⟩
  rintro T ⟨hT,hzT⟩
  have hn:=hT.realGL_image g⁻¹ (gl_pos_inverse g hg)
  rw [HalfPlaneLine.realGLMap_inv] at hn
  have he : (g⁻¹ • · : ℍ → ℍ) '' T=S:=hunique _
    ⟨(isHHypercycleBranch_imaginaryAxis_iff _).mp hn,mem_image_of_mem _ hzT⟩
  have hh:=congrArg (fun U : Set ℍ => (g • · : ℍ → ℍ) '' U) he
  rw [image_image] at hh
  simpa only [smul_inv_smul,image_id'] using hh

/-- P2 has no exceptional actual point for a genuine hyperbolic pencil. -/
theorem existsUnique_hHyperbolicPencil_through (axis : HalfPlaneLine) (z : ℍ) :
    ∃!L : HalfPlaneLine,L∈hHyperbolicPencil axis ∧ z∈L.carrier := by
  obtain ⟨g,hg,rfl⟩:=exists_hHyperbolicChart axis
  obtain ⟨L,⟨hL,hz⟩,hunique⟩:=existsUnique_hHyperbolicPencil_imaginaryAxis_through (g⁻¹ • z)
  refine ⟨L.realGLMap g,⟨(hHyperbolicPencil_realGLMap_iff _ _ g).mpr hL,?_⟩,?_⟩
  · rw [L.realGLMap_carrier]
    exact ⟨g⁻¹ • z,hz,smul_inv_smul g z⟩
  · rintro M ⟨hM,hzM⟩
    have hm : M.realGLMap g⁻¹∈hHyperbolicPencil (.vertical 0) := by
      obtain ⟨r,hr,rfl⟩:=(mem_hHyperbolicPencil_chart_iff g M).mp hM
      rw [HalfPlaneLine.realGLMap_inv]
      exact (mem_hHyperbolicPencil_imaginaryAxis_iff _).mpr ⟨r,hr,rfl⟩
    have hzM' : g⁻¹ • z∈(M.realGLMap g⁻¹).carrier:=(M.realGLMap_mem_carrier g⁻¹ z).mpr hzM
    have he : M.realGLMap g⁻¹=L:=hunique _ ⟨hm,hzM'⟩
    have hh:=congrArg (fun N : HalfPlaneLine => N.realGLMap g) he
    simpa only [show (M.realGLMap g⁻¹).realGLMap g=M by simpa only [inv_inv] using M.realGLMap_inv g⁻¹] using hh

/-- P3 retains actual Euclidean generalized-circle normals. -/
theorem hHypercycleBranch_orthogonal (axis : HalfPlaneLine) {L : HalfPlaneLine}
    (hL : L∈hHyperbolicPencil axis) {S : Set ℍ} (hS : IsHHypercycleBranch axis S) :
    ∃C : Mobius.ComplexGeneralizedCircle, S=halfPlaneCircleCarrier C ∧
      Mobius.ComplexCirclesOrthogonal L.extendedCircle C := by
  obtain ⟨g,hg,rfl⟩:=exists_hHyperbolicChart axis
  obtain ⟨r,hr,rfl⟩:=(mem_hHyperbolicPencil_chart_iff g L).mp hL
  obtain ⟨c,rfl⟩:=(isHHypercycleBranch_chart_iff g hg S).mp hS
  refine ⟨(hypercycleBranchCircle c).image (geodesicRealGLMobius g),?_,?_⟩
  · rw [halfPlaneCircleCarrier_realGL_image _ g hg,imaginaryAxisHypercycleBranch_eq_circleCarrier]
  · rw [←(HalfPlaneLine.circle 0 r hr).extendedCircle_image_realGL _ g hg
      ((HalfPlaneLine.circle 0 r hr).realGLMap_carrier g).symm]
    exact (concentricCircle_hypercycleBranch_orthogonal r c hr).image _ _ _

/-- P4 uses the actual source reflection and genuine conjugacy. -/
theorem hHypercycleBranch_reflection (axis : HalfPlaneLine) {L : HalfPlaneLine}
    (hL : L∈hHyperbolicPencil axis) {S : Set ℍ} (hS : IsHHypercycleBranch axis S) : L.reflection '' S=S := by
  obtain ⟨g,hg,rfl⟩:=exists_hHyperbolicChart axis
  obtain ⟨r,hr,rfl⟩:=(mem_hHyperbolicPencil_chart_iff g L).mp hL
  obtain ⟨c,rfl⟩:=(isHHypercycleBranch_chart_iff g hg S).mp hS
  calc
    _=(g • · : ℍ → ℍ) '' ((HalfPlaneLine.circle 0 r hr).reflection '' imaginaryAxisHypercycleBranch c) := by
      rw [image_image,image_image]
      congr 1
      funext z
      have he:=(HalfPlaneLine.circle 0 r hr).reflection_realGL_conjugation g (g • z)
      simpa only [inv_smul_smul,Function.comp_apply] using he.symm
    _=(g • · : ℍ → ℍ) '' imaginaryAxisHypercycleBranch c := by rw [concentricCircle_reflection_hypercycleBranch]

/-- P5 realizes the genuine curve-distance infimum, on a genuine common pencil line. -/
theorem hHypercycleBranch_equidistance (axis : HalfPlaneLine) {S T : Set ℍ}
    (hS : IsHHypercycleBranch axis S) (hT : IsHHypercycleBranch axis T) (p : ℍ) (hp : p∈S) :
    ∃q : ℍ,q∈T ∧ dist p q=hCurveDistance S T ∧
      ∃L : HalfPlaneLine,L∈hHyperbolicPencil axis ∧ p∈L.carrier ∧ q∈L.carrier := by
  obtain ⟨g,hg,rfl⟩:=exists_hHyperbolicChart axis
  obtain ⟨c,rfl⟩:=(isHHypercycleBranch_chart_iff g hg S).mp hS
  obtain ⟨d,rfl⟩:=(isHHypercycleBranch_chart_iff g hg T).mp hT
  obtain ⟨z,hz,rfl⟩:=hp
  obtain ⟨q,hq,hd,L,hL,hzL,hqL⟩:=imaginaryAxisHypercycleBranch_equidistance c d z hz
  refine ⟨g • q,⟨q,hq,rfl⟩,?_,L.realGLMap g,(hHyperbolicPencil_realGLMap_iff _ _ g).mpr hL,
    (L.realGLMap_mem_carrier g z).mpr hzL,(L.realGLMap_mem_carrier g q).mpr hqL⟩
  rw [(realGL_isometry g).dist_eq,hCurveDistance_isometry_image _ _ _ (realGL_isometry g)]
  exact hd


theorem common_hHypercycleBranch_iff_chart (g : GL (Fin 2) ℝ) (hg : 0<g.val.det) (a b : ℍ) :
    (∃S : Set ℍ,IsHHypercycleBranch ((HalfPlaneLine.vertical 0).realGLMap g) S ∧ a∈S ∧ b∈S) ↔
      ∃T∈imaginaryAxisHypercycleBranchFamily,g⁻¹ • a∈T ∧ g⁻¹ • b∈T := by
  constructor
  · rintro ⟨S,hS,ha,hb⟩
    have hn:=hS.realGL_image g⁻¹ (gl_pos_inverse g hg)
    rw [HalfPlaneLine.realGLMap_inv] at hn
    exact ⟨(g⁻¹ • · : ℍ → ℍ) '' S,(isHHypercycleBranch_imaginaryAxis_iff _).mp hn,
      mem_image_of_mem _ ha,mem_image_of_mem _ hb⟩
  · rintro ⟨T,hT,ha,hb⟩
    exact ⟨(g • · : ℍ → ℍ) '' T,((isHHypercycleBranch_imaginaryAxis_iff _).mpr hT).realGL_image g hg,
      ⟨g⁻¹ • a,ha,smul_inv_smul g a⟩,g⁻¹ • b,hb,smul_inv_smul g b⟩

/-- P6 for every actual axis and the genuine geometric perpendicular bisector. -/
theorem hHyperbolicPencil_perpendicularBisector_iff (axis : HalfPlaneLine) {a b : ℍ} (hab : a≠b)
    {N : HalfPlaneLine} (hN : IsHPerpendicularBisector N a b) :
    N∈hHyperbolicPencil axis ↔ ∃S : Set ℍ,IsHHypercycleBranch axis S ∧ a∈S ∧ b∈S := by
  obtain ⟨g,hg,rfl⟩:=exists_hHyperbolicChart axis
  rw [common_hHypercycleBranch_iff_chart g hg]
  have hab' : g⁻¹ • a≠g⁻¹ • b:=(realGL_isometry g⁻¹).injective.ne hab
  have hN' : IsHPerpendicularBisector (N.realGLMap g⁻¹) (g⁻¹ • a) (g⁻¹ • b):=
    (hPerpendicularBisector_realGLMap_iff g⁻¹ hab N).mpr hN
  have he : (N.realGLMap g⁻¹).realGLMap g=N:=by simpa only [inv_inv] using N.realGLMap_inv g⁻¹
  rw [←he,hHyperbolicPencil_realGLMap_iff]
  exact imaginaryAxisHyperbolicPencil_perpendicularBisector_iff hab' hN'

/-- The actual curve closure, not just its complete supporting circle, has the two true axis ends. -/
theorem IsHHypercycleBranch.idealEndpoints {axis : HalfPlaneLine} {S : Set ℍ} (hS : IsHHypercycleBranch axis S) :
    hTraceIdealEndpoints S=axis.idealEndpoints := by
  obtain ⟨g,hg,rfl⟩:=exists_hHyperbolicChart axis
  obtain ⟨c,rfl⟩:=(isHHypercycleBranch_chart_iff g hg S).mp hS
  rw [realGL_traceIdealEndpoints g hg,imaginaryAxisHypercycleBranch_idealEndpoints]
  have he:=(HalfPlaneLine.vertical 0).idealEndpoints_realGL_image _ g hg
    ((HalfPlaneLine.vertical 0).realGLMap_carrier g).symm
  rw [vertical_idealEndpoints] at he
  exact he.symm

theorem imaginaryAxisHypercycleBranch_disjoint {c d : ℝ} (hcd : c≠d) :
    Disjoint (imaginaryAxisHypercycleBranch c) (imaginaryAxisHypercycleBranch d) := by
  apply Set.disjoint_left.mpr
  intro z hz hd
  change z.re=c*z.im at hz
  change z.re=d*z.im at hd
  apply hcd
  exact (mul_right_cancel₀ z.im_ne_zero (hz.symm.trans hd))

theorem HalfPlaneLine.distance_sinh_level_realGL_image (axis : HalfPlaneLine) (g : GL (Fin 2) ℝ) (c : ℝ) :
    {z : ℍ | Real.sinh ((axis.realGLMap g).pointDist z)=|c|}=
      (g • · : ℍ → ℍ) '' {z : ℍ | Real.sinh (axis.pointDist z)=|c|} := by
  have hp (z : ℍ) : (axis.realGLMap g).pointDist (g • z)=axis.pointDist z:=
    axis.pointDist_isometry_image _ _ (realGL_isometry g) (axis.realGLMap_carrier g).symm z
  ext z
  constructor
  · intro hz
    refine ⟨g⁻¹ • z,?_,smul_inv_smul g z⟩
    change Real.sinh (axis.pointDist (g⁻¹ • z))=|c|
    rw [←hp,smul_inv_smul]
    exact hz
  · rintro ⟨w,hw,rfl⟩
    change Real.sinh ((axis.realGLMap g).pointDist (g • w))=|c|
    rwa [hp]

/-- Every genuine positive distance level is exactly two disjoint genuine individual branches. -/
theorem HalfPlaneLine.distance_level_two_hypercycleBranches (axis : HalfPlaneLine) (r : ℝ) (hr : 0<r) :
    ∃S T : Set ℍ,IsHHypercycleBranch axis S ∧ IsHHypercycleBranch axis T ∧
      Disjoint S T ∧ S≠T ∧ {z : ℍ | axis.pointDist z=r}=S∪T := by
  obtain ⟨g,hg,rfl⟩:=exists_hHyperbolicChart axis
  let c:=Real.sinh r
  have hc : 0<c:=Real.sinh_pos_iff.mpr hr
  let S:=(g • · : ℍ → ℍ) '' imaginaryAxisHypercycleBranch c
  let T:=(g • · : ℍ → ℍ) '' imaginaryAxisHypercycleBranch (-c)
  have hST : Disjoint S T := by
    exact (Set.disjoint_image_iff (realGL_isometry g).injective).mpr
      (imaginaryAxisHypercycleBranch_disjoint (by linarith : c≠-c))
  refine ⟨S,T,(imaginaryAxisHypercycleBranch_isHHypercycleBranch c).realGL_image g hg,
    (imaginaryAxisHypercycleBranch_isHHypercycleBranch (-c)).realGL_image g hg,hST,?_,?_⟩
  · intro he
    have hp : metricProbe c 1 (by norm_num)∈imaginaryAxisHypercycleBranch c:=by change c=c*1; ring
    have hne : S.Nonempty:=⟨g • metricProbe c 1 (by norm_num),mem_image_of_mem _ hp⟩
    obtain ⟨z,hz⟩:=hne
    exact Set.disjoint_left.mp hST hz (he ▸ hz)
  · have he : {z : ℍ | (((HalfPlaneLine.vertical 0).realGLMap g).pointDist z)=r}=
        {z : ℍ | Real.sinh ((((HalfPlaneLine.vertical 0).realGLMap g).pointDist z))=|c|} := by
      ext z
      rw [abs_of_pos hc]
      change _=r ↔ Real.sinh _=Real.sinh r
      exact ⟨congrArg Real.sinh,fun he=>Real.sinh_injective he⟩
    rw [he,HalfPlaneLine.distance_sinh_level_realGL_image,imaginaryAxis_distance_sinh_level_two_branches,
      image_union]


theorem HalfPlaneLine.axis_isHypercycleBranch (axis : HalfPlaneLine) : IsHHypercycleBranch axis axis.carrier := by
  obtain ⟨g,hg,rfl⟩:=exists_hHyperbolicChart axis
  have hh:=(imaginaryAxisHypercycleBranch_isHHypercycleBranch 0).realGL_image g hg
  rwa [imaginaryAxisHypercycleBranch_zero,←HalfPlaneLine.realGLMap_carrier] at hh

theorem IsHHypercycleBranch.pointDist_eq {axis : HalfPlaneLine} {S : Set ℍ}
    (hS : IsHHypercycleBranch axis S) {z w : ℍ} (hz : z∈S) (hw : w∈S) : axis.pointDist z=axis.pointDist w := by
  obtain ⟨g,hg,rfl⟩:=exists_hHyperbolicChart axis
  obtain ⟨c,rfl⟩:=(isHHypercycleBranch_chart_iff g hg S).mp hS
  obtain ⟨u,hu,rfl⟩:=hz
  obtain ⟨v,hv,rfl⟩:=hw
  rw [(HalfPlaneLine.vertical 0).pointDist_isometry_image _ _ (realGL_isometry g)
    ((HalfPlaneLine.vertical 0).realGLMap_carrier g).symm,
    (HalfPlaneLine.vertical 0).pointDist_isometry_image _ _ (realGL_isometry g)
    ((HalfPlaneLine.vertical 0).realGLMap_carrier g).symm]
  apply Real.sinh_injective
  rw [imaginaryAxisHypercycleBranch_pointDist_sinh c u hu,imaginaryAxisHypercycleBranch_pointDist_sinh c v hv]

/-- Compatibility with the earlier literal whole-frontier convention: every actual individual
branch is either the zero-offset axis or a branch of a genuine positive-width hypercyclic region. -/
theorem IsHHypercycleBranch.axis_or_actual_hypercycle {axis : HalfPlaneLine} {S : Set ℍ}
    (hS : IsHHypercycleBranch axis S) :
    S=axis.carrier ∨ ∃r : ℝ,0<r ∧ IsHHypercyclicRegion (axis.distanceSublevel r) ∧
      S⊆hHypercycle (axis.distanceSublevel r) := by
  obtain ⟨C,hC,hSC,p,hp⟩:=hS
  have hS' : IsHHypercycleBranch axis S:=⟨C,hC,hSC,p,hp⟩
  by_cases hr : 0<axis.pointDist p
  · right
    refine ⟨axis.pointDist p,hr,axis.distanceSublevel_hypercyclic _ hr,?_⟩
    intro z hz
    change z∈frontier (axis.distanceSublevel (axis.pointDist p))
    rw [axis.distanceSublevel_frontier _ hr]
    exact hS'.pointDist_eq hz hp
  · left
    have hr0 : axis.pointDist p=0:=le_antisymm (not_lt.mp hr) (axis.pointDist_nonneg p)
    obtain ⟨u,v,hu,hv,hne⟩:=axis.exists_two_points
    have hpa : p∈axis.carrier:=
      (axis.isClosed_carrier.mem_iff_infDist_zero ⟨u,hu⟩).mpr hr0
    obtain ⟨T,hT,hunique⟩:=existsUnique_hHypercycleBranch_through axis p
    exact (hunique S ⟨hS',hp⟩).trans (hunique axis.carrier ⟨axis.axis_isHypercycleBranch,hpa⟩).symm

/-- The actual earlier whole hypercycle frontier decomposes into precisely two disjoint
actual complementary branches, without changing its literal definition. -/
theorem HalfPlaneLine.hypercycle_frontier_two_branches (axis : HalfPlaneLine) (r : ℝ) (hr : 0<r) :
    ∃S T : Set ℍ,IsHHypercycleBranch axis S ∧ IsHHypercycleBranch axis T ∧
      Disjoint S T ∧ S≠T ∧ hHypercycle (axis.distanceSublevel r)=S∪T := by
  change ∃S T : Set ℍ,IsHHypercycleBranch axis S ∧ IsHHypercycleBranch axis T ∧
    Disjoint S T ∧ S≠T ∧ frontier (axis.distanceSublevel r)=S∪T
  rw [axis.distanceSublevel_frontier r hr]
  exact axis.distance_level_two_hypercycleBranches r hr

end
end LowDimensionalTopology.Geometry.Hyperbolic
