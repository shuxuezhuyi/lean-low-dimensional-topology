/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Euclidean.InnerProduct.Gram
public import LowDimensionalTopology.Geometry.Hyperbolic.Geodesic.SideNormalGeometry
public import LowDimensionalTopology.Geometry.Hyperbolic.Convexity.IdealHull.NielsenGapLines

/-!
# Actual finite Nielsen-core polygon geometry
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
open Set Topology Filter
open scoped UpperHalfPlane Complex.UnitDisc OnePoint RealInnerProductSpace
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

theorem _root_.LowDimensionalTopology.Geometry.Hyperbolic.NielsenHalfPlaneGap.cut_line_iff
    (G : Hyperbolic.NielsenHalfPlaneGap)
    (z : ℍ) :
    z∈G.line.carrier ↔ inner ℝ G.cutNormal (Hyperbolic.halfPlaneKleinCoordinate z)=G.cutThreshold := by
  have hD : 0<z.re^2+z.im^2+1 := by positivity
  have he : inner ℝ G.cutNormal (Hyperbolic.halfPlaneKleinCoordinate z)=
      (G.cutNormal.re*(z.re^2+z.im^2-1)-2*G.cutNormal.im*z.re)/(z.re^2+z.im^2+1) := by
    rw [Hyperbolic.halfPlaneKleinCoordinate_explicit,_root_.LowDimensionalTopology.Geometry.Euclidean.complex_real_inner_coordinates]
    ring
  rw [he,div_eq_iff hD.ne']
  cases G with
  | bounded a b hab =>
    change ‖(z:ℂ)-(((a+b)/2:ℝ):ℂ)‖=(b-a)/2 ↔ _
    have hn : ‖(z:ℂ)-(((a+b)/2:ℝ):ℂ)‖^2=(z.re-(a+b)/2)^2+z.im^2 := by
      rw [←Complex.normSq_eq_norm_sq,Complex.normSq_apply]
      simp only [Complex.sub_re,Complex.sub_im,Complex.ofReal_re,Complex.ofReal_im,sub_zero]
      change (z.re-(a+b)/2)*(z.re-(a+b)/2)+z.im*z.im=(z.re-(a+b)/2)^2+z.im^2
      ring
    dsimp [Hyperbolic.NielsenHalfPlaneGap.cutNormal,Hyperbolic.NielsenHalfPlaneGap.cutThreshold]
    constructor <;> intro h <;> nlinarith [norm_nonneg ((z:ℂ)-(((a+b)/2:ℝ):ℂ))]
  | left b =>
    change z.re=b ↔ _
    dsimp [Hyperbolic.NielsenHalfPlaneGap.cutNormal,Hyperbolic.NielsenHalfPlaneGap.cutThreshold]
    constructor <;> intro h <;> nlinarith
  | right a =>
    change z.re=a ↔ _
    dsimp [Hyperbolic.NielsenHalfPlaneGap.cutNormal,Hyperbolic.NielsenHalfPlaneGap.cutThreshold]
    constructor <;> intro h <;> nlinarith

theorem _root_.LowDimensionalTopology.Geometry.Hyperbolic.NielsenHalfPlaneGap.line_re_mem_closure
    (G : Hyperbolic.NielsenHalfPlaneGap)
    (z : ℍ)
    (hz : z∈G.line.carrier) : z.re∈closure G.carrier := by
  cases G with
  | bounded a b hab =>
    rw [Hyperbolic.NielsenHalfPlaneGap.carrier,closure_Ioo hab.ne]
    have hh:=congrArg (fun t:ℝ=>t^2) hz
    change ‖(z:ℂ)-(((a+b)/2:ℝ):ℂ)‖^2=((b-a)/2)^2 at hh
    rw [←Complex.normSq_eq_norm_sq,Complex.normSq_apply] at hh
    simp only [Complex.sub_re,Complex.sub_im,Complex.ofReal_re,Complex.ofReal_im,sub_zero] at hh
    change (z.re-(a+b)/2)*(z.re-(a+b)/2)+z.im*z.im=((b-a)/2)^2 at hh
    constructor <;> nlinarith [sq_pos_of_pos z.im_pos]
  | left b =>
    change z.re=b at hz
    rw [Hyperbolic.NielsenHalfPlaneGap.carrier,closure_Iio]
    exact hz.le
  | right a =>
    change z.re=a at hz
    rw [Hyperbolic.NielsenHalfPlaneGap.carrier,closure_Ioi]
    exact hz.ge

theorem _root_.LowDimensionalTopology.Geometry.Hyperbolic.NielsenHalfPlaneGap.removed_re_mem
    (G : Hyperbolic.NielsenHalfPlaneGap)
    (z : ℍ)
    (hz : G.cutThreshold < inner ℝ G.cutNormal (Hyperbolic.halfPlaneKleinCoordinate z)) :
    z.re∈G.carrier := by
  have hD : 0<z.re^2+z.im^2+1 := by positivity
  have he : inner ℝ G.cutNormal (Hyperbolic.halfPlaneKleinCoordinate z)=
      (G.cutNormal.re*(z.re^2+z.im^2-1)-2*G.cutNormal.im*z.re)/(z.re^2+z.im^2+1) := by
    rw [Hyperbolic.halfPlaneKleinCoordinate_explicit,_root_.LowDimensionalTopology.Geometry.Euclidean.complex_real_inner_coordinates]
    ring
  rw [he,lt_div_iff₀ hD] at hz
  cases G with
  | bounded a b hab =>
    change a<z.re ∧ z.re<b
    dsimp [Hyperbolic.NielsenHalfPlaneGap.cutNormal,Hyperbolic.NielsenHalfPlaneGap.cutThreshold] at hz
    constructor <;> nlinarith [sq_pos_of_pos z.im_pos]
  | left b =>
    change z.re<b
    dsimp [Hyperbolic.NielsenHalfPlaneGap.cutNormal,Hyperbolic.NielsenHalfPlaneGap.cutThreshold] at hz
    nlinarith
  | right a =>
    change a<z.re
    dsimp [Hyperbolic.NielsenHalfPlaneGap.cutNormal,Hyperbolic.NielsenHalfPlaneGap.cutThreshold] at hz
    nlinarith

theorem nielsenGap_line_all_weak_cuts (A : Set ℝ)
    (G : Hyperbolic.NielsenHalfPlaneGap)
    (hG : G.carrier∈Auxiliary.Topology.nielsenRealGapFamily A)
    (z : ℍ) (hz : z∈G.line.carrier) (J : Hyperbolic.NielsenHalfPlaneGap)
    (hJ : J.carrier∈Auxiliary.Topology.nielsenRealGapFamily A) :
    inner ℝ J.cutNormal (Hyperbolic.halfPlaneKleinCoordinate z)≤J.cutThreshold := by
  by_cases he : G.carrier=J.carrier
  · have hline : G.line=J.line := nielsenGap_line_eq_of_carrier_eq G J he
    exact ((Hyperbolic.NielsenHalfPlaneGap.cut_line_iff J z).mp (hline ▸ hz)).le
  · by_contra hn
    have hr : z.re∈J.carrier := Hyperbolic.NielsenHalfPlaneGap.removed_re_mem J z (lt_of_not_ge hn)
    have hdis := Auxiliary.Topology.nielsenRealGapFamily_pairwiseDisjoint A hG hJ he
    have hcl := Hyperbolic.NielsenHalfPlaneGap.line_re_mem_closure G z hz
    have hnh : J.carrier∈𝓝 z.re := J.carrier_isOpen.mem_nhds hr
    have hmeet := mem_closure_iff_nhds.mp hcl _ hnh
    obtain ⟨y,hyJ,hyG⟩:=hmeet
    exact disjoint_left.mp hdis hyG hyJ

theorem nielsenRealArcRegion_mem_closure_of_weak (A : Set ℝ)
    (hne : (Hyperbolic.nielsenRealArcRegion A).Nonempty) (z : ℍ)
    (hz : ∀G : Hyperbolic.NielsenHalfPlaneGap,G.carrier∈Auxiliary.Topology.nielsenRealGapFamily A →
      inner ℝ G.cutNormal (Hyperbolic.halfPlaneKleinCoordinate z)≤G.cutThreshold) :
    z∈closure (Hyperbolic.nielsenRealArcRegion A) := by
  obtain ⟨w,hw⟩:=hne
  let f : ℝ→ℂ:=AffineMap.lineMap (Hyperbolic.halfPlaneKleinCoordinate z) (Hyperbolic.halfPlaneKleinCoordinate w)
  have hball (x:ℍ) : Hyperbolic.halfPlaneKleinCoordinate x∈Metric.ball (0:ℂ) 1 := by
    rw [←Hyperbolic.range_halfPlaneKleinCoordinate]
    exact mem_range_self x
  have himage : f '' Ioo 0 1⊆Hyperbolic.halfPlaneKleinCoordinate '' Hyperbolic.nielsenRealArcRegion A := by
    rintro _ ⟨t,ht,rfl⟩
    have hfB : f t∈Metric.ball (0:ℂ) 1 :=
      (convex_ball (0:ℂ) 1).segment_subset (hball z) (hball w)
        (lineMap_mem_segment ℝ _ _ ⟨ht.1.le,ht.2.le⟩)
    rw [←Hyperbolic.range_halfPlaneKleinCoordinate] at hfB
    obtain ⟨u,hu⟩:=hfB
    refine ⟨u,?_,hu⟩
    intro G hG
    apply (G.cut_keptSide u).mp
    rw [hu]
    have hwG := (G.cut_keptSide w).mpr (hw G hG)
    have hzG := hz G hG
    have he : inner ℝ G.cutNormal (f t)=
        (1-t)*inner ℝ G.cutNormal (Hyperbolic.halfPlaneKleinCoordinate z)+
          t*inner ℝ G.cutNormal (Hyperbolic.halfPlaneKleinCoordinate w) := by
      simp only [f,AffineMap.lineMap_apply,vsub_eq_sub,vadd_eq_add,inner_add_right,inner_sub_right,real_inner_smul_right]
      ring
    rw [he]
    nlinarith [mul_nonneg (show 0≤1-t by linarith [ht.2]) (sub_nonneg.mpr hzG),
      mul_pos ht.1 (sub_pos.mpr hwG)]
  have hzC : Hyperbolic.halfPlaneKleinCoordinate z∈closure (Hyperbolic.halfPlaneKleinCoordinate '' Hyperbolic.nielsenRealArcRegion A) := by
    have hzero : (0:ℝ)∈closure (Ioo 0 1) := by
      rw [closure_Ioo (by norm_num : (0:ℝ)≠1)]
      exact ⟨le_rfl,by norm_num⟩
    have hh := image_closure_subset_closure_image
      (AffineMap.lineMap_continuous : Continuous f) ⟨0,hzero,rfl⟩
    have hh' : Hyperbolic.halfPlaneKleinCoordinate z∈closure (f '' Ioo 0 1) := by
      simpa only [f,AffineMap.lineMap_apply_zero] using hh
    exact closure_mono himage hh'
  rw [Hyperbolic.isOpenEmbedding_halfPlaneKleinCoordinate.isEmbedding.closure_eq_preimage_closure_image]
  exact hzC

theorem nielsenGap_line_subset_frontier (A : Set ℝ)
    (ho : IsOpen (Hyperbolic.nielsenRealArcRegion A))
    (hne : (Hyperbolic.nielsenRealArcRegion A).Nonempty)
    (G : Hyperbolic.NielsenHalfPlaneGap)
    (hG : G.carrier∈Auxiliary.Topology.nielsenRealGapFamily A) :
    G.line.carrier⊆frontier (Hyperbolic.nielsenRealArcRegion A) := by
  intro z hz
  rw [ho.frontier_eq]
  refine ⟨nielsenRealArcRegion_mem_closure_of_weak A hne z
    (nielsenGap_line_all_weak_cuts A G hG z hz),?_⟩
  intro hzN
  exact disjoint_left.mp G.keptSide_disjoint_line (hzN G hG) hz

theorem nielsenRealArcRegion_frontier_exists_gap (A : Set ℝ)
    (ho : IsOpen (Hyperbolic.nielsenRealArcRegion A)) (z : ℍ)
    (hz : z∈frontier (Hyperbolic.nielsenRealArcRegion A)) :
    ∃G : Hyperbolic.NielsenHalfPlaneGap,G.carrier∈Auxiliary.Topology.nielsenRealGapFamily A ∧ z∈G.line.carrier := by
  have hnot : z∉Hyperbolic.nielsenRealArcRegion A := by
    rw [ho.frontier_eq] at hz
    exact hz.2
  change ¬∀G : Hyperbolic.NielsenHalfPlaneGap,G.carrier∈Auxiliary.Topology.nielsenRealGapFamily A → z∈G.keptSide at hnot
  push Not at hnot
  obtain ⟨G,hG,hzG⟩:=hnot
  refine ⟨G,hG,(Hyperbolic.NielsenHalfPlaneGap.cut_line_iff G z).mpr ?_⟩
  have hclosed : IsClosed {u:ℍ | inner ℝ G.cutNormal (Hyperbolic.halfPlaneKleinCoordinate u)≤G.cutThreshold} :=
    isClosed_le (continuous_const.inner Hyperbolic.isOpenEmbedding_halfPlaneKleinCoordinate.continuous)
      continuous_const
  have hle : inner ℝ G.cutNormal (Hyperbolic.halfPlaneKleinCoordinate z)≤G.cutThreshold :=
    closure_minimal (fun u (hu:u∈Hyperbolic.nielsenRealArcRegion A)=>(G.cut_keptSide u).mpr (hu G hG) |>.le) hclosed
      (frontier_subset_closure hz)
  exact le_antisymm hle (not_lt.mp (fun hh=>hzG ((G.cut_keptSide z).mp hh)))

theorem nielsenRealArcRegion_frontier_eq_gap_lines (A : Set ℝ)
    (ho : IsOpen (Hyperbolic.nielsenRealArcRegion A))
    (hne : (Hyperbolic.nielsenRealArcRegion A).Nonempty) :
    frontier (Hyperbolic.nielsenRealArcRegion A)=
      ⋃G : Hyperbolic.NielsenHalfPlaneGap,⋃_ : G.carrier∈Auxiliary.Topology.nielsenRealGapFamily A,G.line.carrier := by
  apply subset_antisymm
  · intro z hz
    obtain ⟨G,hG,hzG⟩:=nielsenRealArcRegion_frontier_exists_gap A ho z hz
    exact mem_iUnion.mpr ⟨G,mem_iUnion.mpr ⟨hG,hzG⟩⟩
  · intro z hz
    obtain ⟨G,hz⟩:=mem_iUnion.mp hz
    obtain ⟨hG,hzG⟩:=mem_iUnion.mp hz
    exact nielsenGap_line_subset_frontier A ho hne G hG hzG

end LowDimensionalTopology.Geometry.Fuchsian
