module
public import LowDimensionalTopology.Geometry.Hyperbolic.Convexity.NativeHalfPlaneComponents
public import LowDimensionalTopology.Geometry.Auxiliary.Topology.Germs
public import Mathlib.Tactic
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter Topology InnerProductGeometry
open scoped UpperHalfPlane Complex.UnitDisc
namespace LowDimensionalTopology.Geometry.Hyperbolic

/-- The actual two-sided native locally geodesic boundary determines a unique local side,
without finite-sidedness, compactness or global convexity. -/
theorem native_jordan_linear_boundary_interior_germ {I O B : Set ℍ} {x : ℍ}
    (hI : IsOpen I) (hO : IsOpen O) (hd : Disjoint I O) (hu : I ∪ O = Bᶜ)
    (hxI : x ∈ frontier I) (hxO : x ∈ frontier O) (m : ℂ) (t : ℝ)
    (he : ∀ᶠ y in 𝓝 x,y∈B ↔inner ℝ m (halfPlaneKleinCoordinate y)=t) :
    (∀ᶠ y in 𝓝 x,y∈I ↔t < inner ℝ m (halfPlaneKleinCoordinate y)) ∨
      (∀ᶠ y in 𝓝 x,y∈I ↔inner ℝ m (halfPlaneKleinCoordinate y)<t) := by
  let f : ℍ→ℝ:=fun y=>inner ℝ m (halfPlaneKleinCoordinate y)-t
  have he : ∀ᶠy in 𝓝 x,y∈B ↔f y=0 := by
    filter_upwards [he] with y hy
    exact hy.trans sub_eq_zero.symm
  obtain ⟨r,hr,hre⟩ := Metric.mem_nhds_iff.mp he
  let A : Set ℍ := Metric.ball x r ∩ {y | 0 < f y}
  let C : Set ℍ := Metric.ball x r ∩ {y | f y < 0}
  have hPos : HConvex {y : ℍ | 0<f y} := by
    apply (hConvex_iff_cayley_discHConvex _).mpr
    have he : halfPlaneToDisc '' {y : ℍ | 0<f y}=discKleinCutGt m t := by
      ext z
      constructor
      · rintro ⟨w,hw,rfl⟩
        exact sub_pos.mp hw
      · intro hz
        refine ⟨discToHalfPlane z,?_,halfPlaneToDisc_discToHalfPlane z⟩
        change 0< inner ℝ m (halfPlaneKleinCoordinate (discToHalfPlane z))-t
        rw [halfPlaneKleinCoordinate,halfPlaneToDisc_discToHalfPlane]
        exact sub_pos.mpr hz
    rw [he]
    exact discKleinCutGt_hConvex m t
  have hNeg : HConvex {y : ℍ | f y<0} := by
    apply (hConvex_iff_cayley_discHConvex _).mpr
    have he : halfPlaneToDisc '' {y : ℍ | f y<0}=discKleinCutLt m t := by
      ext z
      constructor
      · rintro ⟨w,hw,rfl⟩
        exact sub_neg.mp hw
      · intro hz
        refine ⟨discToHalfPlane z,?_,halfPlaneToDisc_discToHalfPlane z⟩
        change inner ℝ m (halfPlaneKleinCoordinate (discToHalfPlane z))-t<0
        rw [halfPlaneKleinCoordinate,halfPlaneToDisc_discToHalfPlane]
        exact sub_neg.mpr hz
    rw [he]
    exact discKleinCutLt_hConvex m t
  have hAc : IsPreconnected A := _root_.LowDimensionalTopology.Geometry.Hyperbolic.HConvex.isPreconnected (by
    intro y hy z hz w hw
    exact ⟨hConvex_metric_ball x r y hy.1 z hz.1 hw,hPos y hy.2 z hz.2 hw⟩)
  have hCc : IsPreconnected C := _root_.LowDimensionalTopology.Geometry.Hyperbolic.HConvex.isPreconnected (by
    intro y hy z hz w hw
    exact ⟨hConvex_metric_ball x r y hy.1 z hz.1 hw,hNeg y hy.2 z hz.2 hw⟩)
  have hmem (y : ℍ) (hy : y ∈ Metric.ball x r) :
      (y ∈ I ∨ y ∈ O) ↔ f y ≠ 0 := by
    change y ∈ I ∪ O ↔ _
    have hh : y ∈ B ↔ f y = 0 := hre hy
    rw [hu,mem_compl_iff,hh]
  have hAsub : A ⊆ I ∪ O := by
    intro y hy
    exact (hmem y hy.1).mpr (ne_of_gt hy.2)
  have hCsub : C ⊆ I ∪ O := by
    intro y hy
    exact (hmem y hy.1).mpr (ne_of_lt hy.2)
  have hexI : ∃ y ∈ Metric.ball x r, y ∈ I := by
    exact mem_closure_iff.mp (frontier_subset_closure hxI) (Metric.ball x r)
      Metric.isOpen_ball (Metric.mem_ball_self hr)
  have hexO : ∃ y ∈ Metric.ball x r, y ∈ O := by
    exact mem_closure_iff.mp (frontier_subset_closure hxO) (Metric.ball x r)
      Metric.isOpen_ball (Metric.mem_ball_self hr)
  have hnotBothI : ¬ (A ⊆ I ∧ C ⊆ I) := by
    rintro ⟨ha,hc⟩
    obtain ⟨y,hy,hyo⟩ := hexO
    have hn := (hmem y hy).mp (Or.inr hyo)
    rcases lt_or_gt_of_ne hn with hneg | hpos
    · exact Set.disjoint_left.mp hd (hc ⟨hy,hneg⟩) hyo
    · exact Set.disjoint_left.mp hd (ha ⟨hy,hpos⟩) hyo
  have hnotBothO : ¬ (A ⊆ O ∧ C ⊆ O) := by
    rintro ⟨ha,hc⟩
    obtain ⟨y,hy,hyi⟩ := hexI
    have hn := (hmem y hy).mp (Or.inl hyi)
    rcases lt_or_gt_of_ne hn with hneg | hpos
    · exact Set.disjoint_left.mp hd hyi (hc ⟨hy,hneg⟩)
    · exact Set.disjoint_left.mp hd hyi (ha ⟨hy,hpos⟩)
  rcases hAc.subset_or_subset hI hO hd hAsub with ha | ha
  · have hc : C ⊆ O := (hCc.subset_or_subset hI hO hd hCsub).resolve_left
      (fun hi => hnotBothI ⟨ha,hi⟩)
    left
    suffices h : ∀ᶠ y in 𝓝 x,y∈I ↔0<f y by
      simpa only [f,sub_pos] using h
    filter_upwards [Metric.ball_mem_nhds x hr] with y hy
    constructor
    · intro hi
      have hn := (hmem y hy).mp (Or.inl hi)
      rcases lt_or_gt_of_ne hn with hneg | hpos
      · exact (Set.disjoint_left.mp hd hi (hc ⟨hy,hneg⟩)).elim
      · exact hpos
    · intro hypos
      exact ha ⟨hy,hypos⟩
  · have hc : C ⊆ I := (hCc.subset_or_subset hI hO hd hCsub).resolve_right
      (fun ho => hnotBothO ⟨ha,ho⟩)
    right
    suffices h : ∀ᶠ y in 𝓝 x,y∈I ↔f y<0 by
      simpa only [f,sub_neg] using h
    filter_upwards [Metric.ball_mem_nhds x hr] with y hy
    constructor
    · intro hi
      have hn := (hmem y hy).mp (Or.inl hi)
      rcases lt_or_gt_of_ne hn with hneg | hpos
      · exact hneg
      · exact (Set.disjoint_left.mp hd hi (ha ⟨hy,hpos⟩)).elim
    · intro hyneg
      exact hc ⟨hy,hyneg⟩



/-- For a genuine regular-open native polygon, every frontier point is approached from
both its actual interior and its actual exterior. -/
theorem native_regular_open_frontier_regions {I : Set ℍ} (hI : IsOpen I)
    (hreg : interior (closure I)=I) :
    IsOpen (closure I)ᶜ ∧Disjoint I (closure I)ᶜ ∧
      I∪(closure I)ᶜ=(frontier I)ᶜ ∧frontier ((closure I)ᶜ)=frontier I := by
  refine ⟨isClosed_closure.isOpen_compl,?_,?_,?_⟩
  · exact disjoint_compl_right.mono_left subset_closure
  · rw [hI.frontier_eq]
    ext x
    simp only [mem_union,mem_compl_iff,Set.mem_sdiff]
    tauto
  · rw [frontier_compl,isClosed_closure.frontier_eq,hreg,hI.frontier_eq]

/-- An actual regular-open native polygon whose frontier locally is an actual h-line
has the original one-sided open half-plane germ, without finite-sidedness or compactness. -/
theorem native_regular_open_line_germ {I : Set ℍ} (hI : IsOpen I)
    (hreg : interior (closure I)=I) {x : ℍ} (hx : x∈frontier I)
    (N : HalfPlaneLine) (he : ∀ᶠy in 𝓝 x,y∈frontier I ↔y∈N.carrier) :
    ∃m : ℂ,∃t : ℝ,m≠0 ∧
      (∀z : ℍ,z∈N.carrier ↔inner ℝ m (halfPlaneKleinCoordinate z)=t) ∧
      (∀ᶠy in 𝓝 x,y∈I ↔inner ℝ m (halfPlaneKleinCoordinate y)<t) := by
  obtain ⟨m,t,hm,hLine⟩:=N.klein_affine_equation
  obtain ⟨hO,hd,hu,hfront⟩:=native_regular_open_frontier_regions hI hreg
  have hxO : x∈frontier ((closure I)ᶜ):=hfront.symm ▸ hx
  have he' : ∀ᶠy in 𝓝 x,y∈frontier I ↔inner ℝ m (halfPlaneKleinCoordinate y)=t := by
    filter_upwards [he] with y hy
    exact hy.trans (hLine y)
  rcases native_jordan_linear_boundary_interior_germ hI hO hd hu hx hxO m t he' with hp | hn
  · refine ⟨-m,-t,neg_ne_zero.mpr hm,?_,?_⟩
    · intro z
      rw [inner_neg_left,neg_inj,hLine]
    · filter_upwards [hp] with y hy
      simpa only [inner_neg_left,neg_lt_neg_iff] using hy
  · exact ⟨m,t,hm,hLine,hn⟩

/-- The genuine closure of a regular-open native polygon has a closed half-plane germ at
any actual locally geodesic frontier point. -/
theorem native_regular_closed_line_germ {I : Set ℍ} (hI : IsOpen I)
    (hreg : interior (closure I)=I) {x : ℍ} (hx : x∈frontier I)
    (N : HalfPlaneLine) (he : ∀ᶠy in 𝓝 x,y∈frontier I ↔y∈N.carrier) :
    ∃m : ℂ,∃t : ℝ,m≠0 ∧
      (∀z : ℍ,z∈N.carrier ↔inner ℝ m (halfPlaneKleinCoordinate z)=t) ∧
      (∀ᶠy in 𝓝 x,y∈closure I ↔inner ℝ m (halfPlaneKleinCoordinate y)≤t) := by
  obtain ⟨m,t,hm,hLine,hOpen⟩:=native_regular_open_line_germ hI hreg hx N he
  refine ⟨m,t,hm,hLine,?_⟩
  have hClosed:=Auxiliary.Topology.angular_closure_germ hOpen
  change ∀ᶠy in 𝓝 x,y∈closure I ↔y∈closure {y : ℍ|inner ℝ m (halfPlaneKleinCoordinate y)<t} at hClosed
  rwa [native_support_cut_closure hm t] at hClosed

end LowDimensionalTopology.Geometry.Hyperbolic
