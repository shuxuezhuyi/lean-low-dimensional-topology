/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Hyperbolic.Triangle.TriangleCoordinates
public import Mathlib.Analysis.Normed.Operator.Banach
public import LowDimensionalTopology.Geometry.Hyperbolic.Metric.HyperbolicBalls
public import Mathlib.Analysis.Normed.Module.Connected

/-!
# Actual compact triangle closures and boundaries
-/

@[expose] public section
open Set Module
open scoped UpperHalfPlane OnePoint Topology Complex.UnitDisc
namespace LowDimensionalTopology.Geometry.Hyperbolic
noncomputable section

theorem standardClosedTriangle_eq_cuts : standardClosedTriangle =
    {p : ℝ × ℝ | 0 ≤ p.1} ∩ ({p | 0 ≤ p.2} ∩ {p | p.1 + p.2 ≤ 1}) := rfl

theorem standardClosedTriangle_convex : Convex ℝ standardClosedTriangle := by
  rw [standardClosedTriangle_eq_cuts]
  exact (convex_halfSpace_ge (ContinuousLinearMap.fst ℝ ℝ ℝ).toLinearMap.isLinear (0 : ℝ)).inter
    ((convex_halfSpace_ge (ContinuousLinearMap.snd ℝ ℝ ℝ).toLinearMap.isLinear (0 : ℝ)).inter
      (convex_halfSpace_le
        (ContinuousLinearMap.fst ℝ ℝ ℝ + ContinuousLinearMap.snd ℝ ℝ ℝ).toLinearMap.isLinear (1 : ℝ)))

theorem standardClosedTriangle_isClosed : IsClosed standardClosedTriangle := by
  rw [standardClosedTriangle_eq_cuts]
  exact (isClosed_le continuous_const continuous_fst).inter
    ((isClosed_le continuous_const continuous_snd).inter
      (isClosed_le (continuous_fst.add continuous_snd) continuous_const))

theorem standardClosedTriangle_isCompact : IsCompact standardClosedTriangle := by
  apply isCompact_Icc.of_isClosed_subset standardClosedTriangle_isClosed (s := Icc (0,0) (1,1))
  intro p hp
  change 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 + p.2 ≤ 1 at hp
  exact ⟨⟨hp.1,hp.2.1⟩,⟨by linarith,by linarith⟩⟩

theorem standardClosedTriangle_interior : interior standardClosedTriangle = standardOpenTriangle := by
  have hfst : interior {p : ℝ × ℝ | 0 ≤ p.1} = {p | 0 < p.1} := by
    change interior ((ContinuousLinearMap.fst ℝ ℝ ℝ) ⁻¹' Ici 0) =
      (ContinuousLinearMap.fst ℝ ℝ ℝ) ⁻¹' Ioi 0
    rw [(ContinuousLinearMap.fst ℝ ℝ ℝ).interior_preimage (by intro x; exact ⟨(x,0),rfl⟩),interior_Ici]
  have hsnd : interior {p : ℝ × ℝ | 0 ≤ p.2} = {p | 0 < p.2} := by
    change interior ((ContinuousLinearMap.snd ℝ ℝ ℝ) ⁻¹' Ici 0) =
      (ContinuousLinearMap.snd ℝ ℝ ℝ) ⁻¹' Ioi 0
    rw [(ContinuousLinearMap.snd ℝ ℝ ℝ).interior_preimage (by intro x; exact ⟨(0,x),rfl⟩),interior_Ici]
  let f : (ℝ × ℝ) →L[ℝ] ℝ := ContinuousLinearMap.fst ℝ ℝ ℝ + ContinuousLinearMap.snd ℝ ℝ ℝ
  have hsum : interior {p : ℝ × ℝ | p.1 + p.2 ≤ 1} = {p | p.1 + p.2 < 1} := by
    change interior (f ⁻¹' Iic 1) = f ⁻¹' Iio 1
    rw [f.interior_preimage (by intro x; exact ⟨(x,0),add_zero x⟩),interior_Iic]
  rw [standardClosedTriangle_eq_cuts,interior_inter,interior_inter,hfst,hsnd,hsum]
  rfl

theorem standardOpenTriangle_closure : closure standardOpenTriangle = standardClosedTriangle := by
  rw [← standardClosedTriangle_interior]
  rw [standardClosedTriangle_convex.closure_interior_eq_closure_of_nonempty_interior]
  · exact standardClosedTriangle_isClosed.closure_eq
  · rw [standardClosedTriangle_interior]
    exact ⟨(1/3,1/3),by norm_num [standardOpenTriangle]⟩

theorem standardOpenTriangle_isOpen : IsOpen standardOpenTriangle := by
  rw [← standardClosedTriangle_interior]
  exact isOpen_interior


theorem standard_first_axis_segment :
    segment ℝ ((0,0) : ℝ × ℝ) (1,0) =
      {p : ℝ × ℝ | 0 ≤ p.1 ∧ p.1 ≤ 1 ∧ p.2 = 0} := by
  ext p
  constructor
  · rintro ⟨a,b,ha,hb,hab,hp⟩
    have he : p = (b,0) := by rw [← hp]; ext <;> simp
    rw [he]
    exact ⟨hb,by linarith,rfl⟩
  · intro hp
    change 0 ≤ p.1 ∧ p.1 ≤ 1 ∧ p.2 = 0 at hp
    refine ⟨1-p.1,p.1,by linarith,hp.1,by ring,?_⟩
    ext <;> simp [hp.2.2]

theorem standard_second_axis_segment :
    segment ℝ ((0,0) : ℝ × ℝ) (0,1) =
      {p : ℝ × ℝ | p.1 = 0 ∧ 0 ≤ p.2 ∧ p.2 ≤ 1} := by
  ext p
  constructor
  · rintro ⟨a,b,ha,hb,hab,hp⟩
    have he : p = (0,b) := by rw [← hp]; ext <;> simp
    rw [he]
    exact ⟨rfl,hb,by linarith⟩
  · intro hp
    change p.1 = 0 ∧ 0 ≤ p.2 ∧ p.2 ≤ 1 at hp
    refine ⟨1-p.2,p.2,by linarith,hp.2.1,by ring,?_⟩
    ext <;> simp [hp.1]

theorem standardClosedTriangle_frontier : frontier standardClosedTriangle =
    segment ℝ ((1,0) : ℝ × ℝ) (0,1) ∪ segment ℝ (0,1) (0,0) ∪ segment ℝ (0,0) (1,0) := by
  rw [frontier,standardClosedTriangle_isClosed.closure_eq,standardClosedTriangle_interior,
    standard_opposite_segment,segment_symm ℝ ((0,1) : ℝ × ℝ) (0,0),
    standard_second_axis_segment,standard_first_axis_segment]
  ext p
  simp only [standardClosedTriangle,standardOpenTriangle,mem_sdiff,mem_ofPred,mem_union]
  constructor
  · rintro ⟨⟨hu,hv,hs⟩,hn⟩
    by_cases hu0 : p.1 = 0
    · exact Or.inl (Or.inr ⟨hu0,hv,by linarith⟩)
    by_cases hv0 : p.2 = 0
    · exact Or.inr ⟨hu,by linarith,hv0⟩
    exact Or.inl (Or.inl ⟨hu,hv,le_antisymm hs
      (not_lt.mp (fun hlt => hn ⟨lt_of_le_of_ne hu (Ne.symm hu0),
        lt_of_le_of_ne hv (Ne.symm hv0),hlt⟩))⟩)
  · intro hp
    rcases hp with (⟨hu,hv,hs⟩ | ⟨hu,hv,hs⟩) | ⟨hu,hv,hs⟩
    · exact ⟨⟨hu,hv,hs.le⟩,fun hh => (ne_of_lt hh.2.2) hs⟩
    · exact ⟨⟨by linarith,hv,by linarith⟩,fun hh => (ne_of_gt hh.1) hu⟩
    · exact ⟨⟨hu,by linarith,by linarith⟩,fun hh => (ne_of_gt hh.2.1) hs⟩

theorem HTriangle.closure_coordinate_preimage (T : HTriangle) :
    closure T.interior = T.coordinate ⁻¹' standardClosedTriangle := by
  rw [T.coordinate_isOpenEmbedding.isEmbedding.closure_eq_preimage_closure_image,
    T.coordinate_image_interior,standardOpenTriangle_closure]

theorem HTriangle.coordinate_image_closure (T : HTriangle) :
    T.coordinate '' closure T.interior = standardClosedTriangle := by
  rw [T.closure_coordinate_preimage]
  apply image_preimage_eq_of_subset
  rw [T.coordinate_range]
  exact T.standardClosedTriangle_subset_domain

theorem HTriangle.closure_isCompact (T : HTriangle) : IsCompact (closure T.interior) := by
  apply T.coordinate_isOpenEmbedding.isEmbedding.isCompact_iff.mpr
  rw [T.coordinate_image_closure]
  exact standardClosedTriangle_isCompact

theorem HTriangle.coordinate_image_frontier (T : HTriangle) :
    T.coordinate '' frontier T.interior = frontier standardClosedTriangle := by
  rw [frontier,T.interior_isOpen.interior_eq,
    image_sdiff T.coordinate_isOpenEmbedding.injective,
    T.coordinate_image_closure,T.coordinate_image_interior,
    frontier,standardClosedTriangle_isClosed.closure_eq,standardClosedTriangle_interior]

theorem HTriangle.frontier_eq_sides (T : HTriangle) :
    frontier T.interior = T.sideA ∪ T.sideB ∪ T.sideC := by
  apply T.coordinate_isOpenEmbedding.injective.image_injective
  rw [T.coordinate_image_frontier,standardClosedTriangle_frontier,image_union,image_union]
  change _ = T.coordinate '' closedHSegment T.b T.c ∪
    T.coordinate '' closedHSegment T.c T.a ∪ T.coordinate '' closedHSegment T.a T.b
  rw [T.coordinate_image_closedHSegment,T.coordinate_image_closedHSegment,
    T.coordinate_image_closedHSegment,T.coordinate_a,T.coordinate_b,T.coordinate_c]


theorem HTriangle.boundary_circle_homeomorph (T : HTriangle) :
    Nonempty (frontier T.interior ≃ₜ Metric.sphere (0 : ℝ × ℝ) 1) := by
  obtain ⟨h,_,_,hf⟩ := exists_homeomorph_image_interior_closure_frontier_eq_unitBall
    standardClosedTriangle_convex
    (by rw [standardClosedTriangle_interior]; exact ⟨(1/3,1/3),by norm_num [standardOpenTriangle]⟩)
    standardClosedTriangle_isCompact.isBounded
  exact ⟨(T.coordinate_isOpenEmbedding.isEmbedding.homeomorphImage (frontier T.interior)).trans
    ((Homeomorph.setCongr T.coordinate_image_frontier).trans
      ((h.isEmbedding.homeomorphImage (frontier standardClosedTriangle)).trans (Homeomorph.setCongr hf)))⟩

theorem HTriangle.exists_jordan_curve (T : HTriangle) :
    ∃ γ : Metric.sphere (0 : ℝ × ℝ) 1 → ℍ, Continuous γ ∧ Function.Injective γ ∧
      range γ = T.sideA ∪ T.sideB ∪ T.sideC := by
  obtain ⟨h⟩ := T.boundary_circle_homeomorph
  let γ : Metric.sphere (0 : ℝ × ℝ) 1 → ℍ := fun p => (h.symm p).val
  refine ⟨γ,continuous_subtype_val.comp h.symm.continuous,?_,?_⟩
  · intro p q he
    apply h.symm.injective
    exact Subtype.ext he
  · rw [← T.frontier_eq_sides]
    ext x
    constructor
    · rintro ⟨p,rfl⟩
      exact (h.symm p).property
    · intro hx
      refine ⟨h ⟨x,hx⟩,?_⟩
      change (h.symm (h ⟨x,hx⟩)).val = x
      rw [h.symm_apply_apply]

theorem connectedComponentIn_compl_frontier_of_isOpen_preconnected
    {X : Type*} [TopologicalSpace X] {S : Set X} (ho : IsOpen S)
    (hc : IsPreconnected S) {x : X} (hx : x ∈ S) :
    connectedComponentIn (frontier S)ᶜ x = S := by
  have hsub : S ⊆ (frontier S)ᶜ := by
    intro y hy hF
    exact hF.2 (ho.interior_eq.symm ▸ hy)
  apply subset_antisymm
  · have hC := isPreconnected_connectedComponentIn (F := (frontier S)ᶜ) (x := x)
    apply hC.subset_left_of_subset_union ho isClosed_closure.isOpen_compl
      (disjoint_compl_right.mono_right (compl_subset_compl.mpr subset_closure))
    · intro y hy
      have hyF := connectedComponentIn_subset _ _ hy
      by_cases hyS : y ∈ S
      · exact Or.inl hyS
      · exact Or.inr (fun hyC => hyF ⟨hyC,ho.interior_eq.symm ▸ hyS⟩)
    · exact ⟨x,mem_connectedComponentIn (hsub hx),hx⟩
  · exact hc.subset_connectedComponentIn hx hsub

theorem HTriangle.interior_eq_bounded_component (T : HTriangle) {x : ℍ} (hx : x ∈ T.interior) :
    connectedComponentIn (T.sideA ∪ T.sideB ∪ T.sideC)ᶜ x = T.interior ∧
      Bornology.IsBounded T.interior := by
  constructor
  · rw [← T.frontier_eq_sides]
    exact connectedComponentIn_compl_frontier_of_isOpen_preconnected
      T.interior_isOpen T.interior_isPreconnected hx
  · exact T.closure_isCompact.isBounded.subset subset_closure


theorem convexDomain_sdiff_standardClosedTriangle_isPreconnected {D : Set (ℝ × ℝ)}
    (hc : Convex ℝ D) (ho : IsOpen D) (h0 : (0,0) ∈ D) (h2 : (0,1) ∈ D) :
    IsPreconnected (D \ standardClosedTriangle) := by
  let A := D ∩ {p : ℝ × ℝ | p.1 < 0}
  let B := D ∩ {p : ℝ × ℝ | p.2 < 0}
  let C := D ∩ {p : ℝ × ℝ | 1 < p.1 + p.2}
  have hA : IsPreconnected A := (hc.inter
    (convex_halfSpace_lt (ContinuousLinearMap.fst ℝ ℝ ℝ).toLinearMap.isLinear (0 : ℝ))).isPreconnected
  have hB : IsPreconnected B := (hc.inter
    (convex_halfSpace_lt (ContinuousLinearMap.snd ℝ ℝ ℝ).toLinearMap.isLinear (0 : ℝ))).isPreconnected
  have hC : IsPreconnected C := (hc.inter (convex_halfSpace_gt
    (ContinuousLinearMap.fst ℝ ℝ ℝ + ContinuousLinearMap.snd ℝ ℝ ℝ).toLinearMap.isLinear (1 : ℝ))).isPreconnected
  have hz : ∀ᶠ t : ℝ in 𝓝 0, (-t,-t) ∈ D :=
    (continuous_neg.prodMk continuous_neg).tendsto 0 (by simpa using ho.mem_nhds h0)
  have hz' := hz.filter_mono (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
  obtain ⟨t,hDt,ht⟩ := (hz'.and self_mem_nhdsWithin).exists
  have hc2 : ∀ᶠ t : ℝ in 𝓝 0, (-t,1 + 2*t) ∈ D :=
    (continuous_neg.prodMk (continuous_const.add (continuous_const.mul continuous_id))).tendsto 0
      (by simpa using ho.mem_nhds h2)
  have hc2' := hc2.filter_mono (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
  obtain ⟨s,hDs,hs⟩ := (hc2'.and self_mem_nhdsWithin).exists
  have hAB : IsPreconnected (A ∪ B) := hA.union'
    ⟨(-t,-t),⟨hDt,by change -t < 0; linarith⟩,⟨hDt,by change -t < 0; linarith⟩⟩ hB
  have hABC : IsPreconnected (A ∪ B ∪ C) := hAB.union'
    ⟨(-s,1+2*s),Or.inl ⟨hDs,by change -s < 0; linarith⟩,
      ⟨hDs,by change 1 < -s + (1+2*s); linarith⟩⟩ hC
  have he : D \ standardClosedTriangle = A ∪ B ∪ C := by
    ext p
    simp only [A,B,C,standardClosedTriangle,mem_sdiff,mem_inter_iff,mem_ofPred,
      mem_union,not_and_or,not_le]
    tauto
  rw [he]
  exact hABC

theorem HTriangle.exterior_isPreconnected (T : HTriangle) : IsPreconnected (closure T.interior)ᶜ := by
  apply T.coordinate_isOpenEmbedding.isEmbedding.isInducing.isPreconnected_image.mp
  rw [image_compl_eq_range_sdiff_image T.coordinate_isOpenEmbedding.injective,
    T.coordinate_range,T.coordinate_image_closure]
  apply convexDomain_sdiff_standardClosedTriangle_isPreconnected
    T.coordinateDomain_convex T.coordinateDomain_isOpen
  · rw [← T.coordinate_range,← T.coordinate_a]
    exact mem_range_self T.a
  · rw [← T.coordinate_range,← T.coordinate_c]
    exact mem_range_self T.c


theorem DiscTriangle.closure_eq_cayley (T : DiscTriangle) :
    closure T.interior = halfPlaneToDisc '' closure T.toHalfPlane.interior := by
  rw [T.interior_eq_cayley]
  exact (cayleyHomeomorph.image_closure _).symm

theorem DiscTriangle.frontier_eq_cayley (T : DiscTriangle) :
    frontier T.interior = halfPlaneToDisc '' frontier T.toHalfPlane.interior := by
  rw [T.interior_eq_cayley]
  exact (cayleyHomeomorph.image_frontier _).symm

theorem DiscTriangle.closure_isCompact (T : DiscTriangle) : IsCompact (closure T.interior) := by
  rw [T.closure_eq_cayley]
  exact T.toHalfPlane.closure_isCompact.image continuous_halfPlaneToDisc

theorem DiscTriangle.frontier_eq_sides (T : DiscTriangle) :
    frontier T.interior = T.sideA ∪ T.sideB ∪ T.sideC := by
  rw [T.frontier_eq_cayley,T.toHalfPlane.frontier_eq_sides,image_union,image_union]
  change halfPlaneToDisc '' closedHSegment (discToHalfPlane T.b) (discToHalfPlane T.c) ∪
    halfPlaneToDisc '' closedHSegment (discToHalfPlane T.c) (discToHalfPlane T.a) ∪
    halfPlaneToDisc '' closedHSegment (discToHalfPlane T.a) (discToHalfPlane T.b) = _
  rw [← closedDiscHSegment_eq_cayley_image,← closedDiscHSegment_eq_cayley_image,
    ← closedDiscHSegment_eq_cayley_image]
  rfl

theorem DiscTriangle.interior_isPreconnected (T : DiscTriangle) : IsPreconnected T.interior :=
  T.interior_discHConvex.isPreconnected

theorem DiscTriangle.exterior_isPreconnected (T : DiscTriangle) :
    IsPreconnected (closure T.interior)ᶜ := by
  have he : halfPlaneToDisc '' (closure T.toHalfPlane.interior)ᶜ =
      (halfPlaneToDisc '' closure T.toHalfPlane.interior)ᶜ := cayleyHomeomorph.image_compl _
  rw [T.closure_eq_cayley,← he]
  exact T.toHalfPlane.exterior_isPreconnected.image _ continuous_halfPlaneToDisc.continuousOn

theorem DiscTriangle.exists_jordan_curve (T : DiscTriangle) :
    ∃ γ : Metric.sphere (0 : ℝ × ℝ) 1 → 𝔻, Continuous γ ∧ Function.Injective γ ∧
      range γ = T.sideA ∪ T.sideB ∪ T.sideC := by
  obtain ⟨γ,hγc,hγi,hγr⟩ := T.toHalfPlane.exists_jordan_curve
  refine ⟨halfPlaneToDisc ∘ γ,continuous_halfPlaneToDisc.comp hγc,
    cayleyHomeomorph.injective.comp hγi,?_⟩
  rw [range_comp,hγr,← T.toHalfPlane.frontier_eq_sides,← T.frontier_eq_cayley,T.frontier_eq_sides]

theorem continuous_image_closure_eq_of_isCompactClosure
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y]
    {f : X → Y} (hf : Continuous f) {S : Set X} (hc : IsCompact (closure S)) :
    f '' closure S = closure (f '' S) :=
  subset_antisymm (image_closure_subset_closure_image hf)
    (closure_minimal (image_mono subset_closure) (hc.image hf).isClosed)

theorem openEmbedding_image_frontier_eq_of_isCompactClosure
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y]
    {f : X → Y} (hf : Topology.IsOpenEmbedding f) {S : Set X}
    (ho : IsOpen S) (hc : IsCompact (closure S)) : f '' frontier S = frontier (f '' S) := by
  rw [frontier,ho.interior_eq,image_sdiff hf.injective,
    continuous_image_closure_eq_of_isCompactClosure hf.continuous hc,
    frontier,(hf.isOpenMap _ ho).interior_eq]

def HTriangle.complexInterior (T : HTriangle) : Set ℂ := ((↑) : ℍ → ℂ) '' T.interior

def DiscTriangle.complexInterior (T : DiscTriangle) : Set ℂ := ((↑) : 𝔻 → ℂ) '' T.interior

theorem HTriangle.complexInterior_isOpen (T : HTriangle) : IsOpen T.complexInterior :=
  UpperHalfPlane.isOpenEmbedding_coe.isOpenMap _ T.interior_isOpen

theorem DiscTriangle.complexInterior_isOpen (T : DiscTriangle) : IsOpen T.complexInterior :=
  disc_isOpenEmbedding_coe.isOpenMap _ T.interior_isOpen

theorem HTriangle.complexInterior_closure (T : HTriangle) :
    closure T.complexInterior = ((↑) : ℍ → ℂ) '' closure T.interior :=
  (continuous_image_closure_eq_of_isCompactClosure UpperHalfPlane.continuous_coe T.closure_isCompact).symm

theorem DiscTriangle.complexInterior_closure (T : DiscTriangle) :
    closure T.complexInterior = ((↑) : 𝔻 → ℂ) '' closure T.interior :=
  (continuous_image_closure_eq_of_isCompactClosure disc_isOpenEmbedding_coe.continuous T.closure_isCompact).symm

theorem HTriangle.complexInterior_closure_isCompact (T : HTriangle) :
    IsCompact (closure T.complexInterior) := by
  rw [T.complexInterior_closure]
  exact T.closure_isCompact.image UpperHalfPlane.continuous_coe

theorem DiscTriangle.complexInterior_closure_isCompact (T : DiscTriangle) :
    IsCompact (closure T.complexInterior) := by
  rw [T.complexInterior_closure]
  exact T.closure_isCompact.image disc_isOpenEmbedding_coe.continuous

theorem HTriangle.complexInterior_isPreconnected (T : HTriangle) :
    IsPreconnected T.complexInterior :=
  T.interior_isPreconnected.image _ UpperHalfPlane.continuous_coe.continuousOn

theorem DiscTriangle.complexInterior_isPreconnected (T : DiscTriangle) :
    IsPreconnected T.complexInterior :=
  T.interior_isPreconnected.image _ disc_isOpenEmbedding_coe.continuous.continuousOn

theorem HTriangle.complexInterior_frontier (T : HTriangle) :
    frontier T.complexInterior = ((↑) : ℍ → ℂ) '' (T.sideA ∪ T.sideB ∪ T.sideC) := by
  rw [← T.frontier_eq_sides]
  exact (openEmbedding_image_frontier_eq_of_isCompactClosure
    UpperHalfPlane.isOpenEmbedding_coe T.interior_isOpen T.closure_isCompact).symm

theorem DiscTriangle.complexInterior_frontier (T : DiscTriangle) :
    frontier T.complexInterior = ((↑) : 𝔻 → ℂ) '' (T.sideA ∪ T.sideB ∪ T.sideC) := by
  rw [← T.frontier_eq_sides]
  exact (openEmbedding_image_frontier_eq_of_isCompactClosure
    disc_isOpenEmbedding_coe T.interior_isOpen T.closure_isCompact).symm


theorem HTriangle.complexExterior_isPreconnected (T : HTriangle) :
    IsPreconnected (closure T.complexInterior)ᶜ := by
  obtain ⟨p,_,hmin⟩ := T.closure_isCompact.exists_isMinOn
    (T.interior_nonempty.mono subset_closure) UpperHalfPlane.continuous_im.continuousOn
  let A : Set ℂ := ((↑) : ℍ → ℂ) '' (closure T.interior)ᶜ
  let B : Set ℂ := {z | z.im < p.im}
  have hA : IsPreconnected A :=
    T.exterior_isPreconnected.image _ UpperHalfPlane.continuous_coe.continuousOn
  have hB : IsPreconnected B :=
    (convex_halfSpace_lt Complex.imCLM.toLinearMap.isLinear p.im).isPreconnected
  let w : ℍ := UpperHalfPlane.mk (⟨0,p.im/2⟩ : ℂ) (half_pos p.im_pos)
  have hw : w ∉ closure T.interior := by
    intro hw
    have hm := hmin hw
    change p.im ≤ p.im / 2 at hm
    linarith [p.im_pos]
  have hinter : (A ∩ B).Nonempty :=
    ⟨(w : ℂ),⟨w,hw,rfl⟩,by change p.im / 2 < p.im; linarith [p.im_pos]⟩
  have he : (closure T.complexInterior)ᶜ = A ∪ B := by
    rw [T.complexInterior_closure]
    ext z
    constructor
    · intro hz
      by_cases hzi : 0 < z.im
      · exact Or.inl ⟨UpperHalfPlane.mk z hzi,fun hh => hz ⟨_,hh,rfl⟩,rfl⟩
      · exact Or.inr (by change z.im < p.im; linarith [p.im_pos])
    · rintro (⟨v,hv,rfl⟩ | hz)
      · rintro ⟨u,hu,he⟩
        exact hv ((UpperHalfPlane.coe_injective he) ▸ hu)
      · rintro ⟨u,hu,rfl⟩
        exact (not_lt_of_ge (hmin hu)) hz
  rw [he]
  exact hA.union' hinter hB

theorem complex_outer_region_isPreconnected {r : ℝ} (hr : 0 ≤ r) :
    IsPreconnected {z : ℂ | r < ‖z‖} := by
  have hs : IsPreconnected (Metric.sphere (0 : ℂ) 1) :=
    isPreconnected_sphere (by rw [Complex.rank_real_complex]; norm_num) 0 1
  have hc := (hs.prod (isPreconnected_Ioi (a := r))).image
    (fun p : ℂ × ℝ => p.2 • p.1) (continuous_snd.smul continuous_fst).continuousOn
  have he : (fun p : ℂ × ℝ => p.2 • p.1) ''
      (Metric.sphere (0 : ℂ) 1 ×ˢ Ioi r) = {z : ℂ | r < ‖z‖} := by
    ext z
    constructor
    · rintro ⟨⟨u,t⟩,⟨hu,ht⟩,rfl⟩
      have hu1 : ‖u‖ = 1 := by simpa only [Metric.mem_sphere,dist_zero_right] using hu
      change r < ‖t • u‖
      rw [norm_smul,Real.norm_of_nonneg (le_trans hr ht.le),hu1,mul_one]
      exact ht
    · intro hz
      have hn : 0 < ‖z‖ := lt_of_le_of_lt hr hz
      refine ⟨(‖z‖⁻¹ • z,‖z‖),⟨?_,hz⟩,?_⟩
      · change dist (‖z‖⁻¹ • z) 0 = 1
        rw [dist_zero_right,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hn.le),
          inv_mul_cancel₀ (ne_of_gt hn)]
      · change ‖z‖ • (‖z‖⁻¹ • z) = z
        rw [smul_smul,mul_inv_cancel₀ (ne_of_gt hn),one_smul]
  rw [he] at hc
  exact hc


theorem DiscTriangle.complexExterior_isPreconnected (T : DiscTriangle) :
    IsPreconnected (closure T.complexInterior)ᶜ := by
  obtain ⟨p,_,hmax⟩ := T.closure_isCompact.exists_isMaxOn
    (T.interior_nonempty.mono subset_closure) (continuous_norm.comp disc_isOpenEmbedding_coe.continuous).continuousOn
  let r := (‖(p : ℂ)‖ + 1) / 2
  have hr0 : 0 < r := by dsimp [r]; linarith [norm_nonneg (p : ℂ)]
  have hpr : ‖(p : ℂ)‖ < r := by dsimp [r]; linarith [p.norm_lt_one]
  have hr1 : r < 1 := by dsimp [r]; linarith [p.norm_lt_one]
  let A : Set ℂ := ((↑) : 𝔻 → ℂ) '' (closure T.interior)ᶜ
  let B : Set ℂ := {z | r < ‖z‖}
  have hA : IsPreconnected A :=
    T.exterior_isPreconnected.image _ disc_isOpenEmbedding_coe.continuous.continuousOn
  have hB : IsPreconnected B := complex_outer_region_isPreconnected hr0.le
  let s := (r + 1) / 2
  have hs0 : 0 < s := by dsimp [s]; linarith
  have hrs : r < s := by dsimp [s]; linarith
  have hs1 : s < 1 := by dsimp [s]; linarith
  let w : 𝔻 := Complex.UnitDisc.mk (s : ℂ)
    (by simpa only [Complex.norm_real,Real.norm_eq_abs,abs_of_pos hs0] using hs1)
  have hwn : ‖(w : ℂ)‖ = s := by
    change ‖(s : ℂ)‖ = s
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos hs0]
  have hw : w ∉ closure T.interior := by
    intro hw
    have hm := hmax hw
    change ‖(w : ℂ)‖ ≤ ‖(p : ℂ)‖ at hm
    rw [hwn] at hm
    linarith
  have hinter : (A ∩ B).Nonempty :=
    ⟨(w : ℂ),⟨w,hw,rfl⟩,by change r < ‖(w : ℂ)‖; rwa [hwn]⟩
  have he : (closure T.complexInterior)ᶜ = A ∪ B := by
    rw [T.complexInterior_closure]
    ext z
    constructor
    · intro hz
      by_cases hzn : ‖z‖ < 1
      · exact Or.inl ⟨Complex.UnitDisc.mk z hzn,fun hh => hz ⟨_,hh,rfl⟩,rfl⟩
      · exact Or.inr (by change r < ‖z‖; linarith)
    · rintro (⟨v,hv,rfl⟩ | hz)
      · rintro ⟨u,hu,he⟩
        exact hv ((disc_isOpenEmbedding_coe.injective he) ▸ hu)
      · rintro ⟨u,hu,rfl⟩
        have hm := hmax hu
        change ‖(u : ℂ)‖ ≤ ‖(p : ℂ)‖ at hm
        change r < ‖(u : ℂ)‖ at hz
        linarith
  rw [he]
  exact hA.union' hinter hB


theorem connectedComponentIn_compl_frontier_of_mem_exterior
    {X : Type*} [TopologicalSpace X] {S : Set X} (ho : IsOpen S)
    (hc : IsPreconnected (closure S)ᶜ) {x : X} (hx : x ∉ closure S) :
    connectedComponentIn (frontier S)ᶜ x = (closure S)ᶜ := by
  have hsub : (closure S)ᶜ ⊆ (frontier S)ᶜ := fun _ hy hF => hy hF.1
  apply subset_antisymm
  · have hC := isPreconnected_connectedComponentIn (F := (frontier S)ᶜ) (x := x)
    apply hC.subset_left_of_subset_union isClosed_closure.isOpen_compl ho
      (disjoint_compl_left.mono_right subset_closure)
    · intro y hy
      have hyF := connectedComponentIn_subset _ _ hy
      by_cases hyS : y ∈ S
      · exact Or.inr hyS
      · exact Or.inl (fun hyC => hyF ⟨hyC,ho.interior_eq.symm ▸ hyS⟩)
    · exact ⟨x,mem_connectedComponentIn (hsub hx),hx⟩
  · exact hc.subset_connectedComponentIn hx hsub

theorem complex_bounded_component_iff_mem {S : Set ℂ} (ho : IsOpen S)
    (hi : IsPreconnected S) (he : IsPreconnected (closure S)ᶜ) (hk : IsCompact (closure S))
    {x : ℂ} (hx : x ∉ frontier S) :
    Bornology.IsBounded (connectedComponentIn (frontier S)ᶜ x) ↔ x ∈ S := by
  by_cases hxS : x ∈ S
  · rw [connectedComponentIn_compl_frontier_of_isOpen_preconnected ho hi hxS]
    exact ⟨fun _ => hxS,fun _ => hk.isBounded.subset subset_closure⟩
  · have hxE : x ∉ closure S := fun hxC => hx ⟨hxC,ho.interior_eq.symm ▸ hxS⟩
    rw [connectedComponentIn_compl_frontier_of_mem_exterior ho he hxE]
    constructor
    · intro hb
      exfalso
      apply NormedSpace.unbounded_univ ℝ ℂ
      simpa only [union_compl_self] using hk.isBounded.union hb
    · intro hs
      exact (hxS hs).elim

theorem HTriangle.complex_bounded_component_iff_mem (T : HTriangle) {x : ℂ}
    (hx : x ∉ frontier T.complexInterior) :
    Bornology.IsBounded (connectedComponentIn (frontier T.complexInterior)ᶜ x) ↔
      x ∈ T.complexInterior :=
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.complex_bounded_component_iff_mem T.complexInterior_isOpen T.complexInterior_isPreconnected
    T.complexExterior_isPreconnected T.complexInterior_closure_isCompact hx

theorem DiscTriangle.complex_bounded_component_iff_mem (T : DiscTriangle) {x : ℂ}
    (hx : x ∉ frontier T.complexInterior) :
    Bornology.IsBounded (connectedComponentIn (frontier T.complexInterior)ᶜ x) ↔
      x ∈ T.complexInterior :=
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.complex_bounded_component_iff_mem T.complexInterior_isOpen T.complexInterior_isPreconnected
    T.complexExterior_isPreconnected T.complexInterior_closure_isCompact hx

theorem HTriangle.complex_exists_jordan_curve (T : HTriangle) :
    ∃ γ : Metric.sphere (0 : ℝ × ℝ) 1 → ℂ, Continuous γ ∧ Function.Injective γ ∧
      range γ = frontier T.complexInterior := by
  obtain ⟨γ,hγc,hγi,hγr⟩ := T.exists_jordan_curve
  refine ⟨((↑) : ℍ → ℂ) ∘ γ,UpperHalfPlane.continuous_coe.comp hγc,
    UpperHalfPlane.isEmbedding_coe.injective.comp hγi,?_⟩
  rw [range_comp,hγr,T.complexInterior_frontier]

theorem DiscTriangle.complex_exists_jordan_curve (T : DiscTriangle) :
    ∃ γ : Metric.sphere (0 : ℝ × ℝ) 1 → ℂ, Continuous γ ∧ Function.Injective γ ∧
      range γ = frontier T.complexInterior := by
  obtain ⟨γ,hγc,hγi,hγr⟩ := T.exists_jordan_curve
  refine ⟨((↑) : 𝔻 → ℂ) ∘ γ,disc_isOpenEmbedding_coe.continuous.comp hγc,
    disc_isOpenEmbedding_coe.injective.comp hγi,?_⟩
  rw [range_comp,hγr,T.complexInterior_frontier]


/-- The three actual sides form a Jordan curve whose unique bounded component is precisely
this genuine source triangle, viewed in the ordinary complex plane. -/
theorem HTriangle.jordan_interior (T : HTriangle) :
    ∃ γ : Metric.sphere (0 : ℝ × ℝ) 1 → ℂ, Continuous γ ∧ Function.Injective γ ∧
      range γ = ((↑) : ℍ → ℂ) '' (T.sideA ∪ T.sideB ∪ T.sideC) ∧
      IsConnected T.complexInterior ∧ Bornology.IsBounded T.complexInterior ∧
      ∀ x ∉ range γ, Bornology.IsBounded (connectedComponentIn (range γ)ᶜ x) ↔ x ∈ T.complexInterior := by
  obtain ⟨γ,hγc,hγi,hγr⟩ := T.complex_exists_jordan_curve
  refine ⟨γ,hγc,hγi,hγr.trans T.complexInterior_frontier,
    ⟨T.interior_nonempty.image _,T.complexInterior_isPreconnected⟩,
    T.complexInterior_closure_isCompact.isBounded.subset subset_closure,?_⟩
  intro x hx
  rw [hγr] at hx ⊢
  exact T.complex_bounded_component_iff_mem hx

/-- The same actual Jordan-interior statement for the native disc model. -/
theorem DiscTriangle.jordan_interior (T : DiscTriangle) :
    ∃ γ : Metric.sphere (0 : ℝ × ℝ) 1 → ℂ, Continuous γ ∧ Function.Injective γ ∧
      range γ = ((↑) : 𝔻 → ℂ) '' (T.sideA ∪ T.sideB ∪ T.sideC) ∧
      IsConnected T.complexInterior ∧ Bornology.IsBounded T.complexInterior ∧
      ∀ x ∉ range γ, Bornology.IsBounded (connectedComponentIn (range γ)ᶜ x) ↔ x ∈ T.complexInterior := by
  obtain ⟨γ,hγc,hγi,hγr⟩ := T.complex_exists_jordan_curve
  refine ⟨γ,hγc,hγi,hγr.trans T.complexInterior_frontier,
    ⟨T.interior_nonempty.image _,T.complexInterior_isPreconnected⟩,
    T.complexInterior_closure_isCompact.isBounded.subset subset_closure,?_⟩
  intro x hx
  rw [hγr] at hx ⊢
  exact T.complex_bounded_component_iff_mem hx

end
end LowDimensionalTopology.Geometry.Hyperbolic
