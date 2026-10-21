/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Hyperbolic.Convexity.IdealHull.NielsenGapIntersection
public import LowDimensionalTopology.Geometry.Fuchsian.Nielsen.NielsenIdealHull
@[expose] public section
open Set
open scoped Topology OnePoint Complex.UnitDisc UpperHalfPlane RealInnerProductSpace
namespace LowDimensionalTopology.Geometry.Hyperbolic
open LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Surfaces LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.Euclidean
noncomputable section

/-- The actual finite real chart in the half-plane's genuine ideal circle. -/
def nielsenRealBoundaryPoint (x : ℝ) : OnePoint ℂ:=((x : ℂ) : OnePoint ℂ)

theorem nielsenRealBoundaryPoint_isEmbedding : Topology.IsEmbedding nielsenRealBoundaryPoint :=
  OnePoint.isOpenEmbedding_coe.isEmbedding.comp Complex.isometry_ofReal.isEmbedding

def nielsenHalfPlaneRealSet (Λ : Set (OnePoint ℂ)) : Set ℝ:=nielsenRealBoundaryPoint ⁻¹' Λ

theorem nielsenHalfPlaneRealSet_isClosed (Λ : Set (OnePoint ℂ)) (hΛ : IsClosed Λ) :
    IsClosed (nielsenHalfPlaneRealSet Λ) :=
  hΛ.preimage nielsenRealBoundaryPoint_isEmbedding.continuous

theorem nielsen_halfPlane_set_representation (Λ : Set (OnePoint ℂ))
    (hΛ : Λ⊆halfPlaneIdealBoundary) (hinf : (∞ : OnePoint ℂ)∈Λ) :
    insert ∞ (nielsenRealBoundaryPoint '' nielsenHalfPlaneRealSet Λ)=Λ := by
  ext p
  constructor
  · rintro (rfl|⟨x,hx,rfl⟩)
    · exact hinf
    · exact hx
  · intro hp
    induction p using OnePoint.rec with
    | infty => exact mem_insert _ _
    | coe z =>
      have him : z.im=0:=(coe_mem_halfPlaneIdealBoundary z).mp (hΛ hp)
      have he : (z.re : ℂ)=z:=by apply Complex.ext <;> simp [him]
      right
      exact ⟨z.re,by change ((z.re : ℂ) : OnePoint ℂ)∈Λ;rw [he];exact hp,by change ((z.re : ℂ) : OnePoint ℂ)=(z : OnePoint ℂ);rw [he]⟩

theorem nielsen_halfPlane_ordinary_representation (Λ : Set (OnePoint ℂ))
    (hinf : (∞ : OnePoint ℂ)∈Λ) :
    nielsenRealBoundaryPoint '' (nielsenHalfPlaneRealSet Λ)ᶜ=halfPlaneIdealBoundary\Λ := by
  ext p
  constructor
  · rintro ⟨x,hx,rfl⟩
    exact ⟨(coe_mem_halfPlaneIdealBoundary _).mpr (by simp),hx⟩
  · rintro ⟨hp,hnot⟩
    induction p using OnePoint.rec with
    | infty => exact (hnot hinf).elim
    | coe z =>
      have him : z.im=0:=(coe_mem_halfPlaneIdealBoundary z).mp hp
      have he : (z.re : ℂ)=z:=by apply Complex.ext <;> simp [him]
      exact ⟨z.re,by change ((z.re : ℂ) : OnePoint ℂ)∉Λ;rw [he];exact hnot,by change ((z.re : ℂ) : OnePoint ℂ)=(z : OnePoint ℂ);rw [he]⟩

theorem nielsenHalfPlaneRealSet_infinite (Λ : Set (OnePoint ℂ)) (hi : Λ.Infinite)
    (hΛ : Λ⊆halfPlaneIdealBoundary) (hinf : (∞ : OnePoint ℂ)∈Λ) :
    (nielsenHalfPlaneRealSet Λ).Infinite := by
  by_contra hf
  have hh : (insert (∞ : OnePoint ℂ) (nielsenRealBoundaryPoint '' nielsenHalfPlaneRealSet Λ)).Finite:=
    (not_infinite.mp hf).image _ |>.insert _
  rw [nielsen_halfPlane_set_representation Λ hΛ hinf] at hh
  exact hi hh

/-- Actual maximal complementary arcs on the genuine compactified ideal boundary. -/
def nielsenHalfPlaneArcFamily (Λ : Set (OnePoint ℂ)) : Set (Set (OnePoint ℂ)):=
  {J | ∃p∈halfPlaneIdealBoundary\Λ,J=connectedComponentIn (halfPlaneIdealBoundary\Λ) p}

theorem nielsen_realGap_component_image (Λ : Set (OnePoint ℂ))
    (hinf : (∞ : OnePoint ℂ)∈Λ) {x : ℝ} (hx : x∉nielsenHalfPlaneRealSet Λ) :
    nielsenRealBoundaryPoint '' connectedComponentIn (nielsenHalfPlaneRealSet Λ)ᶜ x=
      connectedComponentIn (halfPlaneIdealBoundary\Λ) (nielsenRealBoundaryPoint x) := by
  rw [embedding_image_connectedComponentIn nielsenRealBoundaryPoint_isEmbedding hx,
    nielsen_halfPlane_ordinary_representation Λ hinf]

theorem nielsenHalfPlaneArcFamily_eq_realGapImage (Λ : Set (OnePoint ℂ))
    (hinf : (∞ : OnePoint ℂ)∈Λ) :
    nielsenHalfPlaneArcFamily Λ=(fun S : Set ℝ=>nielsenRealBoundaryPoint '' S) ''
      Auxiliary.Topology.nielsenRealGapFamily (nielsenHalfPlaneRealSet Λ) := by
  ext J
  constructor
  · rintro ⟨p,hp,rfl⟩
    rw [←nielsen_halfPlane_ordinary_representation Λ hinf] at hp
    obtain ⟨x,hx,rfl⟩:=hp
    exact ⟨connectedComponentIn (nielsenHalfPlaneRealSet Λ)ᶜ x,⟨x,hx,rfl⟩,
      nielsen_realGap_component_image Λ hinf hx⟩
  · rintro ⟨S,⟨x,hx,rfl⟩,rfl⟩
    refine ⟨nielsenRealBoundaryPoint x,?_,nielsen_realGap_component_image Λ hinf hx⟩
    rw [←nielsen_halfPlane_ordinary_representation Λ hinf]
    exact mem_image_of_mem _ hx

/-- The source Nielsen construction from actual maximal ideal arcs and their opposite
open geodesic half-planes, expressed in the genuine finite-real boundary chart. -/
def nielsenHalfPlaneArcRegion (Λ : Set (OnePoint ℂ)) : Set ℍ:=
  {z | ∀G : NielsenHalfPlaneGap,nielsenRealBoundaryPoint '' G.carrier∈nielsenHalfPlaneArcFamily Λ → z∈G.keptSide}

theorem nielsenHalfPlaneArcRegion_eq_realArcRegion (Λ : Set (OnePoint ℂ))
    (hinf : (∞ : OnePoint ℂ)∈Λ) :
    nielsenHalfPlaneArcRegion Λ=nielsenRealArcRegion (nielsenHalfPlaneRealSet Λ) := by
  have hi : Function.Injective (fun S : Set ℝ=>nielsenRealBoundaryPoint '' S):=
    Set.image_injective.mpr nielsenRealBoundaryPoint_isEmbedding.injective
  ext z
  constructor
  · intro hz G hG
    apply hz G
    rw [nielsenHalfPlaneArcFamily_eq_realGapImage Λ hinf]
    exact mem_image_of_mem _ hG
  · intro hz G hG
    rw [nielsenHalfPlaneArcFamily_eq_realGapImage Λ hinf] at hG
    obtain ⟨S,hS,he⟩:=hG
    exact hz G (hi he ▸ hS)

theorem nielsenHalfPlaneArcFamily_countable (Λ : Set (OnePoint ℂ))
    (hΛ : IsClosed Λ) (hinf : (∞ : OnePoint ℂ)∈Λ) : (nielsenHalfPlaneArcFamily Λ).Countable := by
  rw [nielsenHalfPlaneArcFamily_eq_realGapImage Λ hinf]
  exact (Auxiliary.Topology.nielsenRealGapFamily_countable (nielsenHalfPlaneRealSet_isClosed Λ hΛ)).image _


theorem nielsenHalfPlaneArcFamily_sUnion (Λ : Set (OnePoint ℂ)) :
    ⋃₀ nielsenHalfPlaneArcFamily Λ=halfPlaneIdealBoundary\Λ := by
  ext p
  constructor
  · rintro ⟨J,⟨q,_,rfl⟩,hp⟩
    exact connectedComponentIn_subset _ _ hp
  · intro hp
    exact ⟨connectedComponentIn (halfPlaneIdealBoundary\Λ) p,⟨p,hp,rfl⟩,mem_connectedComponentIn hp⟩

theorem nielsenHalfPlaneArcFamily_pairwiseDisjoint (Λ : Set (OnePoint ℂ)) :
    (nielsenHalfPlaneArcFamily Λ).PairwiseDisjoint id := by
  intro S hS T hT hne
  apply Set.disjoint_left.mpr
  intro p hpS hpT
  obtain ⟨x,_,rfl⟩:=hS
  obtain ⟨y,_,rfl⟩:=hT
  exact hne ((connectedComponentIn_eq hpS).trans (connectedComponentIn_eq hpT).symm)

theorem nielsenHalfPlaneArcFamily_exists_gap (Λ : Set (OnePoint ℂ)) (hΛ : IsClosed Λ)
    (hne : (nielsenHalfPlaneRealSet Λ).Nonempty) (hinf : (∞ : OnePoint ℂ)∈Λ)
    {J : Set (OnePoint ℂ)} (hJ : J∈nielsenHalfPlaneArcFamily Λ) :
    ∃G : NielsenHalfPlaneGap,nielsenRealBoundaryPoint '' G.carrier=J := by
  rw [nielsenHalfPlaneArcFamily_eq_realGapImage Λ hinf] at hJ
  obtain ⟨S,⟨x,hx,hS⟩,hSJ⟩:=hJ
  obtain ⟨G,hG⟩:=nielsen_realGap_exists (nielsenHalfPlaneRealSet_isClosed Λ hΛ) hne hx
  exact ⟨G,by rw [hG,←hS];exact hSJ⟩

theorem nielsen_cayley_realBoundaryPoint (x : ℝ) :
    extendedCayley (nielsenRealBoundaryPoint x)=(cayleyFormula (x : ℂ) : OnePoint ℂ) := by
  apply extendedCayley_coe
  intro hh
  have hi:=congrArg Complex.im hh
  norm_num at hi

theorem nielsen_cayleyIdealSet_image (Λ : Set (OnePoint ℂ))
    (hΛ : Λ⊆halfPlaneIdealBoundary) (hinf : (∞ : OnePoint ℂ)∈Λ) :
    ((↑) : ℂ → OnePoint ℂ) '' nielsenCayleyIdealSet (nielsenHalfPlaneRealSet Λ)=extendedCayley '' Λ := by
  have hh : ((↑) : ℂ → OnePoint ℂ) '' nielsenCayleyIdealSet (nielsenHalfPlaneRealSet Λ)=
      extendedCayley '' insert ∞ (nielsenRealBoundaryPoint '' nielsenHalfPlaneRealSet Λ):=by
    change ((↑) : ℂ → OnePoint ℂ) '' insert 1 (cayleyFormula '' (Complex.ofReal '' _))=_
    rw [image_insert_eq,image_insert_eq,extendedCayley_infty]
    congr 1
    ext p
    constructor
    · rintro ⟨q,⟨w,⟨x,hx,rfl⟩,rfl⟩,rfl⟩
      exact ⟨nielsenRealBoundaryPoint x,mem_image_of_mem _ hx,nielsen_cayley_realBoundaryPoint x⟩
    · rintro ⟨q,⟨x,hx,rfl⟩,rfl⟩
      exact ⟨cayleyFormula (x : ℂ),mem_image_of_mem _ (mem_image_of_mem _ hx),
        (nielsen_cayley_realBoundaryPoint x).symm⟩
  exact hh.trans (congrArg (fun S=>extendedCayley '' S) (nielsen_halfPlane_set_representation Λ hΛ hinf))

theorem nielsenHalfPlaneArcRegion_eq_cayleySupport (Λ : Set (OnePoint ℂ)) (hΛ : IsClosed Λ)
    (hne : (nielsenHalfPlaneRealSet Λ).Nonempty) (hinf : (∞ : OnePoint ℂ)∈Λ) :
    nielsenHalfPlaneArcRegion Λ=halfPlaneToDisc ⁻¹'
      nielsenGeodesicHalfspaceIntersection (nielsenCayleyIdealSet (nielsenHalfPlaneRealSet Λ)) := by
  rw [nielsenHalfPlaneArcRegion_eq_realArcRegion Λ hinf]
  exact nielsen_realArcRegion_eq_supporting _ (nielsenHalfPlaneRealSet_isClosed Λ hΛ) hne


/-- Actual maximal complementary arcs on the original unit-circle ideal boundary. -/
def nielsenDiscArcFamily (Λ : Set (OnePoint ℂ)) : Set (Set (OnePoint ℂ)):=
  {J | ∃p∈extendedDiscIdealBoundary\Λ,J=connectedComponentIn (extendedDiscIdealBoundary\Λ) p}

theorem nielsen_cayley_ordinaryBoundary (Λ : Set (OnePoint ℂ)) :
    extendedCayley '' (halfPlaneIdealBoundary\Λ)=extendedDiscIdealBoundary\(extendedCayley '' Λ) := by
  rw [image_sdiff extendedCayley.injective,extendedCayley_image_idealBoundary]

theorem nielsenDiscArcFamily_cayley_image (Λ : Set (OnePoint ℂ)) :
    nielsenDiscArcFamily (extendedCayley '' Λ)=
      (fun J : Set (OnePoint ℂ)=>extendedCayley '' J) '' nielsenHalfPlaneArcFamily Λ := by
  ext J
  constructor
  · rintro ⟨p,hp,rfl⟩
    rw [←nielsen_cayley_ordinaryBoundary Λ] at hp
    obtain ⟨q,hq,rfl⟩:=hp
    refine ⟨connectedComponentIn (halfPlaneIdealBoundary\Λ) q,⟨q,hq,rfl⟩,?_⟩
    change extendedCayley '' connectedComponentIn (halfPlaneIdealBoundary\Λ) q=_
    rw [extendedCayley.image_connectedComponentIn hq,nielsen_cayley_ordinaryBoundary Λ]
  · rintro ⟨S,⟨q,hq,rfl⟩,rfl⟩
    refine ⟨extendedCayley q,?_,?_⟩
    · rw [←nielsen_cayley_ordinaryBoundary Λ]
      exact mem_image_of_mem _ hq
    · change extendedCayley '' connectedComponentIn (halfPlaneIdealBoundary\Λ) q=_
      rw [extendedCayley.image_connectedComponentIn hq,nielsen_cayley_ordinaryBoundary Λ]

theorem nielsen_cayleyIdealSet_unitCircle (Λ : Set (OnePoint ℂ))
    (hΛ : Λ⊆halfPlaneIdealBoundary) (hinf : (∞ : OnePoint ℂ)∈Λ) :
    ∀p∈nielsenCayleyIdealSet (nielsenHalfPlaneRealSet Λ),‖p‖=1 := by
  intro p hp
  have hh : (p : OnePoint ℂ)∈extendedCayley '' Λ:=by
    rw [←nielsen_cayleyIdealSet_image Λ hΛ hinf]
    exact mem_image_of_mem _ hp
  have hb : (p : OnePoint ℂ)∈extendedCayley '' halfPlaneIdealBoundary:=image_mono hΛ hh
  rw [extendedCayley_image_idealBoundary] at hb
  exact (coe_mem_extendedDiscIdealBoundary p).mp hb

theorem nielsen_cayleyIdealSet_infinite (Λ : Set (OnePoint ℂ)) (hi : Λ.Infinite)
    (hΛ : Λ⊆halfPlaneIdealBoundary) (hinf : (∞ : OnePoint ℂ)∈Λ) :
    (nielsenCayleyIdealSet (nielsenHalfPlaneRealSet Λ)).Infinite := by
  intro hf
  have hh : (extendedCayley '' Λ).Finite:=by
    rw [←nielsen_cayleyIdealSet_image Λ hΛ hinf]
    exact hf.image _
  exact hi (Set.Finite.of_finite_image hh extendedCayley.injective.injOn)

theorem nielsenHalfPlaneArcRegion_isOpen (Λ : Set (OnePoint ℂ)) (hΛclosed : IsClosed Λ)
    (hi : Λ.Infinite) (hΛ : Λ⊆halfPlaneIdealBoundary) (hinf : (∞ : OnePoint ℂ)∈Λ) :
    IsOpen (nielsenHalfPlaneArcRegion Λ) := by
  rw [nielsenHalfPlaneArcRegion_eq_cayleySupport Λ hΛclosed (nielsenHalfPlaneRealSet_infinite Λ hi hΛ hinf).nonempty
    hinf]
  exact (nielsen_geodesicHalfspaces_isOpen _ (nielsen_cayleyIdealSet_infinite Λ hi hΛ hinf)
    (nielsen_cayleyIdealSet_unitCircle Λ hΛ hinf)).preimage cayleyHomeomorph.continuous

theorem nielsenHalfPlaneArcRegion_hConvex (Λ : Set (OnePoint ℂ)) (hΛclosed : IsClosed Λ)
    (hi : Λ.Infinite) (hΛ : Λ⊆halfPlaneIdealBoundary) (hinf : (∞ : OnePoint ℂ)∈Λ) :
    HConvex (nielsenHalfPlaneArcRegion Λ) := by
  apply (hConvex_iff_cayley_discHConvex _).mpr
  rw [nielsenHalfPlaneArcRegion_eq_cayleySupport Λ hΛclosed (nielsenHalfPlaneRealSet_infinite Λ hi hΛ hinf).nonempty
    hinf,
    Set.image_preimage_eq (f:=halfPlaneToDisc) _ cayleyHomeomorph.surjective]
  exact nielsen_geodesicHalfspaces_convex _ (nielsen_cayleyIdealSet_infinite Λ hi hΛ hinf)
    (nielsen_cayleyIdealSet_unitCircle Λ hΛ hinf)

theorem nielsenHalfPlaneArcRegion_nonempty (Λ : Set (OnePoint ℂ)) (hΛclosed : IsClosed Λ)
    (hi : Λ.Infinite) (hΛ : Λ⊆halfPlaneIdealBoundary) (hinf : (∞ : OnePoint ℂ)∈Λ) :
    (nielsenHalfPlaneArcRegion Λ).Nonempty := by
  rw [nielsenHalfPlaneArcRegion_eq_cayleySupport Λ hΛclosed (nielsenHalfPlaneRealSet_infinite Λ hi hΛ hinf).nonempty
    hinf]
  obtain ⟨z,hz⟩:=nielsen_geodesicHalfspaces_nonempty _ (nielsen_cayleyIdealSet_infinite Λ hi hΛ hinf)
    (nielsen_cayleyIdealSet_unitCircle Λ hΛ hinf)
  refine ⟨discToHalfPlane z,?_⟩
  change halfPlaneToDisc (discToHalfPlane z)∈nielsenGeodesicHalfspaceIntersection (nielsenCayleyIdealSet
    (nielsenHalfPlaneRealSet Λ))
  rw [halfPlaneToDisc_discToHalfPlane]
  exact hz

end
end LowDimensionalTopology.Geometry.Hyperbolic
