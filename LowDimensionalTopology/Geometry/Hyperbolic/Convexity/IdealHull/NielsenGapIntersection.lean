/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Euclidean.InnerProduct.Gram
public import LowDimensionalTopology.Geometry.Hyperbolic.Convexity.IdealHull.NielsenBoundaryCuts
public import LowDimensionalTopology.Geometry.Auxiliary.Topology.RealLine.NielsenRealGaps
public import LowDimensionalTopology.Geometry.Hyperbolic.Convexity.IdealHull.NielsenHalfspaces
@[expose] public section
open Set
open scoped Topology OnePoint Complex.UnitDisc UpperHalfPlane RealInnerProductSpace
namespace LowDimensionalTopology.Geometry.Hyperbolic
open LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic
noncomputable section

/-- The ideal circle set in the actual Cayley chart, including its omitted real ideal point. -/
def nielsenCayleyIdealSet (A : Set ℝ) : Set ℂ:=insert 1 (cayleyFormula '' (Complex.ofReal '' A))

/-- Intersection of the genuine open geodesic sides opposite all maximal real complementary arcs. -/
def nielsenRealArcRegion (A : Set ℝ) : Set ℍ:=
  {z | ∀G : NielsenHalfPlaneGap,G.carrier∈Auxiliary.Topology.nielsenRealGapFamily A → z∈G.keptSide}

theorem nielsen_realGap_exists {A : Set ℝ} (hA : IsClosed A) (hne : A.Nonempty)
    {x : ℝ} (hx : x∉A) :
    ∃G : NielsenHalfPlaneGap,G.carrier=connectedComponentIn Aᶜ x := by
  rcases Auxiliary.Topology.nielsen_realGap_classification hA hne hx with ⟨a,b,_,_,hab,he⟩|⟨b,_,he⟩|⟨a,_,he⟩
  · exact ⟨.bounded a b hab,he.symm⟩
  · exact ⟨.left b,he.symm⟩
  · exact ⟨.right a,he.symm⟩

theorem nielsenCayleyIdealSet_support_iff (A : Set ℝ) (n : ℂ) (t : ℝ) :
    (∀p∈nielsenCayleyIdealSet A,inner ℝ n p≤t) ↔
      n.re≤t ∧ ∀x∈A,0≤nielsenHalfPlaneCutPolynomial n t x 0 := by
  constructor
  · intro h
    refine ⟨?_,fun x hx=>?_⟩
    · simpa [_root_.LowDimensionalTopology.Geometry.Euclidean.complex_real_inner_coordinates] using h 1 (mem_insert 1 _)
    · exact (nielsen_cayley_real_support_iff n t x).mp
        (h _ (mem_insert_of_mem _ (mem_image_of_mem _ (mem_image_of_mem _ hx))))
  · rintro ⟨hRe,hA⟩ p (hp|hp)
    · subst p
      simpa [_root_.LowDimensionalTopology.Geometry.Euclidean.complex_real_inner_coordinates] using hRe
    · obtain ⟨q,⟨x,hx,rfl⟩,rfl⟩:=hp
      exact (nielsen_cayley_real_support_iff n t x).mpr (hA x hx)

/-- Maximality is actual connected-component maximality, rather than a condition imposed on an interval. -/
theorem nielsen_gap_contained_maximal {A : Set ℝ} (hA : IsClosed A) (hne : A.Nonempty)
    (G : NielsenHalfPlaneGap) (hG : G.carrier⊆Aᶜ) :
    ∃J : NielsenHalfPlaneGap,J.carrier∈Auxiliary.Topology.nielsenRealGapFamily A ∧ G.carrier⊆J.carrier := by
  obtain ⟨x,hx⟩:=G.carrier_nonempty
  obtain ⟨J,hJ⟩:=nielsen_realGap_exists hA hne (hG hx)
  refine ⟨J,⟨x,hG hx,hJ⟩,?_⟩
  rw [hJ]
  exact G.carrier_preconnected.subset_connectedComponentIn hx hG

/-- The source intersection over actual maximal arcs equals the genuine supporting-geodesic
intersection in the true Cayley model; neither construction is defined by the other. -/
theorem nielsen_realArcRegion_eq_supporting (A : Set ℝ) (hA : IsClosed A) (hne : A.Nonempty) :
    nielsenRealArcRegion A=halfPlaneToDisc ⁻¹' nielsenGeodesicHalfspaceIntersection (nielsenCayleyIdealSet A) := by
  ext z
  constructor
  · intro hz n hn t hcut hs
    obtain ⟨ha,hP⟩:=(nielsenCayleyIdealSet_support_iff A n t).mp hs
    obtain ⟨G,hkept,hgap⟩:=nielsen_regular_cut_gap n t hcut ha
    have hG : G.carrier⊆Aᶜ:=by
      intro x hx hxA
      exact (not_lt_of_ge (hP x hxA)) ((hgap x).mpr hx)
    obtain ⟨J,hJ,hGJ⟩:=nielsen_gap_contained_maximal hA hne G hG
    exact (hkept z).mpr (G.keptSide_antitone J hGJ (hz J hJ))
  · intro hz G hG
    obtain ⟨x,hx,hGx⟩:=hG
    have hsup : ∀p∈nielsenCayleyIdealSet A,inner ℝ G.cutNormal p≤G.cutThreshold:=by
      apply (nielsenCayleyIdealSet_support_iff A _ _).mpr
      refine ⟨G.cut_regular.2,fun y hy=>?_⟩
      by_contra hneg
      have hm : y∈G.carrier:=(G.cut_carrier y).mp (lt_of_not_ge hneg)
      rw [hGx] at hm
      exact connectedComponentIn_subset Aᶜ x hm hy
    have hn : G.cutNormal≠0:=by
      intro he
      have hh:=G.cut_regular.1
      rw [he,norm_zero] at hh
      exact not_lt_of_ge (abs_nonneg _) hh
    exact (G.cut_keptSide z).mp (hz G.cutNormal hn G.cutThreshold G.cut_regular.1 hsup)

end
end LowDimensionalTopology.Geometry.Hyperbolic
