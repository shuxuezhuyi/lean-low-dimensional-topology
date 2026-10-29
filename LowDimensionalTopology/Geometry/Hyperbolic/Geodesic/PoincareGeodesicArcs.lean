module

public import LowDimensionalTopology.Geometry.Hyperbolic.Geodesic.RectifiableMinimizerExistence
public import LowDimensionalTopology.Geometry.Hyperbolic.Geodesic.RectifiableMinimizers
public import LowDimensionalTopology.Geometry.Hyperbolic.ModelMaps.CayleyHalfPlaneDisk.GeodesicSegments

/-!
# The unique actual rectifiable Poincaré geodesic arc

A geodesic arc is the image of an actual injective continuous rectifiable
joining curve whose literal weighted arclength is the full rectifiable distance.
The geometric segment is a conclusion, rather than part of this definition.
Distinct endpoints have a unique such image. Its complete supporting circle or
diameter is geometrically orthogonal to the unit circle; the finite interior
arc is not asserted to meet the boundary. Coincident endpoints are treated by
the separate singleton convention with a singleton parameter interval.
-/

@[expose] public section
noncomputable section

open Set MeasureTheory
open scoped ENNReal Complex.UnitDisc

namespace LowDimensionalTopology.Geometry.Hyperbolic

/-- The book's geometric minimizing arc, with its actual rectifiable,
injective parametrization and literal full-rectifiable minimum as witnesses.
A singleton parameter interval is allowed for the coincident-endpoint convention. -/
def IsPoincareGeodesicArc (z w : 𝔻) (S : Set ℂ) : Prop :=
  ∃ c : RectifiableCurve, c.IsPathIn LiZhongQC.unitDisc z w ∧
    InjOn c.curve (Icc c.a c.b) ∧
    c.weightedLength (fun ζ => ENNReal.ofReal (LiZhongQC.poincareDensityDisc ζ)) =
      discRectifiableEDist z w ∧ c.curve '' Icc c.a c.b = S

/-- Every actual minimizing arc has the already independently defined
geometric segment as its entire unparametrized image. -/
theorem IsPoincareGeodesicArc.trace_eq {z w : 𝔻} {S : Set ℂ}
    (hS : IsPoincareGeodesicArc z w S) (hzw : z ≠ w) :
    S = ((↑) : 𝔻 → ℂ) '' closedDiscHSegment z w := by
  obtain ⟨c, hc, _hinj, hmin, htrace⟩ := hS
  rw [discRectifiableEDist_eq_pathDist] at hmin
  exact htrace.symm.trans
    (rectifiable_trace_eq_closedDiscHSegment_of_minimizing c hzw hc hmin)

/-- The genuine segment admits an actual injective rectifiable traversal
which attains the infimum over every continuous rectifiable joining curve. -/
theorem isPoincareGeodesicArc_closedDiscHSegment (z w : 𝔻) (hzw : z ≠ w) :
    IsPoincareGeodesicArc z w (((↑) : 𝔻 → ℂ) '' closedDiscHSegment z w) := by
  obtain ⟨c, hc, hlen, hinj⟩ := exists_injective_rectifiable_disk_minimizer z w hzw
  refine ⟨c, hc, hinj, ?_, ?_⟩
  · rw [discRectifiableEDist_eq_pathDist]
    exact hlen
  · exact rectifiable_trace_eq_closedDiscHSegment_of_minimizing c hzw hc hlen

/-- The book's minimizing-arc definition is equivalent to the actual
geometric closed segment, as a theorem about the complete traversed image. -/
theorem isPoincareGeodesicArc_iff {z w : 𝔻} {S : Set ℂ} (hzw : z ≠ w) :
    IsPoincareGeodesicArc z w S ↔
      S = ((↑) : 𝔻 → ℂ) '' closedDiscHSegment z w := by
  constructor
  · exact fun hS => hS.trace_eq hzw
  · rintro rfl
    exact isPoincareGeodesicArc_closedDiscHSegment z w hzw

/-- There is a unique geometric minimizing arc between distinct endpoints.
Uniqueness concerns its image, and makes no claim about parametrization. -/
theorem existsUnique_poincareGeodesicArc (z w : 𝔻) (hzw : z ≠ w) :
    ∃! S : Set ℂ, IsPoincareGeodesicArc z w S := by
  exact ⟨((↑) : 𝔻 → ℂ) '' closedDiscHSegment z w,
    isPoincareGeodesicArc_closedDiscHSegment z w hzw,
    fun _ hS => hS.trace_eq hzw⟩

/-- This classification describes the complete supporting generalized circle,
including infinity for a diameter, rather than only the finite geodesic arc. -/
theorem DiscLine.completeCircle_or_diameter (L : DiscLine) :
    (∃ c : ℂ, ∃ r : ℝ, 0 < r ∧ ‖c‖ ^ 2 = r ^ 2 + 1 ∧
      L.val.val = Mobius.complexCircle c r) ∨
    (∃ a : ℂ, a ≠ 0 ∧ L.val.val = Mobius.complexLine a 0) := by
  rcases (Mobius.isComplexGeneralizedCircle_iff L.val.val).mp L.val.property with
    ⟨c, r, hr, he⟩ | ⟨a, t, ha, he⟩
  · have hs : L.val =
        ⟨Mobius.complexCircle c r, Mobius.complexCircle_isGeneralized c r hr⟩ :=
      Subtype.ext he
    have ho := L.property
    rw [hs] at ho
    exact Or.inl ⟨c, r, hr, (complexCircle_orthogonal_discBoundary_iff c r hr).mp ho, he⟩
  · have hs : L.val =
        ⟨Mobius.complexLine a t, Mobius.complexLine_isGeneralized a t ha⟩ :=
      Subtype.ext he
    have ho := L.property
    rw [hs] at ho
    have ht : t = 0 := (complexLine_orthogonal_discBoundary_iff a t ha).mp ho
    exact Or.inr ⟨a, ha, by simpa only [ht] using he⟩

/-- The finite arc is exactly the native closed subarc of its unique complete
supporting circle or diameter, which is orthogonal to the actual unit circle. -/
theorem IsPoincareGeodesicArc.existsUnique_supportingLine {z w : 𝔻} {S : Set ℂ}
    (hS : IsPoincareGeodesicArc z w S) (hzw : z ≠ w) :
    ∃! L : DiscLine, z ∈ L.carrier ∧ w ∈ L.carrier ∧
      S = ((↑) : 𝔻 → ℂ) '' nativeDiscClosedSegment L z w ∧
      S ⊆ ((↑) : 𝔻 → ℂ) '' L.carrier ∧
      Mobius.ComplexCirclesOrthogonal L.val discBoundaryCircle ∧
      ((∃ c : ℂ, ∃ r : ℝ, 0 < r ∧ ‖c‖ ^ 2 = r ^ 2 + 1 ∧
          L.val.val = Mobius.complexCircle c r) ∨
        (∃ a : ℂ, a ≠ 0 ∧ L.val.val = Mobius.complexLine a 0)) := by
  obtain ⟨L, ⟨hz, hw⟩, huniq⟩ := existsUnique_discLine_through z w hzw
  have htrace : S = ((↑) : 𝔻 → ℂ) '' nativeDiscClosedSegment L z w := by
    rw [nativeDiscClosedSegment_eq L hzw hz hw]
    exact hS.trace_eq hzw
  have hsub : nativeDiscClosedSegment L z w ⊆ L.carrier := by
    intro u hu
    simp only [nativeDiscClosedSegment, mem_insert_iff] at hu
    rcases hu with rfl | rfl | hu
    · exact hz
    · exact hw
    · exact hu.1.1
  refine ⟨L, ⟨hz, hw, htrace, ?_, L.property, L.completeCircle_or_diameter⟩, ?_⟩
  · rw [htrace]
    exact image_mono hsub
  · intro M hM
    exact huniq M ⟨hM.1, hM.2.1⟩

/-- A singleton has the literal zero-length constant traversal on `[0,0]`.
No constant map on a nondegenerate interval is asserted to be injective. -/
theorem isPoincareGeodesicArc_singleton (z : 𝔻) :
    IsPoincareGeodesicArc z z {(z : ℂ)} := by
  let c : RectifiableCurve :=
    { a := 0
      b := 0
      curve := fun _ => (z : ℂ)
      ordered := le_rfl
      continuous := continuousOn_const
      boundedVariation := BoundedVariationOn.of_subsingleton (by simp) }
  have hpath : c.IsPathIn LiZhongQC.unitDisc z z := by
    refine ⟨rfl, rfl, ?_⟩
    rintro _ ⟨t, _ht, rfl⟩
    exact z.property
  have hinj : InjOn c.curve (Icc c.a c.b) := by
    intro a ha b hb _
    exact le_antisymm (ha.2.trans hb.1) (hb.2.trans ha.1)
  have hlength : c.euclideanLength = 0 := by
    change variationOnFromTo (fun _ : ℝ => (z : ℂ)) (Icc (0 : ℝ) 0) 0 0 = 0
    exact variationOnFromTo.self _ _ _
  refine ⟨c, hpath, hinj, ?_, ?_⟩
  · unfold RectifiableCurve.weightedLength
    rw [hlength, discRectifiableEDist_eq_pathDist, discPathDist_eq_halfPlane, dist_self]
    simp
  · simp [c]

/-- The coincident-endpoint convention also has a unique geometric image. -/
theorem isPoincareGeodesicArc_self_iff (z : 𝔻) (S : Set ℂ) :
    IsPoincareGeodesicArc z z S ↔ S = {(z : ℂ)} := by
  constructor
  · rintro ⟨c, hc, _hinj, hmin, htrace⟩
    have hzero : c.weightedLength
        (fun ζ => ENNReal.ofReal (LiZhongQC.poincareDensityDisc ζ)) = 0 := by
      rw [discRectifiableEDist_eq_pathDist, discPathDist_eq_halfPlane, dist_self] at hmin
      simpa only [ENNReal.ofReal_zero] using hmin
    exact htrace.symm.trans (rectifiable_trace_eq_singleton_of_length_zero c hc hzero)
  · rintro rfl
    exact isPoincareGeodesicArc_singleton z

end LowDimensionalTopology.Geometry.Hyperbolic
