module

public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.HalfPlaneRegion
public import LowDimensionalTopology.External.LiZhongQC.Ch11.S36_Hamilton
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Open fundamental regions and measurable integration domains

An open half-plane fundamental region need not meet its boundary orbits.
The planar image of its relative closure does meet every orbit, and is a
measurable fundamental domain in the integration convention. Its difference
from the original open region is null, so all set integrals agree. Neither
connectedness nor compactness of the region is required.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set MeasureTheory Topology
open scoped UpperHalfPlane

namespace LowDimensionalTopology.Geometry.Fuchsian

/-- The planar integration domain associated to the actual relative closure
of an open half-plane region. -/
def closedPlanarRegion (F : Set ℍ) : Set ℂ :=
  UpperHalfPlane.coe '' closure F

private theorem disjoint_interior_closures {S T : Set ℍ}
    (h : Disjoint S T) (hT : IsOpen T) :
    Disjoint (interior (closure S)) (interior (closure T)) := by
  exact (((h.closure_left hT).mono_left interior_subset).closure_right
    isOpen_interior).mono_right interior_subset

/-- The planar image of the open region and that of its relative closure
agree almost everywhere for planar Lebesgue measure. -/
theorem openPlanarRegion_ae_closedPlanarRegion {F : Set ℍ}
    (hF : IsOpen F)
    (hfront : (volume : Measure ℂ) (UpperHalfPlane.coe '' frontier F) = 0) :
    (UpperHalfPlane.coe '' F) =ᵐ[volume] closedPlanarRegion F := by
  apply ae_eq_set.mpr
  constructor
  · have hsub : UpperHalfPlane.coe '' F ⊆ closedPlanarRegion F :=
      image_mono subset_closure
    rw [sdiff_eq_empty.mpr hsub, measure_empty]
  · apply measure_mono_null _ hfront
    rintro z ⟨⟨τ, hτ, rfl⟩, hnot⟩
    refine ⟨τ, ?_, rfl⟩
    change τ ∈ closure F ∧ τ ∉ interior F
    refine ⟨hτ, ?_⟩
    rw [hF.interior_eq]
    exact fun hτF => hnot ⟨τ, hτF, rfl⟩

/-- Every integrand has the same set integral over the original open region
and the closed measurable integration domain. No integrability premise is
needed for this equality of the actual Bochner integrals. -/
theorem integral_openPlanarRegion_eq_closedPlanarRegion {F : Set ℍ}
    (hF : IsOpen F)
    (hfront : (volume : Measure ℂ) (UpperHalfPlane.coe '' frontier F) = 0)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : ℂ → E) :
    (∫ z in UpperHalfPlane.coe '' F, f z) = ∫ z in closedPlanarRegion F, f z :=
  setIntegral_congr_set (openPlanarRegion_ae_closedPlanarRegion hF hfront)

/-- Integrability over the original open region is exactly integrability
over its associated closed measurable domain. -/
theorem integrableOn_openPlanarRegion_iff_closedPlanarRegion {F : Set ℍ}
    (hF : IsOpen F)
    (hfront : (volume : Measure ℂ) (UpperHalfPlane.coe '' frontier F) = 0)
    {E : Type*} [NormedAddCommGroup E] (f : ℂ → E) :
    IntegrableOn f (UpperHalfPlane.coe '' F) ↔ IntegrableOn f (closedPlanarRegion F) := by
  change Integrable f (volume.restrict (UpperHalfPlane.coe '' F)) ↔
    Integrable f (volume.restrict (closedPlanarRegion F))
  rw [Measure.restrict_congr_set (openPlanarRegion_ae_closedPlanarRegion hF hfront)]

/-- An actual native open fundamental region gives a source integration
fundamental domain for the same matrix group. The native group is its actual
Möbius image; matrix lifts differing by sign cause no extra orbit assumption. -/
theorem closedPlanarRegion_isFundamentalDomainH
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    (P : HalfPlaneFuchsianGroup (Γ.map Hyperbolic.realSLMobius))
    {F : Set ℍ} (hF : IsHalfPlaneFundamentalRegion P F) :
    LiZhongQC.IsFundamentalDomainH Γ (closedPlanarRegion F) := by
  let := P.nativeAction
  dsimp only [IsHalfPlaneFundamentalRegion] at hF
  rcases hF with ⟨ho, hd, hc, hn⟩
  have hO : IsOpen (UpperHalfPlane.coe '' F) :=
    UpperHalfPlane.isOpenEmbedding_coe.isOpenMap F ho
  have hOD : UpperHalfPlane.coe '' F ⊆ closedPlanarRegion F :=
    image_mono subset_closure
  have hOiD : UpperHalfPlane.coe '' F ⊆ interior (closedPlanarRegion F) :=
    hO.subset_interior_iff.mpr hOD
  have hi (τ : ℍ) (hτ : (τ : ℂ) ∈ interior (closedPlanarRegion F)) :
      τ ∈ interior (closure F) := by
    have hpre : UpperHalfPlane.coe ⁻¹' closedPlanarRegion F = closure F :=
      UpperHalfPlane.coe_injective.preimage_image _
    have h := preimage_interior_subset_interior_preimage UpperHalfPlane.continuous_coe hτ
    rwa [hpre] at h
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rintro z ⟨τ, _, rfl⟩
    exact τ.im_pos
  · exact UpperHalfPlane.measurableEmbedding_coe.measurableSet_image.mpr
      isClosed_closure.measurableSet
  · intro τ
    obtain ⟨g, y, hy, hgy⟩ := hc τ
    obtain ⟨A, hA, hAg⟩ := g.property
    have hAy : A • y = τ := (P.nativeAction_realSL g A hAg y).symm.trans hgy
    refine ⟨A⁻¹, Γ.inv_mem hA, y, hy, ?_⟩
    rw [← hAy, inv_smul_smul]
  · intro τ₁ τ₂ hτ₁ hτ₂ hrel
    obtain ⟨A, hA, hAτ⟩ := hrel
    let g : Γ.map Hyperbolic.realSLMobius :=
      ⟨Hyperbolic.realSLMobius A, A, hA, rfl⟩
    have hact : g • τ₁ = τ₂ := (P.nativeAction_realSL g A rfl τ₁).trans hAτ
    by_cases hg : g = 1
    · simpa only [hg, one_smul] using hact
    · let e : ℍ ≃ₜ ℍ := (P.nativeHom g).toHomeomorph
      have hdis : Disjoint ((fun x : ℍ => g • x) '' interior (closure F))
          (interior (closure F)) := by
        change Disjoint (e '' interior (closure F)) (interior (closure F))
        rw [e.image_interior, e.image_closure]
        exact disjoint_interior_closures (hd g hg) ho
      exact (Set.disjoint_left.mp hdis ⟨τ₁, hi τ₁ hτ₁, hact⟩ (hi τ₂ hτ₂)).elim
  · apply measure_mono_null _ hn
    rintro z ⟨⟨τ, hτ, rfl⟩, hnot⟩
    refine ⟨τ, ?_, rfl⟩
    change τ ∈ closure F ∧ τ ∉ interior F
    refine ⟨hτ, ?_⟩
    rw [ho.interior_eq]
    exact fun hτF => hnot (hOiD ⟨τ, hτF, rfl⟩)

end LowDimensionalTopology.Geometry.Fuchsian
