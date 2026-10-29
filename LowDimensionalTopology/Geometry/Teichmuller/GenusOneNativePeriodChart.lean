module

public import LowDimensionalTopology.Unproved.Teichmuller.OriginalGenusOnePeriodCoordinates
public import LowDimensionalTopology.Geometry.Teichmuller.GenusOnePeriodBeltramiDerivative

/-!
# Period coordinates on the original marked-torus quotient

The independent period-coordinate premise supplies a homeomorphism for the
existing native quotient topology. Its inverse, followed by the original
upper-half-plane inclusion, is the coordinate used throughout this file.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set Filter Topology
open scoped UpperHalfPlane

namespace LowDimensionalTopology.Geometry.Teichmuller.GenusOne
open Surfaces

/-- The period chart on the original quotient and its existing topology. -/
def nativePeriodChart (τ₀ : ℍ)
    (hperiod : Unproved.Teichmuller.OriginalGenusOnePeriodCoordinates τ₀) :
    OpenPartialHomeomorph
      (TeichmullerSpace.{0, 0} (normalizedClosedTorus τ₀)) ℂ :=
  let E : ℍ ≃ₜ TeichmullerSpace.{0, 0} (normalizedClosedTorus τ₀) :=
    Classical.choose hperiod
  let f : TeichmullerSpace.{0, 0} (normalizedClosedTorus τ₀) → ℂ :=
    fun q => (E.symm q : ℂ)
  let hf : Topology.IsOpenEmbedding f := by
    change Topology.IsOpenEmbedding (((↑) : ℍ → ℂ) ∘ E.symm)
    exact UpperHalfPlane.isOpenEmbedding_coe.comp E.symm.isOpenEmbedding
  hf.toOpenPartialHomeomorph f

theorem nativePeriodChart_source (τ₀ : ℍ)
    (hperiod : Unproved.Teichmuller.OriginalGenusOnePeriodCoordinates τ₀) :
    (nativePeriodChart τ₀ hperiod).source = univ := by
  rfl

/-- The actual period family has precisely its specified period coordinate. -/
theorem nativePeriodChart_normalizedFamilyPoint (τ₀ : ℍ)
    (hperiod : Unproved.Teichmuller.OriginalGenusOnePeriodCoordinates τ₀) (σ : ℍ) :
    nativePeriodChart τ₀ hperiod (normalizedFamilyPoint τ₀ σ) = (σ : ℂ) := by
  let E : ℍ ≃ₜ TeichmullerSpace.{0, 0} (normalizedClosedTorus τ₀) :=
    Classical.choose hperiod
  have hE : E σ = normalizedFamilyPoint τ₀ σ := (Classical.choose_spec hperiod) σ
  change (E.symm (normalizedFamilyPoint τ₀ σ) : ℂ) = (σ : ℂ)
  rw [← hE, E.symm_apply_apply]

/-- The original marked-family curve has unit derivative in its actual period
coordinate. No tensor derivative or tangent-space identification is assumed. -/
theorem hasDerivAt_nativePeriodChart_nearbyFamily (τ₀ : ℍ)
    (hperiod : Unproved.Teichmuller.OriginalGenusOnePeriodCoordinates τ₀) (τ : ℍ) :
    HasDerivAt
      (fun t : ℂ => nativePeriodChart τ₀ hperiod
        (normalizedFamilyPoint τ₀ (nearbyPeriod τ t))) 1 0 := by
  have hcont : ContinuousAt (fun t : ℂ => ((τ : ℂ) + t).im) 0 :=
    (Complex.continuous_im.comp (continuous_const.add continuous_id)).continuousAt
  have hpos : ∀ᶠ t : ℂ in 𝓝 0, 0 < ((τ : ℂ) + t).im :=
    (continuousAt_const : ContinuousAt (fun _ : ℂ => (0 : ℝ)) 0).eventually_lt hcont
      (by simpa only [add_zero, UpperHalfPlane.coe_im] using τ.im_pos)
  have hbase : HasDerivAt (fun t : ℂ => (τ : ℂ) + t) 1 0 := by
    exact (hasDerivAt_id (0 : ℂ)).const_add (τ : ℂ)
  apply hbase.congr_of_eventuallyEq
  filter_upwards [hpos] with t ht
  rw [nativePeriodChart_normalizedFamilyPoint]
  simp only [nearbyPeriod, dite_eq_left ht]

end LowDimensionalTopology.Geometry.Teichmuller.GenusOne
