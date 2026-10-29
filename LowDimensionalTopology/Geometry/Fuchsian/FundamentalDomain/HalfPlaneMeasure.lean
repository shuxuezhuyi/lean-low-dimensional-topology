module
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.HalfPlaneRegion
public import LowDimensionalTopology.Geometry.Hyperbolic.Area.NativeIsometryMeasure
public import Mathlib.MeasureTheory.Group.FundamentalDomain
@[expose] public section
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped UpperHalfPlane Pointwise
namespace LowDimensionalTopology.Geometry.Fuchsian
/-- Every original open region is a Mathlib a.e. fundamental domain for its actual projective action. -/
theorem IsHalfPlaneFundamentalRegion.measureFundamentalDomain
    {H : Subgroup Mobius.complexMobiusGroup} (P : HalfPlaneFuchsianGroup H)
    {F : Set ℍ} (hF : IsHalfPlaneFundamentalRegion P F) :
    letI := P.nativeAction
    MeasureTheory.IsFundamentalDomain H F (volume : Measure ℍ) := by
  let := P.nativeAction
  let : Countable H := Mobius.discreteMobius_countable H P.discrete
  have hq : ∀ g : H, QuasiMeasurePreserving (fun x : ℍ => g • x) volume volume :=
    fun g => (Hyperbolic.nativeIsometry_measurePreserving (P.nativeHom g)).quasiMeasurePreserving
  have hn : (volume : Measure ℍ) (frontier F) = 0 :=
    (Hyperbolic.halfPlane_volume_eq_zero_iff_planar_volume_eq_zero _).mpr hF.2.2.2
  have hb : ∀ᵐ y : ℍ ∂(volume : Measure ℍ), y ∉ frontier F :=
    measure_eq_zero_iff_ae_notMem.mp hn
  have ha : ∀ᵐ x : ℍ ∂volume, ∀ g : H, g • x ∉ frontier F := by
    rw [ae_all_iff]
    intro g
    exact QuasiMeasurePreserving.ae (hq g) (p := fun y : ℍ => y ∉ frontier F) hb
  have hc : ∀ᵐ x : ℍ ∂volume, ∃ g : H, g • x ∈ F := ha.mono fun x hx => by
    obtain ⟨g, y, hy, hgy⟩ := hF.2.2.1 x
    have hyF : y ∈ interior F := by
      rw [← closure_sdiff_frontier]
      refine ⟨hy, ?_⟩
      simpa only [← hgy, inv_smul_smul] using hx g⁻¹
    refine ⟨g⁻¹, ?_⟩
    simpa only [← hgy, inv_smul_smul, hF.1.interior_eq] using hyF
  exact MeasureTheory.IsFundamentalDomain.mk'' hF.1.measurableSet.nullMeasurableSet hc
    (fun g hg => (hF.2.1 g hg).aedisjoint) hq
end LowDimensionalTopology.Geometry.Fuchsian
