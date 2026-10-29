module

public import LowDimensionalTopology.Geometry.Teichmuller.NormalizedProjectiveFuchsianChange
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.HalfPlaneRegion

/-! # The genuine fundamental region under the actual normalized coefficient map -/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped UpperHalfPlane OnePoint

namespace LowDimensionalTopology.Geometry.Teichmuller.NormalizedCoefficientTransport

open GammaMeasurableBeltrami Hyperbolic Mobius

/-- The same actual normalized map transports every original genuine open
region to a genuine region for its actual deformed projective group. -/
theorem normalizedUpperHomeomorph_fundamentalRegion
    {Γ : Subgroup Deck} (hΓ : LiZhongQC.IsFuchsian Γ) (ν : Ball Γ)
    (P : Fuchsian.HalfPlaneFuchsianGroup (Γ.map realSLMobius))
    (P' : Fuchsian.HalfPlaneFuchsianGroup ((deformedGroup hΓ ν).map realSLMobius))
    (F : Set ℍ) (hF : Fuchsian.IsHalfPlaneFundamentalRegion P F) :
    Fuchsian.IsHalfPlaneFundamentalRegion P' (normalizedUpperHomeomorph ν '' F) := by
  classical
  let := P.nativeAction
  let := P'.nativeAction
  let f := normalizedUpperHomeomorph ν
  let e := normalizedProjectiveFuchsianEquiv hΓ ν
  have hsource (g : Γ.map realSLMobius) (z : ℍ) :
      projectiveConjugatedCoverAction Γ (Homeomorph.refl ℍ) g z = g • z := by
    apply UpperHalfPlane.ext
    apply OnePoint.coe_injective
    exact (projectiveConjugatedCoverAction_id_sphere Γ g z).symm.trans
      (P.nativeAction_boundary g z)
  have haction (g : Γ.map realSLMobius) (z : ℍ) : f (g • z) = e g • f z := by
    apply UpperHalfPlane.ext
    apply OnePoint.coe_injective
    have h := normalizedProjectiveFuchsianEquiv_conjugacy hΓ ν g z
    rw [hsource] at h
    exact h.symm.trans (P'.nativeAction_boundary (e g) (f z))
  obtain ⟨ho, hd, hc, hn⟩ := hF
  refine ⟨f.isOpenMap F ho, ?_, ?_, ?_⟩
  · intro k hk
    obtain ⟨g, rfl⟩ := e.surjective k
    have hg : g ≠ 1 := by
      intro h
      apply hk
      rw [h, map_one]
    apply Set.disjoint_left.mpr
    rintro x ⟨y, ⟨z, hz, rfl⟩, rfl⟩ ⟨w, hw, he⟩
    have hgw : g • z = w := f.injective ((haction g z).trans he.symm)
    exact Set.disjoint_left.mp (hd g hg) ⟨z, hz, rfl⟩ (by simpa only [hgw] using hw)
  · intro x
    obtain ⟨g, y, hy, hgy⟩ := hc (f.symm x)
    refine ⟨e g, f y, ?_, ?_⟩
    · rw [← f.image_closure F]
      exact ⟨y, hy, rfl⟩
    · rw [← haction, hgy, f.apply_symm_apply]
  · have hfront : UpperHalfPlane.coe '' frontier (f '' F) =
        normalizedMap ν '' (UpperHalfPlane.coe '' frontier F) := by
      rw [← f.image_frontier F, Set.image_image, Set.image_image]
      rfl
    rw [hfront]
    obtain ⟨Q, hQ, _⟩ := normalizedMap_spec ν
    exact LiZhongQC.thm9_6_cor1_null hQ (subset_univ _) hn

end LowDimensionalTopology.Geometry.Teichmuller.NormalizedCoefficientTransport
