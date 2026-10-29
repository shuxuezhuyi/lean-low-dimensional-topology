module

public import LowDimensionalTopology.Geometry.Surfaces.OriginalThurstonBoundary

/-!
# The original positive-scaling quotient and weighted-spectrum closure

Concrete coordinate homeomorphisms show that the existing quotient projection
is open. Its original quotient topology then identifies the preimage of the
projective curve closure with the independent nonzero weighted-spectrum closure.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set Topology

namespace LowDimensionalTopology.Geometry.Surfaces

variable {X : Type} [TopologicalSpace X]

/-- One positive real scales every coordinate of the same original nonnegative product. -/
def scaleNonnegativeSpectrumPositive (a : Set.Ioi (0 : ℝ))
    (f : NonnegativeSpectrum X) : NonnegativeSpectrum X :=
  fun β => ⟨a.val * (f β : ℝ), mul_nonneg a.property.le (f β).property⟩

/-- Coordinate multiplication is continuous in the actual original product topology. -/
theorem continuous_scaleNonnegativeSpectrumPositive (a : Set.Ioi (0 : ℝ)) :
    Continuous (scaleNonnegativeSpectrumPositive a : NonnegativeSpectrum X → _) := by
  apply continuous_pi
  intro β
  exact (continuous_const.mul (continuous_subtype_val.comp (continuous_apply β))).subtype_mk _

/-- Common positive multiplication preserves exclusion of the whole zero spectrum. -/
def scaleNonzeroNonnegativeSpectrumPositive (a : Set.Ioi (0 : ℝ))
    (f : NonzeroNonnegativeSpectrum X) : NonzeroNonnegativeSpectrum X := by
  refine ⟨scaleNonnegativeSpectrumPositive a f.val, ?_⟩
  intro hzero
  apply f.property
  funext β
  apply Subtype.ext
  have hβ : a.val * (f.val β : ℝ) = 0 :=
    congrArg (fun z : NonnegativeSpectrum X => (z β : ℝ)) hzero
  exact (mul_eq_zero.mp hβ).resolve_left (ne_of_gt a.property)

/-- The same scalar map is continuous on the actual nonzero subspace. -/
theorem continuous_scaleNonzeroNonnegativeSpectrumPositive (a : Set.Ioi (0 : ℝ)) :
    Continuous (scaleNonzeroNonnegativeSpectrumPositive a : NonzeroNonnegativeSpectrum X → _) :=
  ((continuous_scaleNonnegativeSpectrumPositive a).comp continuous_subtype_val).subtype_mk _

/-- Common positive multiplication and reciprocal multiplication are actual homeomorphisms. -/
def nonzeroNonnegativeSpectrumScaleHomeomorph (a : Set.Ioi (0 : ℝ)) :
    NonzeroNonnegativeSpectrum X ≃ₜ NonzeroNonnegativeSpectrum X where
  toFun := scaleNonzeroNonnegativeSpectrumPositive a
  invFun := scaleNonzeroNonnegativeSpectrumPositive ⟨a.val⁻¹, inv_pos.mpr a.property⟩
  left_inv := by
    intro f
    apply Subtype.ext
    funext β
    apply Subtype.ext
    change a.val⁻¹ * (a.val * (f.val β : ℝ)) = (f.val β : ℝ)
    rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt a.property), one_mul]
  right_inv := by
    intro f
    apply Subtype.ext
    funext β
    apply Subtype.ext
    change a.val * (a.val⁻¹ * (f.val β : ℝ)) = (f.val β : ℝ)
    rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt a.property), one_mul]
  continuous_toFun := continuous_scaleNonzeroNonnegativeSpectrumPositive a
  continuous_invFun :=
    continuous_scaleNonzeroNonnegativeSpectrumPositive ⟨a.val⁻¹, inv_pos.mpr a.property⟩

/-- These concrete coordinate homeomorphisms leave the actual projective ray unchanged. -/
theorem projectivize_nonzeroNonnegativeSpectrumScaleHomeomorph
    (a : Set.Ioi (0 : ℝ)) (f : NonzeroNonnegativeSpectrum X) :
    projectivizeNonnegativeSpectrum (nonzeroNonnegativeSpectrumScaleHomeomorph a f) =
      projectivizeNonnegativeSpectrum f := by
  apply (projectivizeNonnegativeSpectrum_eq_iff _ _).mpr
  exact ⟨a.val, a.property, fun _ => rfl⟩

/-- Saturation is exactly the union of the concrete common-scalar homeomorphism images. -/
theorem projectivizeNonnegativeSpectrum_preimage_image (U : Set (NonzeroNonnegativeSpectrum X)) :
    projectivizeNonnegativeSpectrum ⁻¹' (projectivizeNonnegativeSpectrum '' U) =
      ⋃ a : Set.Ioi (0 : ℝ), nonzeroNonnegativeSpectrumScaleHomeomorph a '' U := by
  ext f
  constructor
  · rintro ⟨z, hz, hzf⟩
    obtain ⟨c, hc, hcoords⟩ := (projectivizeNonnegativeSpectrum_eq_iff f z).mp hzf.symm
    refine Set.mem_iUnion.mpr ⟨⟨c, hc⟩, z, hz, ?_⟩
    apply Subtype.ext
    funext β
    apply Subtype.ext
    exact (hcoords β).symm
  · intro hf
    obtain ⟨a, z, hz, rfl⟩ := Set.mem_iUnion.mp hf
    exact ⟨z, hz, (projectivize_nonzeroNonnegativeSpectrumScaleHomeomorph a z).symm⟩

/-- The existing positive-scaling quotient projection is open in its original topology. -/
theorem isOpenMap_projectivizeNonnegativeSpectrum :
    IsOpenMap (projectivizeNonnegativeSpectrum : NonzeroNonnegativeSpectrum X → _) := by
  intro U hU
  apply (isQuotientMap_projectivizeNonnegativeSpectrum (X := X)).isCoinducing.isOpen_preimage.mp
  rw [projectivizeNonnegativeSpectrum_preimage_image]
  exact isOpen_iUnion fun a => (nonzeroNonnegativeSpectrumScaleHomeomorph a).isOpenMap U hU

variable (R : ClosedRiemannSurface X) {g : ℕ} (hg : 2 ≤ g) (hgenus : R.HasGenus g)
variable (hCurve : Unproved.Surfaces.ClosedCurveIntersectionGeometry R hg hgenus)

/-- The same positive scalar in a projective curve fiber is its actual original curve weight. -/
theorem projectivizeNonnegativeSpectrum_preimage_curveRange :
    projectivizeNonnegativeSpectrum ⁻¹'
      Set.range (projectiveIntersectionSpectrum R hg hgenus hCurve) =
        Set.range (weightedIntersectionSpectrum R hg hgenus hCurve) := by
  ext f
  constructor
  · rintro ⟨β, hβ⟩
    have hray : projectivizeNonnegativeSpectrum f =
        projectivizeNonnegativeSpectrum (intersectionSpectrum R hg hgenus hCurve β) := hβ.symm
    obtain ⟨c, hc, hcoords⟩ := (projectivizeNonnegativeSpectrum_eq_iff _ _).mp hray
    refine ⟨(⟨c, hc⟩, β), ?_⟩
    apply Subtype.ext
    funext γ
    apply Subtype.ext
    exact (hcoords γ).symm
  · rintro ⟨⟨a, β⟩, rfl⟩
    exact ⟨β, (projectivize_weightedIntersectionSpectrum R hg hgenus hCurve a β).symm⟩

/-- Original projective closure membership equals original nonzero weighted-closure membership. -/
theorem projectivizeNonnegativeSpectrum_mem_originalThurstonBoundary_iff
    (f : NonzeroNonnegativeSpectrum X) :
    projectivizeNonnegativeSpectrum f ∈ originalThurstonBoundary R hg hgenus hCurve ↔
      f.val ∈ closure (Set.range (fun w : Set.Ioi (0 : ℝ) × EssentialSimpleFreeClass X =>
        (weightedIntersectionSpectrum R hg hgenus hCurve w).val)) := by
  have hopen : IsOpenMap (projectivizeNonnegativeSpectrum :
      NonzeroNonnegativeSpectrum X → ProjectiveNonnegativeSpectrum X) :=
    isOpenMap_projectivizeNonnegativeSpectrum
  have hpre := hopen.preimage_closure_eq_closure_preimage
    (isQuotientMap_projectivizeNonnegativeSpectrum (X := X)).continuous
    (Set.range (projectiveIntersectionSpectrum R hg hgenus hCurve))
  rw [projectivizeNonnegativeSpectrum_preimage_curveRange R hg hgenus hCurve] at hpre
  have hsub : closure (Set.range (weightedIntersectionSpectrum R hg hgenus hCurve)) =
      Subtype.val ⁻¹' closure (Set.range (fun w : Set.Ioi (0 : ℝ) × EssentialSimpleFreeClass X =>
        (weightedIntersectionSpectrum R hg hgenus hCurve w).val)) := by
    simpa only [← Set.range_comp, Function.comp_def] using
      (IsEmbedding.subtypeVal.closure_eq_preimage_closure_image
        (Set.range (weightedIntersectionSpectrum R hg hgenus hCurve)))
  change f ∈ projectivizeNonnegativeSpectrum ⁻¹'
    closure (Set.range (projectiveIntersectionSpectrum R hg hgenus hCurve)) ↔ _
  rw [hpre, hsub, Set.mem_preimage]

end LowDimensionalTopology.Geometry.Surfaces
