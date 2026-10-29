module

public import LowDimensionalTopology.Geometry.Teichmuller.NativeBersTranslationLocalInverse

/-!
# The genuine coordinate translation is bijective on the entire Bers domains

The domain is the image of the whole compatible coefficient ball. Its exact
source group-point characterization is proved, rather than replacing it by
a small section neighborhood or an arbitrary automorphic-function set.
The actual normalized pullback supplies every inverse value globally.
No global analyticity or homeomorphism assertion is made here.
-/

public section
noncomputable section
set_option autoImplicit false

open Set Topology
open scoped UpperHalfPlane

namespace LowDimensionalTopology.Geometry.Teichmuller.NormalizedCoefficientTransport

open GammaMeasurableBeltrami

variable {Γ : Subgroup Deck}

/-- The entire actual Bers image of the original compatible coefficient ball. -/
def coefficientBersImage (hΓ : LiZhongQC.IsFuchsian Γ) : Set (BersWeighted.Automorphic Γ) :=
  range fun μ : Ball Γ => BersWeighted.automorphicProjection hΓ μ.val

/-- Membership in the entire Bers image means an actual compatible subunit coefficient. -/
theorem mem_coefficientBersImage_iff_coefficient (hΓ : LiZhongQC.IsFuchsian Γ)
    (φ : BersWeighted.Automorphic Γ) :
    φ ∈ coefficientBersImage hΓ ↔
      ∃ μ : Ball Γ, BersWeighted.automorphicProjection hΓ μ.val = φ := Iff.rfl

/-- This whole native image is precisely the original source group Bers image,
with its faithful canonical function and original coefficient classes. -/
theorem mem_coefficientBersImage_iff_sourcePoint (hΓ : LiZhongQC.IsFuchsian Γ)
    (φ : BersWeighted.Automorphic Γ) :
    φ ∈ coefficientBersImage hΓ ↔
      ∃ q : LiZhongQC.TeichGamma Γ, LiZhongQC.bersMapGamma Γ q = (φ.toSource : ℂ → ℂ) := by
  constructor
  · rintro ⟨μ, rfl⟩
    refine ⟨Quotient.mk _ (toSourceGamma μ), ?_⟩
    exact (bersProjection_eq μ).trans
      (BersWeighted.automorphicProjection_toSource_eq hΓ μ.val (mem_ball_zero_iff.mp μ.property)).symm
  · rintro ⟨q, hq⟩
    let μ := fromSourceGamma q.out
    refine ⟨μ, ?_⟩
    apply BersWeighted.Automorphic.toSource_injective
    apply Subtype.ext
    calc
      _ = LiZhongQC.bersFunction (toSourceGamma μ).val.val :=
        BersWeighted.automorphicProjection_toSource_eq hΓ μ.val (mem_ball_zero_iff.mp μ.property)
      _ = LiZhongQC.bersFunction q.out.val.val :=
        sourceBers_congr_ae (toSourceGamma μ) q.out (toSourceGamma_fromSourceGamma_ae q.out)
      _ = LiZhongQC.bersMapGamma Γ q := rfl
      _ = (φ.toSource : ℂ → ℂ) := hq

/-- Every original whole-domain value is also in the genuine universal image. -/
theorem coefficientBersImage_subset_universal (hΓ : LiZhongQC.IsFuchsian Γ) :
    coefficientBersImage hΓ ⊆ nativeUniversalBersImage Γ := by
  rintro _ ⟨μ, rfl⟩
  refine ⟨(toSourceGamma μ).val, ?_⟩
  exact (BersWeighted.automorphicProjection_toSource_eq hΓ μ.val
    (mem_ball_zero_iff.mp μ.property)).symm

/-- The actual normalized pullback lies in the full original coefficient ball. -/
def pulledBackBall (hΓ : LiZhongQC.IsFuchsian Γ) (ν : Ball Γ)
    (κ : Ball (deformedGroup hΓ ν)) : Ball Γ :=
  ⟨gammaPullback hΓ ν κ.val, by
    rw [Metric.mem_ball, dist_zero_right]
    change ‖pullback ν κ.val.val‖ < 1
    exact norm_pullback_lt_one ν κ.val.val⟩

/-- The ball transport retains the original normalized coefficient pullback. -/
theorem pulledBackBall_val (hΓ : LiZhongQC.IsFuchsian Γ) (ν : Ball Γ)
    (κ : Ball (deformedGroup hΓ ν)) :
    (pulledBackBall hΓ ν κ).val = gammaPullback hΓ ν κ.val := by
  rfl

/-- Actual translation cancels its normalized pullback for every target
coefficient in the entire unit ball, not only near the zero coefficient. -/
theorem gammaTranslation_pulledBackBall (hΓ : LiZhongQC.IsFuchsian Γ) (ν : Ball Γ)
    (κ : Ball (deformedGroup hΓ ν)) :
    gammaTranslation hΓ ν (pulledBackBall hΓ ν κ).val = κ.val := by
  apply Subtype.ext
  exact translation_pullback ν κ.val.val (Ball.norm_lt_one κ)

/-- The actual coordinate map sends the whole original Bers domain into the
whole domain for its exact normalized deformed group. -/
theorem bersTranslation_mapsTo_coefficientBersImage
    (hΓ : LiZhongQC.IsFuchsian Γ) (ν : Ball Γ) :
    MapsTo (bersTranslation hΓ ν) (coefficientBersImage hΓ)
      (coefficientBersImage (deformedGroup_spec hΓ ν).1) := by
  rintro _ ⟨μ, rfl⟩
  refine ⟨translatedBall hΓ ν μ, ?_⟩
  exact (bersTranslation_automorphicProjection hΓ ν μ).symm

/-- Every target Bers point has the original actual normalized pullback as a
preimage; no global surjectivity hypothesis or section-radius bound is used. -/
theorem bersTranslation_surjOn_coefficientBersImage
    (hΓ : LiZhongQC.IsFuchsian Γ) (ν : Ball Γ) :
    SurjOn (bersTranslation hΓ ν) (coefficientBersImage hΓ)
      (coefficientBersImage (deformedGroup_spec hΓ ν).1) := by
  rintro _ ⟨κ, rfl⟩
  let μ := pulledBackBall hΓ ν κ
  refine ⟨BersWeighted.automorphicProjection hΓ μ.val, ⟨μ, rfl⟩, ?_⟩
  rw [bersTranslation_automorphicProjection hΓ ν μ]
  change BersWeighted.automorphicProjection (deformedGroup_spec hΓ ν).1
      (gammaTranslation hΓ ν μ.val) = _
  exact congrArg (BersWeighted.automorphicProjection (deformedGroup_spec hΓ ν).1)
    (gammaTranslation_pulledBackBall hΓ ν κ)

/-- The genuine coordinate translation is bijective on the entire original
and target Bers domains, for their actual unchanged group data. -/
def coefficientBersTranslationEquiv (hΓ : LiZhongQC.IsFuchsian Γ) (ν : Ball Γ) :
    coefficientBersImage hΓ ≃ coefficientBersImage (deformedGroup_spec hΓ ν).1 := by
  let f : coefficientBersImage hΓ → coefficientBersImage (deformedGroup_spec hΓ ν).1 :=
    fun φ => ⟨bersTranslation hΓ ν φ.val,
      bersTranslation_mapsTo_coefficientBersImage hΓ ν φ.property⟩
  apply Equiv.ofBijective f
  constructor
  · intro φ ψ he
    apply Subtype.ext
    exact bersTranslation_injOn_nativeUniversalBersImage hΓ ν
      (coefficientBersImage_subset_universal hΓ φ.property)
      (coefficientBersImage_subset_universal hΓ ψ.property) (congrArg Subtype.val he)
  · intro ψ
    obtain ⟨φ, hφ, he⟩ := bersTranslation_surjOn_coefficientBersImage hΓ ν ψ.property
    exact ⟨⟨φ, hφ⟩, Subtype.ext he⟩

/-- The full-domain equivalence retains the literal actual coordinate translation. -/
theorem coefficientBersTranslationEquiv_apply
    (hΓ : LiZhongQC.IsFuchsian Γ) (ν : Ball Γ)
    (φ : coefficientBersImage hΓ) :
    (coefficientBersTranslationEquiv hΓ ν φ).val = bersTranslation hΓ ν φ.val := by
  rfl

/-- The global inverse is precisely the actual normalized coefficient
pullback after the original Bers projection, on every coefficient point. -/
theorem coefficientBersTranslationEquiv_symm_coefficient
    (hΓ : LiZhongQC.IsFuchsian Γ) (ν : Ball Γ) (κ : Ball (deformedGroup hΓ ν)) :
    ((coefficientBersTranslationEquiv hΓ ν).symm
      ⟨BersWeighted.automorphicProjection (deformedGroup_spec hΓ ν).1 κ.val, by
        change _ ∈ Set.range (fun μ : Ball (deformedGroup hΓ ν) =>
          BersWeighted.automorphicProjection (deformedGroup_spec hΓ ν).1 μ.val)
        exact Set.mem_range_self κ⟩).val =
      BersWeighted.automorphicProjection hΓ (pulledBackBall hΓ ν κ).val := by
  let e := coefficientBersTranslationEquiv hΓ ν
  let x : coefficientBersImage hΓ :=
    ⟨BersWeighted.automorphicProjection hΓ (pulledBackBall hΓ ν κ).val,
      by
        change _ ∈ Set.range (fun μ : Ball Γ => BersWeighted.automorphicProjection hΓ μ.val)
        exact Set.mem_range_self (pulledBackBall hΓ ν κ)⟩
  let y : coefficientBersImage (deformedGroup_spec hΓ ν).1 :=
    ⟨BersWeighted.automorphicProjection (deformedGroup_spec hΓ ν).1 κ.val, by
      change _ ∈ Set.range (fun μ : Ball (deformedGroup hΓ ν) =>
        BersWeighted.automorphicProjection (deformedGroup_spec hΓ ν).1 μ.val)
      exact Set.mem_range_self κ⟩
  have he : e x = y := by
    apply Subtype.ext
    change bersTranslation hΓ ν
      (BersWeighted.automorphicProjection hΓ (pulledBackBall hΓ ν κ).val) = _
    rw [bersTranslation_automorphicProjection]
    change BersWeighted.automorphicProjection (deformedGroup_spec hΓ ν).1
      (gammaTranslation hΓ ν (pulledBackBall hΓ ν κ).val) = _
    exact congrArg (BersWeighted.automorphicProjection (deformedGroup_spec hΓ ν).1)
      (gammaTranslation_pulledBackBall hΓ ν κ)
  exact congrArg Subtype.val (e.injective ((e.apply_symm_apply y).trans he.symm))

end LowDimensionalTopology.Geometry.Teichmuller.NormalizedCoefficientTransport
