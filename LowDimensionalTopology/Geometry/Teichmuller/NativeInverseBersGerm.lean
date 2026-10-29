module

public import LowDimensionalTopology.Geometry.Teichmuller.NativeAhlforsWeillPullback

/-!
# Actual normalized inverse Bers germs and their scalar holomorphic families

The clipped rational coefficient is extended by zero off the upper half plane.
Its uniform pointwise bound and proved native pullback class give a genuine
compatible source coefficient. The inverse Bers germ is defined independently
by the actual normalized pullback followed by the actual Bers projection.
Their source values agree by the proved coefficient a.e. comparison.

A genuine holomorphic parameter curve in the full native weighted automorphic
space therefore gives an actual compatible coefficient family satisfying the
Ahlfors-Bers hypotheses, and the resulting inverse Bers germ is holomorphic at
every lower-half-plane point. No family holomorphy is added as a field.

The holomorphic-dependence theorem uses Wu Xiaobin's LiZhongQC development,
Apache-2.0, fixed upstream commit
`1c0d5473c020b66ed5106331a38a61536760b9b2`; see `THIRD_PARTY_NOTICES.md`.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set MeasureTheory Filter Topology
open scoped ENNReal UpperHalfPlane

namespace LowDimensionalTopology.Geometry.Teichmuller.NormalizedCoefficientTransport

open GammaMeasurableBeltrami

variable {Γ : Subgroup Deck}

/-- The literal pointwise holomorphic representative, zero off the upper half plane. -/
def inverseSectionPlane (hΓ : LiZhongQC.IsFuchsian Γ) (ν : Ball Γ)
    (φ : BersWeighted.Automorphic (deformedGroup hΓ ν)) (z : ℂ) : ℂ := by
  classical
  exact if hz : 0 < z.im then inverseSectionCoefficient hΓ ν φ ⟨z, hz⟩ else 0

@[simp] theorem inverseSectionPlane_coe (hΓ : LiZhongQC.IsFuchsian Γ) (ν : Ball Γ)
    (φ : BersWeighted.Automorphic (deformedGroup hΓ ν)) (z : ℍ) :
    inverseSectionPlane hΓ ν φ (z : ℂ) = inverseSectionCoefficient hΓ ν φ z := by
  exact dite_eq_left z.im_pos

theorem inverseSectionPlane_off (hΓ : LiZhongQC.IsFuchsian Γ) (ν : Ball Γ)
    (φ : BersWeighted.Automorphic (deformedGroup hΓ ν)) {z : ℂ} (hz : ¬0 < z.im) :
    inverseSectionPlane hΓ ν φ z = 0 := by
  exact dite_eq_right hz

/-- The actual upper-half-plane null-class equivalence proves planar measurability. -/
theorem inverseSectionPlane_aestronglyMeasurable (hΓ : LiZhongQC.IsFuchsian Γ)
    (ν : Ball Γ) (φ : BersWeighted.Automorphic (deformedGroup hΓ ν)) :
    AEStronglyMeasurable (inverseSectionPlane hΓ ν φ) (volume : Measure ℂ) := by
  have hr : AEStronglyMeasurable (inverseSectionPlane hΓ ν φ)
      (volume.restrict LiZhongQC.upperHalf) := by
    apply aestronglyMeasurable_plane_iff.mpr
    simpa only [inverseSectionPlane_coe] using
      inverseSectionCoefficient_aestronglyMeasurable hΓ ν φ
  have he : LiZhongQC.upperHalf.indicator (inverseSectionPlane hΓ ν φ) =
      inverseSectionPlane hΓ ν φ := by
    funext z
    by_cases hz : z ∈ LiZhongQC.upperHalf
    · exact indicator_of_mem hz _
    · rw [indicator_of_notMem hz, inverseSectionPlane_off hΓ ν φ hz]
  rw [← he]
  exact (aestronglyMeasurable_indicator_iff LiZhongQC.isOpen_upperHalf.measurableSet).mpr hr

/-- The same strict bound holds at every planar point, including the zero extension. -/
theorem norm_inverseSectionPlane_le (hΓ : LiZhongQC.IsFuchsian Γ) (ν : Ball Γ)
    (φ : BersWeighted.Automorphic (deformedGroup hΓ ν))
    (hφ : ‖φ‖ < inverseSectionRadius ν) (z : ℂ) :
    ‖inverseSectionPlane hΓ ν φ z‖ ≤ inverseSectionBound ν := by
  by_cases hz : 0 < z.im
  · rw [inverseSectionPlane, dite_eq_left hz]
    exact norm_inverseSectionCoefficient_le hΓ ν φ hφ _
  · rw [inverseSectionPlane_off hΓ ν φ hz, norm_zero]
    exact inverseSectionBound_nonneg ν

/-- A genuine globally measurable subunit source coefficient. -/
theorem inverseSectionPlane_isBeltramiCoeff (hΓ : LiZhongQC.IsFuchsian Γ) (ν : Ball Γ)
    (φ : BersWeighted.Automorphic (deformedGroup hΓ ν))
    (hφ : ‖φ‖ < inverseSectionRadius ν) :
    LiZhongQC.IsBeltramiCoeff (inverseSectionPlane hΓ ν φ) univ (inverseSectionBound ν) := by
  rw [LiZhongQC.IsBeltramiCoeff, Measure.restrict_univ]
  exact ⟨inverseSectionPlane_aestronglyMeasurable hΓ ν φ,
    Eventually.of_forall (norm_inverseSectionPlane_le hΓ ν φ hφ)⟩

/-- The planar representative is exactly the original native pullback class a.e. -/
theorem inverseSectionPlane_ae (hΓ : LiZhongQC.IsFuchsian Γ) (ν : Ball Γ)
    (φ : BersWeighted.Automorphic (deformedGroup hΓ ν))
    (hφ : ‖φ‖ < inverseSectionRadius ν) :
    inverseSectionPlane hΓ ν φ =ᵐ[volume.restrict LiZhongQC.upperHalf]
      planeRepresentative (gammaPullback hΓ ν (BersWeighted.ahlforsWeill φ)).val := by
  apply ae_plane_iff.mpr
  filter_upwards [pullback_ahlforsWeill_coe_ae hΓ ν φ hφ] with z hz
  simpa only [inverseSectionPlane_coe, planeRepresentative_coe, gammaPullback_val] using hz.symm

/-- Compatibility follows from the actual native pullback, transported through its true a.e. law. -/
theorem inverseSectionPlane_compatible (hΓ : LiZhongQC.IsFuchsian Γ) (ν : Ball Γ)
    (φ : BersWeighted.Automorphic (deformedGroup hΓ ν))
    (hφ : ‖φ‖ < inverseSectionRadius ν) :
    LiZhongQC.IsGammaCompatible Γ (inverseSectionPlane hΓ ν φ) := by
  let μ := gammaPullback hΓ ν (BersWeighted.ahlforsWeill φ)
  have he : ∀ᵐ z : ℍ ∂volume, inverseSectionPlane hΓ ν φ z = μ.val z := by
    simpa only [planeRepresentative_coe] using ae_plane_iff.mp (inverseSectionPlane_ae hΓ ν φ hφ)
  intro γ hγ
  apply ae_plane_iff.mpr
  filter_upwards [he, (measurePreserving_deck γ).quasiMeasurePreserving.ae he,
    (mem_compatibleSubmodule_iff μ.val).mp μ.property γ hγ] with z hz hγz hnative
  have hm : inverseSectionPlane hΓ ν φ ((γ • z : ℍ) : ℂ) =
      inverseSectionPlane hΓ ν φ
        (((γ 0 0 : ℂ) * z + γ 0 1) / ((γ 1 0 : ℂ) * z + γ 1 1)) := by
    rw [LiZhongQC.h23l_b_coe_smul]
  rw [← hm]
  change inverseSectionPlane hΓ ν φ z = inverseSectionPlane hΓ ν φ ((γ • z : ℍ) : ℂ) * phase γ z
  rw [hz, hγz]
  simpa only [mul_comm] using hnative

/-- The actual pointwise holomorphic coefficient packaged in the genuine source Gamma ball. -/
def inverseSectionSource (hΓ : LiZhongQC.IsFuchsian Γ) (ν : Ball Γ)
    (φ : BersWeighted.Automorphic (deformedGroup hΓ ν))
    (hφ : ‖φ‖ < inverseSectionRadius ν) : LiZhongQC.BeltramiGamma Γ :=
  ⟨⟨inverseSectionPlane hΓ ν φ,
    ⟨⟨inverseSectionBound ν, inverseSectionBound_nonneg ν, inverseSectionBound_lt_one ν,
      inverseSectionPlane_isBeltramiCoeff hΓ ν φ hφ⟩,
      fun _ hz => inverseSectionPlane_off hΓ ν φ (not_lt.mpr hz)⟩⟩,
    inverseSectionPlane_compatible hΓ ν φ hφ⟩

/-- The inverse coordinate germ is independently the actual normalized pullback and Bers value. -/
def inverseBersGerm (hΓ : LiZhongQC.IsFuchsian Γ) (ν : Ball Γ)
    (φ : BersWeighted.Automorphic (deformedGroup hΓ ν)) : BersWeighted.Automorphic Γ :=
  BersWeighted.automorphicProjection hΓ (gammaPullback hΓ ν (BersWeighted.ahlforsWeill φ))

/-- Its full canonically extended source function agrees with the actual holomorphic family. -/
theorem inverseBersGerm_source (hΓ : LiZhongQC.IsFuchsian Γ) (ν : Ball Γ)
    (φ : BersWeighted.Automorphic (deformedGroup hΓ ν))
    (hφ : ‖φ‖ < inverseSectionRadius ν) :
    ((inverseBersGerm hΓ ν φ).toSource : ℂ → ℂ) =
      LiZhongQC.bersFunction (inverseSectionSource hΓ ν φ hφ).val.val := by
  have hμ : ‖gammaPullback hΓ ν (BersWeighted.ahlforsWeill φ)‖ < 1 := by
    change ‖pullback ν (BersWeighted.ahlforsWeill φ).val‖ < 1
    exact norm_pullback_lt_one ν _
  let μB : Ball Γ :=
    ⟨gammaPullback hΓ ν (BersWeighted.ahlforsWeill φ), by
      simpa only [Metric.mem_ball, dist_zero_right] using hμ⟩
  have he : ((inverseBersGerm hΓ ν φ).toSource : ℂ → ℂ) = bersProjection μB := by
    change BersWeighted.decode
      (BersWeighted.projection (gammaPullback hΓ ν (BersWeighted.ahlforsWeill φ))) = _
    rw [BersWeighted.projection, dite_eq_left hμ]
    exact BersWeighted.decode_projectionValue μB
  have hs := sourceBers_congr_ae (toSourceGamma μB) (inverseSectionSource hΓ ν φ hφ)
    (inverseSectionPlane_ae hΓ ν φ hφ).symm
  calc
    _ = bersProjection μB := he
    _ = _ := by
      rw [bersProjection_eq]
      exact hs

/-- A globally valid source family, equal to the actual section on its true small ball. -/
def inverseSectionFamily (hΓ : LiZhongQC.IsFuchsian Γ) (ν : Ball Γ)
    (q : ℂ → BersWeighted.Automorphic (deformedGroup hΓ ν)) (t : ℂ) :
    LiZhongQC.BeltramiGamma Γ := by
  classical
  exact if ht : ‖q t‖ < inverseSectionRadius ν then inverseSectionSource hΓ ν (q t) ht
    else toSourceGamma ν

theorem inverseSectionFamily_coefficient (hΓ : LiZhongQC.IsFuchsian Γ) (ν : Ball Γ)
    (q : ℂ → BersWeighted.Automorphic (deformedGroup hΓ ν)) {t : ℂ}
    (ht : ‖q t‖ < inverseSectionRadius ν) :
    (inverseSectionFamily hΓ ν q t).val.val = inverseSectionPlane hΓ ν (q t) := by
  rw [inverseSectionFamily, dite_eq_left ht]
  rfl

/-- Actual parameter differentiability gives pointwise holomorphy of the genuine source family. -/
theorem inverseSectionFamily_holomorphic (hΓ : LiZhongQC.IsFuchsian Γ) (ν : Ball Γ)
    {P : Set ℂ} (q : ℂ → BersWeighted.Automorphic (deformedGroup hΓ ν))
    (hq : DifferentiableOn ℂ q P) (hbound : ∀ t ∈ P, ‖q t‖ < inverseSectionRadius ν) :
    ∀ z : ℂ, DifferentiableOn ℂ (fun t => (inverseSectionFamily hΓ ν q t).val.val z) P := by
  intro z
  have hraw : DifferentiableOn ℂ (fun t => inverseSectionPlane hΓ ν (q t) z) P := by
    intro t ht
    by_cases hz : 0 < z.im
    · have hd := (differentiableAt_inverseSectionCoefficient hΓ ν (q t)
        (hbound t ht) (⟨z, hz⟩ : ℍ)).comp_differentiableWithinAt t (hq t ht)
      apply hd.congr
      · intro u _
        simp only [inverseSectionPlane, dite_eq_left hz, Function.comp_apply]
      · simp only [inverseSectionPlane, dite_eq_left hz, Function.comp_apply]
    · simpa only [inverseSectionPlane, dite_eq_right hz] using
        (differentiableWithinAt_const (c := (0 : ℂ)) :
          DifferentiableWithinAt ℂ (fun _ : ℂ => (0 : ℂ)) P t)
  exact hraw.congr fun t ht => congrFun (inverseSectionFamily_coefficient hΓ ν q (hbound t ht)) z

/-- Every planar point has the same actual strict subunit family bound. -/
theorem inverseSectionFamily_bound (hΓ : LiZhongQC.IsFuchsian Γ) (ν : Ball Γ)
    {P : Set ℂ} (q : ℂ → BersWeighted.Automorphic (deformedGroup hΓ ν))
    (hbound : ∀ t ∈ P, ‖q t‖ < inverseSectionRadius ν) :
    ∀ t ∈ P, ∀ z : ℂ, ‖(inverseSectionFamily hΓ ν q t).val.val z‖ ≤ inverseSectionBound ν := by
  intro t ht z
  rw [inverseSectionFamily_coefficient hΓ ν q (hbound t ht)]
  exact norm_inverseSectionPlane_le hΓ ν (q t) (hbound t ht) z

/-- The true Ahlfors-Bers theorem proves scalar holomorphy of the actual inverse Bers germ. -/
theorem inverseBersGerm_scalar_differentiableOn (hΓ : LiZhongQC.IsFuchsian Γ) (ν : Ball Γ)
    {P : Set ℂ} (hP : IsOpen P) (q : ℂ → BersWeighted.Automorphic (deformedGroup hΓ ν))
    (hq : DifferentiableOn ℂ q P) (hbound : ∀ t ∈ P, ‖q t‖ < inverseSectionRadius ν)
    {z : ℂ} (hz : z ∈ LiZhongQC.lowerHalf) :
    DifferentiableOn ℂ (fun t => ((inverseBersGerm hΓ ν (q t)).toSource : ℂ → ℂ) z) P := by
  have hs := LiZhongQC.bers_holomorphic_dependence hΓ hP
    (μ := inverseSectionFamily hΓ ν q) (inverseSectionFamily_holomorphic hΓ ν q hq hbound)
    (inverseSectionBound_lt_one ν) (inverseSectionFamily_bound hΓ ν q hbound) z hz
  apply hs.congr
  intro t ht
  rw [LiZhongQC.bersFunctionGamma, inverseSectionFamily_coefficient hΓ ν q (hbound t ht)]
  exact congrFun (inverseBersGerm_source hΓ ν (q t) (hbound t ht)) z

end LowDimensionalTopology.Geometry.Teichmuller.NormalizedCoefficientTransport
