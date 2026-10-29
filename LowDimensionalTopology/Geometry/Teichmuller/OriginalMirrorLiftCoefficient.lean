module

public import LowDimensionalTopology.Geometry.Teichmuller.OriginalMirroredMarked
public import LowDimensionalTopology.Geometry.Teichmuller.RawBersFixedReflection
public import LowDimensionalTopology.Geometry.Teichmuller.GeneralQCLiftCoefficientTransport

/-!
# The literal coefficient of the same mirrored marking

The actual covering is precomposed by the supplied minus-conjugation map.
Explicit reflected target charts give the literal reflected coefficient;
the existing biholomorphic identity adapter transfers it to the native atlas.
An AE coefficient equality is transported only when it is actually supplied.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Complex Set Filter MeasureTheory
open scoped Manifold ContDiff ComplexConjugate UpperHalfPlane

namespace LowDimensionalTopology.Geometry.Teichmuller.GeneralQC

open Surfaces LiZhongQC BersWeighted

/-- The same plane extension also agrees off the true domain, since sigma fixes I. -/
theorem originalMirror_pext_sigma {X : Type} (p : UpperHalfPlane → X)
    (σ : UpperHalfPlane ≃ₜ UpperHalfPlane)
    (hσ : ∀ τ, (σ τ : ℂ) = -conj (τ : ℂ)) (z : ℂ) :
    utm_pext (fun τ => p (σ τ)) z = utm_pext p (-conj z) := by
  have hσI : σ UpperHalfPlane.I = UpperHalfPlane.I := by
    apply UpperHalfPlane.ext
    rw [hσ]
    norm_num
  have him : (-conj z).im = z.im := by simp
  by_cases hz : 0 < z.im
  · have hz' : 0 < (-conj z).im := by rwa [him]
    rw [utm_pext, dite_eq_left hz, utm_pext, dite_eq_left hz']
    apply congrArg p
    apply UpperHalfPlane.ext
    exact hσ _
  · have hz' : ¬0 < (-conj z).im := by rwa [him]
    rw [utm_pext, dite_eq_right hz, utm_pext, dite_eq_right hz', hσI]

/-- This actual target/cover pair has the literal reflected lifted coefficient. -/
theorem originalMirror_liftCoeff_native {X : Type} [TopologicalSpace X]
    (S : LiZhongQC.ClosedRS.{0}) (p : UpperHalfPlane → X) (hp : Continuous p)
    (f : X ≃ₜ S.carrier) (σ : UpperHalfPlane ≃ₜ UpperHalfPlane)
    (hσ : ∀ τ, (σ τ : ℂ) = -conj (τ : ℂ)) :
    @s27u_liftCoeff X S.carrier S.topologicalSpace
        (originalMirrorNative S).toRiemannAtlas.toChartedSpace
        (fun τ => p (σ τ)) f =
      fun z => conj (@s27u_liftCoeff X S.carrier S.topologicalSpace
        S.chartedSpace p f (-conj z)) := by
  have hExplicit :
      @s27u_liftCoeff X S.carrier S.topologicalSpace (originalMirrorChartedSpace S)
          (fun τ => p (σ τ)) f =
        fun z => conj (@s27u_liftCoeff X S.carrier S.topologicalSpace
          S.chartedSpace p f (-conj z)) := by
    funext z
    by_cases hz : z ∈ upperHalf
    · have hz' : -conj z ∈ upperHalf := by
        simpa only [upperHalf, mem_ofPred_eq, neg_im, conj_im, neg_neg] using hz
      rw [@s27u_liftCoeff_of_mem X S.carrier S.topologicalSpace
        (originalMirrorChartedSpace S) (fun τ => p (σ τ)) f z hz,
        @s27u_liftCoeff_of_mem X S.carrier S.topologicalSpace S.chartedSpace p f
          (-conj z) hz']
      change complexDilatation
          (fun w => originalReflectedChart
            (S.chartedSpace.chartAt (f (utm_pext (fun τ => p (σ τ)) z)))
            (f (utm_pext (fun τ => p (σ τ)) w))) z =
        conj (complexDilatation
          (fun w => S.chartedSpace.chartAt (f (utm_pext p (-conj z)))
            (f (utm_pext p w))) (-conj z))
      simp only [originalReflectedChart_apply, originalMirror_pext_sigma p σ hσ]
      exact fixedBersReflectedPlaneFunction_dilatation
        (fun w => S.chartedSpace.chartAt (f (utm_pext p (-conj z)))
          (f (utm_pext p w))) z
    · have hz' : -conj z ∉ upperHalf := by
        simpa only [upperHalf, mem_ofPred_eq, neg_im, conj_im, neg_neg] using hz
      rw [@s27u_liftCoeff_of_not_mem X S.carrier S.topologicalSpace
        (originalMirrorChartedSpace S) (fun τ => p (σ τ)) f z hz,
        @s27u_liftCoeff_of_not_mem X S.carrier S.topologicalSpace S.chartedSpace p f
          (-conj z) hz', map_zero]
  have hNative :
      @s27u_liftCoeff X S.carrier S.topologicalSpace
          (originalMirrorNative S).toRiemannAtlas.toChartedSpace
          (fun τ => p (σ τ)) f =
        @s27u_liftCoeff X S.carrier S.topologicalSpace (originalMirrorChartedSpace S)
          (fun τ => p (σ τ)) f :=
    @liftCoeff_postcompose_biholomorphic
      X S.carrier S.carrier inferInstance S.topologicalSpace S.topologicalSpace
      (originalMirrorChartedSpace S) (originalMirrorNative S).toRiemannAtlas.toChartedSpace
      (originalMirror_isManifold S) (originalMirrorNative S).toRiemannAtlas.isManifold
      (fun τ => p (σ τ)) (hp.comp σ.continuous) f f.continuous
      (Homeomorph.refl S.carrier)
      (closedTarget_identity_biholomorphic (originalMirrorClosedRS S))
  exact hNative.trans hExplicit

/-- A supplied actual AE coefficient equality is carried to the same mirror marking. -/
theorem originalMirroredClosedMarked_liftCoeff_ae {X : Type} [TopologicalSpace X]
    (R : ClosedRiemannSurface X) (p : UpperHalfPlane → X) (hp : Continuous p)
    (σ : UpperHalfPlane ≃ₜ UpperHalfPlane)
    (hσ : ∀ τ, (σ τ : ℂ) = -conj (τ : ℂ)) (m : ClosedMarked R) (μ : ℂ → ℂ)
    (hμ : ∀ᵐ z ∂(volume.restrict upperHalf), s27u_liftCoeff p m.marking z = μ z) :
    ∀ᵐ z ∂(volume.restrict upperHalf),
      s27u_liftCoeff (fun τ => p (σ τ))
        (originalMirroredClosedMarked R m).marking z = conj (μ (-conj z)) := by
  have hcov := originalMirror_liftCoeff_native (closedTarget R m) p hp m.marking σ hσ
  rw [ae_restrict_iff' isOpen_upperHalf.measurableSet] at hμ ⊢
  filter_upwards [fixedBersReflection_measurePreserving.quasiMeasurePreserving.ae hμ]
    with z hz hzu
  have hσz : -conj z ∈ upperHalf := by
    simpa only [upperHalf, mem_ofPred_eq, neg_im, conj_im, neg_neg] using hzu
  change @s27u_liftCoeff X (closedTarget R m).carrier (closedTarget R m).topologicalSpace
      (originalMirrorNative (closedTarget R m)).toRiemannAtlas.toChartedSpace
      (fun τ => p (σ τ)) m.marking z = conj (μ (-conj z))
  exact (congrFun hcov z).trans (congrArg conj (hz hσz))

end LowDimensionalTopology.Geometry.Teichmuller.GeneralQC
