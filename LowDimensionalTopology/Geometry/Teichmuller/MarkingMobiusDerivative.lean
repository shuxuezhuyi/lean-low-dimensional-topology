module

public import LowDimensionalTopology.Geometry.Teichmuller.MarkingMobiusRecentring
public import LowDimensionalTopology.Geometry.Teichmuller.NativeBersTranslationGlobalAnalytic
public import Mathlib.Analysis.Calculus.FDeriv.Congr

/-! The genuine derivative and ambient harmonic law of marking recentering. -/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set Filter Topology
open scoped UpperHalfPlane Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
open Surfaces GammaMeasurableBeltrami BersWeighted NormalizedCoefficientTransport
variable {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {Γ : Subgroup Deck} {p : ℍ → X}
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g) (hΓ : LiZhongQC.IsFuchsian Γ)

/-- Every original QC normalizer has the full nonlinear square, its actual
Fréchet derivative, and the literal AW coefficient pullback by the same α⁻¹.
All normalizations are obtained from the original marking data. -/
theorem exists_upperMarkingBersDerivativeAndHarmonicLaw :
    letI := R.toRiemannAtlas.toChartedSpace
    letI := R.toRiemannAtlas.isManifold
    letI := R.t2Space
    letI := R.connectedSpace
    ∀ w : QCNormalizerModular.Normalizer hp,
      let f := QCNormalizerModular.descendedAut hp w.val w.property
      let hw := QCNormalizerModular.descendedAut_isLift hp w.val w.property
      ∃ (ρ : Ball Γ) (N₀ : Deck)
        (hN₀ : ∀ z : ℍ, normalizedUpperEquiv ρ z = N₀ • w.val z),
        ∀ ν : Ball Γ,
          let ν' := givenReferenceChangedBall hp hp hΓ f.val w.val hw ρ N₀ hN₀ ν
          ∃ (α : Deck) (hα : ∀ z : ℍ, normalizedUpperEquiv ν' z =
              α • normalizedUpperEquiv ν (w.val.symm z)),
            let G := givenReferenceBersMap hp hp hΓ f.val w.val hw ρ N₀ hN₀
            let J := markingRecentringIsometry hΓ w.val w.property ν ν' α hα
            let Eν := inverseBersDerivativeEquiv R hp hg hgenus hΓ ν
            let Eν' := inverseBersDerivativeEquiv R hp hg hgenus hΓ ν'
            (∀ (φ : Automorphic Γ) (_hφ : φ ∈ coefficientBersImage hΓ),
              bersTranslation hΓ ν' (G φ) = J (bersTranslation hΓ ν φ)) ∧
            (Eν').symm.toContinuousLinearMap.comp
                (fderiv ℂ G (baseBersValue hΓ ν)) =
              J.toContinuousLinearEquiv.toContinuousLinearMap.comp
                Eν.symm.toContinuousLinearMap ∧
            ∀ v : Automorphic Γ,
              (ahlforsWeill ((Eν').symm (fderiv ℂ G (baseBersValue hΓ ν) v))).val =
                pullback α⁻¹ (ahlforsWeill (Eν.symm v)).val := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  let := R.t2Space
  let := R.connectedSpace
  intro w
  let f := QCNormalizerModular.descendedAut hp w.val w.property
  let hw := QCNormalizerModular.descendedAut_isLift hp w.val w.property
  obtain ⟨ρ, N₀, hN₀, hrec⟩ := exists_upperMarkingBersRecentring R hp hg hgenus hΓ w
  refine ⟨ρ, N₀, hN₀, ?_⟩
  intro ν
  let ν' := givenReferenceChangedBall hp hp hΓ f.val w.val hw ρ N₀ hN₀ ν
  obtain ⟨α, hα, hn⟩ := hrec ν
  let G := givenReferenceBersMap hp hp hΓ f.val w.val hw ρ N₀ hN₀
  let J := markingRecentringIsometry hΓ w.val w.property ν ν' α hα
  let Eν := inverseBersDerivativeEquiv R hp hg hgenus hΓ ν
  let Eν' := inverseBersDerivativeEquiv R hp hg hgenus hΓ ν'
  let b := baseBersValue hΓ ν
  have hmem : b ∈ coefficientBersImage hΓ :=
    (mem_coefficientBersImage_iff_coefficient hΓ b).mpr ⟨ν, rfl⟩
  have hcenter : G b = baseBersValue hΓ ν' := by
    exact givenReferenceBersMap_projection hp hp hΓ hΓ f.val w.val hw ρ N₀ hN₀ ν
  have hG : DifferentiableAt ℂ G b :=
    ((givenReferenceBersMap_analytic_bothDirections R R hg hgenus hΓ hΓ hp hp
      f.val w.val hw ρ N₀ hN₀).1 b hmem).differentiableAt
  have hν' : HasFDerivAt (bersTranslation hΓ ν') Eν'.symm.toContinuousLinearMap (G b) := by
    rw [hcenter]
    exact hasFDerivAt_bersTranslation R hp hg hgenus hΓ ν'
  have hleft := hν'.comp b hG.hasFDerivAt
  have hright := J.toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt.comp b
    (hasFDerivAt_bersTranslation R hp hg hgenus hΓ ν)
  have heq :
      (fun φ : Automorphic Γ => bersTranslation hΓ ν' (G φ)) =ᶠ[𝓝 b]
        (fun φ : Automorphic Γ => J (bersTranslation hΓ ν φ)) := by
    filter_upwards [(isOpen_coefficientBersImage R hp hg hgenus hΓ).mem_nhds hmem]
      with φ hφ
    exact hn φ hφ
  have hd : Eν'.symm.toContinuousLinearMap.comp (fderiv ℂ G b) =
      J.toContinuousLinearEquiv.toContinuousLinearMap.comp Eν.symm.toContinuousLinearMap :=
    (hleft.congr_of_eventuallyEq heq.symm).unique hright
  refine ⟨α, hα, hn, hd, ?_⟩
  intro v
  let φ := Eν.symm v
  let ψ := Eν'.symm (fderiv ℂ G b v)
  have hv : ψ = J φ := by
    exact congrArg
      (fun L : Automorphic Γ →L[ℂ] Automorphic (deformedGroup hΓ ν') => L v) hd
  have hs : (ψ.toSource : ℂ → ℂ) = realMobiusPullback α⁻¹ (φ.toSource : ℂ → ℂ) :=
    (congrArg (fun q : Automorphic (deformedGroup hΓ ν') => (q.toSource : ℂ → ℂ)) hv).trans
      (markingRecentringIsometry_toSource hΓ w.val w.property ν ν' α hα φ)
  exact ahlforsWeill_realMobiusPullback α⁻¹ φ ψ hs

end LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
