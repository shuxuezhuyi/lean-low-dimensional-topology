module

public import LowDimensionalTopology.Geometry.Surfaces.Euclidean.OriginalTorusGeneratorMarkings
public import LowDimensionalTopology.Geometry.Teichmuller.Space
public import LowDimensionalTopology.Geometry.Teichmuller.SmoothBeltrami

/-!
# Supporting data for the original genus-one marked quotient

The period change descends through the existing analytic torus coverings.
The descended homeomorphism uses the original models and their exact fibres.
Actual smooth oriented markings define points of the original marked quotient.
The original marking relation retains its common based-loop transport data.
Beltrami cover coefficients retain the actual chart derivative phase.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set Module
open scoped UpperHalfPlane ComplexConjugate

namespace LowDimensionalTopology.Geometry.Teichmuller.GenusOne
open Surfaces

/-- The real linear period change on the original covering plane. -/
def periodChange (τ σ : ℍ) : ℂ ≃L[ℝ] ℂ :=
  (normalizedTorusBasis τ).equivFunL.trans (normalizedTorusBasis σ).equivFunL.symm

theorem periodChange_coordinates (τ σ : ℍ) (z : ℂ) :
    (normalizedTorusBasis σ).equivFun (periodChange τ σ z) =
      (normalizedTorusBasis τ).equivFun z := by
  change (normalizedTorusBasis σ).equivFunL
    ((normalizedTorusBasis σ).equivFunL.symm
      ((normalizedTorusBasis τ).equivFunL z)) = _
  exact (normalizedTorusBasis σ).equivFunL.apply_symm_apply _

theorem periodChange_lattice_iff (τ σ : ℍ) (z : ℂ) :
    z ∈ Submodule.span ℤ (Set.range (normalizedTorusBasis τ)) ↔
      periodChange τ σ z ∈ Submodule.span ℤ (Set.range (normalizedTorusBasis σ)) := by
  rw [complexIntegerSpan_mem_iff_coordinates, complexIntegerSpan_mem_iff_coordinates,
    periodChange_coordinates]

theorem periodChange_inverse (τ σ : ℍ) (z : ℂ) :
    periodChange σ τ (periodChange τ σ z) = z := by
  change (normalizedTorusBasis τ).equivFunL.symm
    ((normalizedTorusBasis σ).equivFunL
      ((normalizedTorusBasis σ).equivFunL.symm
        ((normalizedTorusBasis τ).equivFunL z))) = z
  rw [ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearEquiv.symm_apply_apply]

/-- Descent of the specified period change to the existing actual torus carriers.
This is only the topological part; it does not assert analyticity of a real affine map. -/
theorem exists_periodChange_homeomorph (τ σ : ℍ) :
    ∃ f : ComplexTorusCarrier ≃ₜ ComplexTorusCarrier,
      ∀ z : ℂ, f ((normalizedTorusModel τ).projection z) =
        (normalizedTorusModel σ).projection (periodChange τ σ z) := by
  let T := normalizedTorusModel τ
  let U := normalizedTorusModel σ
  have hfiber (z w : ℂ) : T.projection z = T.projection w ↔
      U.projection (periodChange τ σ z) = U.projection (periodChange τ σ w) := by
    rw [T.fiber_iff, U.fiber_iff, ← map_sub]
    exact periodChange_lattice_iff τ σ (z - w)
  let f : ComplexTorusCarrier → ComplexTorusCarrier := fun x =>
    U.projection (periodChange τ σ (Function.surjInv T.surjective x))
  have hcomm (z : ℂ) : f (T.projection z) = U.projection (periodChange τ σ z) :=
    (hfiber _ _).mp (Function.surjInv_eq T.surjective (T.projection z))
  have hfc : Continuous f := by
    apply (T.covering.isQuotientMap T.surjective).continuous_iff.mpr
    have he : f ∘ T.projection = U.projection ∘ periodChange τ σ := funext hcomm
    rw [he]
    exact U.covering.continuous.comp (periodChange τ σ).continuous
  let g : ComplexTorusCarrier → ComplexTorusCarrier := fun x =>
    T.projection (periodChange σ τ (Function.surjInv U.surjective x))
  have hcommInv (z : ℂ) : g (U.projection z) = T.projection (periodChange σ τ z) := by
    apply (T.fiber_iff _ _).mpr
    have hz := (U.fiber_iff _ _).mp
      (Function.surjInv_eq U.surjective (U.projection z))
    have hΛ := (periodChange_lattice_iff σ τ _).mp hz
    simpa only [map_sub] using hΛ
  have hgc : Continuous g := by
    apply (U.covering.isQuotientMap U.surjective).continuous_iff.mpr
    have he : g ∘ U.projection = T.projection ∘ periodChange σ τ := funext hcommInv
    rw [he]
    exact T.covering.continuous.comp (periodChange σ τ).continuous
  refine ⟨⟨⟨f, g, ?_, ?_⟩, hfc, hgc⟩, hcomm⟩
  · intro x
    obtain ⟨z, rfl⟩ := T.surjective x
    rw [hcomm, hcommInv, periodChange_inverse]
  · intro x
    obtain ⟨z, rfl⟩ := U.surjective x
    rw [hcommInv, hcomm, periodChange_inverse]

/-- A genuine oriented smooth marking into an actual normalized torus is an
original marked surface, on the original carrier and complex atlas. -/
def markedNormalizedTorus {X : Type} [TopologicalSpace X]
    (R : ClosedRiemannSurface X) (τ : ℍ)
    (f : SmoothSurfaceEquiv R.toRiemannSurface (normalizedTorusModel τ).surface)
    (hf : PreservesComplexOrientation R.toRiemannAtlas
      (normalizedTorusModel τ).surface.toRiemannAtlas f.toHomeomorph) :
    MarkedRiemannSurface.{0, 0} R where
  carrier := ComplexTorusCarrier
  topology := inferInstance
  surface := normalizedClosedTorus τ
  marking := f
  orientation_preserving := hf

/-- The actual original quotient point, given the genuine marking above. -/
def originalTorusPoint {X : Type} [TopologicalSpace X]
    (R : ClosedRiemannSurface X) (τ : ℍ)
    (f : SmoothSurfaceEquiv R.toRiemannSurface (normalizedTorusModel τ).surface)
    (hf : PreservesComplexOrientation R.toRiemannAtlas
      (normalizedTorusModel τ).surface.toRiemannAtlas f.toHomeomorph) :
    TeichmullerSpace.{0, 0} R :=
  TeichmullerSpace.mk (markedNormalizedTorus R τ f hf)

/-- The actual generator relation is the equality relation in the
existing original quotient. No new generator-marked quotient is introduced. -/
theorem original_mk_eq_iff_generator_marked {X : Type} [TopologicalSpace X]
    (R : ClosedRiemannSurface X) (hR : R.HasGenus 1)
    (x : X) (sigma : Fin 2 → FundamentalGroup X x)
    (hgen : Subgroup.closure (Set.range sigma) = ⊤)
    (M N : MarkedRiemannSurface.{0, 0} R) :
    TeichmullerSpace.mk M = TeichmullerSpace.mk N ↔
      GeneratorMarkedTargetsEquivalent M.surface.toRiemannSurface N.surface.toRiemannSurface
        M.marking.toHomeomorph N.marking.toHomeomorph x sigma := by
  rw [TeichmullerSpace.mk_eq_mk_iff]
  have hN : HasTopologicalGenus N.carrier 1 := by
    obtain ⟨er⟩ := hR
    exact ⟨N.marking.toHomeomorph.symm.trans er⟩
  change (∃ h : M.carrier ≃ₜ N.carrier,
    RiemannAnalyticMap M.surface.toRiemannAtlas N.surface.toRiemannAtlas h ∧
      ContinuousMap.Homotopic ((_root_.toContinuousMap h).comp M.markingMap) N.markingMap) ↔ _
  unfold GeneratorMarkedTargetsEquivalent
  apply exists_congr
  intro h
  apply and_congr_right
  intro _hh
  exact R.toRiemannSurface.torus_homotopic_iff_generator_transport
    N.surface.toRiemannSurface hR hN
    ((_root_.toContinuousMap h).comp M.markingMap) N.markingMap x sigma hgen

/-- Pull the actual atlas Beltrami tensor to the original plane cover.
The transition derivative is essential: the tensor is not a scalar on the torus. -/
def torusCoverBeltramiValue (τ : ℍ)
    (μ : BeltramiDifferential (normalizedTorusModel τ).surface.toRiemannAtlas)
    (z : ℂ) : ℂ :=
  let A := (normalizedTorusModel τ).surface.toRiemannAtlas
  let p := (normalizedTorusModel τ).projection
  let c := A.cover (p z)
  let e : BeltramiDifferential.Chart A := ⟨c.choose, c.choose_spec.1⟩
  μ.coeff e ⟨e.val (p z), e.val.map_source c.choose_spec.2⟩ *
    conj (deriv (e.val ∘ p) z) / deriv (e.val ∘ p) z

end LowDimensionalTopology.Geometry.Teichmuller.GenusOne
