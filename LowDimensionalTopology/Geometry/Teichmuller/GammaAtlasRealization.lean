module

public import LowDimensionalTopology.Geometry.Teichmuller.GammaMeasurableBeltrami
public import Mathlib.Tactic.Linarith

/-!
# Realization with the original measurable coefficient bound

The actual uniformizing construction retains K=(1+k)/(1-k), so its genuine
marking has preferred-chart Beltrami tensor bounded by exactly k. The coefficient
lift agrees almost everywhere with the given compatible raw coefficient.
This statement concerns the actual preferred chartAt family; it does not assert
an equivalence with all raw families on every original-atlas chart.
-/

@[expose] public section
noncomputable section

open Set MeasureTheory
open scoped UpperHalfPlane Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller.GammaMeasurableBeltrami

open Surfaces
open LiZhongQC

universe u

/-- The genuine marked realization retains the original coefficient bound. -/
theorem exists_marked_atlas_tensor_with_bound {X : Type u} [TopologicalSpace X]
    (R : ClosedRiemannSurface X) {Γ : Subgroup Deck} {p₀ : ℍ → X}
    (hp₀ : let := R.toRiemannAtlas.toChartedSpace; IsUniformization Γ p₀)
    {μ : ℂ → ℂ} {k : ℝ} (hk₀ : 0 ≤ k) (hk : k < 1)
    (hμ : IsBeltramiCoeff μ upperHalf k) (hΓ : IsGammaCompatible Γ μ) :
    let := R.toRiemannAtlas.toChartedSpace
    ∃ m : MarkedRS X,
      IsKQCRS m.marking ((1 + k) / (1 - k)) ∧
      (s27u_liftCoeff p₀ m.marking =ᵐ[volume.restrict upperHalf] μ) ∧
      IsBeltramiDifferential (markingAtlasCoefficient m) k := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  let := R.t2Space
  let := R.connectedSpace
  let := R.compactSpace
  obtain ⟨-, hN, hwK, -⟩ := s27u_sym_spec hk₀ hk hμ
  obtain ⟨hwU, -, -, hwKU, hwd⟩ := s27u_fSym_upperHalf hk₀ hk hμ
  obtain ⟨F, hF⟩ := s27u_homeo_upper hwK hN.2.1 hwU
  obtain ⟨Y, e, hhol⟩ := s27v_xmu_exists hp₀ hk₀ hk hμ hΓ hF
  have hU := s27v_isUniformization hp₀ hk₀ hk hμ hΓ hF e hhol
  have hL : IsLift p₀ (s27u_proj p₀ e F) e F := fun τ => by
    change e (p₀ (F.symm (F τ))) = e (p₀ τ)
    rw [F.symm_apply_apply]
  have hFeq : EqOn (liftToC F) (s27u_fSym μ) upperHalf := fun z hz => by
    rw [h23l_liftToC_eq F hz, UpperHalfPlane.ofComplex_apply_of_im_pos
      (show 0 < z.im from hz)]
    exact hF _
  let K : ℝ := (1 + k) / (1 - k)
  have hFK : IsKQC (liftToC F) upperHalf K := ad_isKQC_congr hwKU hFeq
  have hK : IsKQCRS e K := s27v_isKQCRS_of_lift hp₀ hU hL hFK
  let m : MarkedRS X := ⟨Y, e, ⟨K, hK⟩⟩
  have hbound : (K - 1) / (K + 1) = k := by
    have hKplus : K + 1 ≠ 0 := by linarith [hK.1]
    apply (div_eq_iff hKplus).2
    have hden : 1 - k ≠ 0 := by linarith
    have heq : K * (1 - k) = 1 + k := div_mul_cancel₀ _ hden
    nlinarith
  refine ⟨m, hK, ?_, ?_⟩
  · filter_upwards [hwd, ae_restrict_mem isOpen_upperHalf.measurableSet] with z h1 hz
    change s27u_liftCoeff p₀ e z = μ z
    rw [← s27u_liftCoeff_eq_dilatation hp₀ hU hL hz, ← h1]
    exact abR_t_complexDilatation_congr isOpen_upperHalf hFeq hz
  · rw [← hbound]
    exact eq23_1_beltrami_differential
      (f := m.marking) (show IsKQCRS m.marking K from hK)

/-- The actual compatible L-infinity class realizes a tensor bounded by its
own intrinsic class norm, retaining that bound through the construction. -/
theorem exists_marked_atlas_tensor_normBound {X : Type u} [TopologicalSpace X]
    (R : ClosedRiemannSurface X) {Γ : Subgroup Deck} {p₀ : ℍ → X}
    (hp₀ : let := R.toRiemannAtlas.toChartedSpace; IsUniformization Γ p₀)
    (μ : Ball Γ) :
    let := R.toRiemannAtlas.toChartedSpace
    ∃ m : MarkedRS X,
      IsKQCRS m.marking ((1 + ‖μ.val.val‖) / (1 - ‖μ.val.val‖)) ∧
      (s27u_liftCoeff p₀ m.marking =ᵐ[volume.restrict upperHalf]
        planeRepresentative μ.val.val) ∧
      IsBeltramiDifferential (markingAtlasCoefficient m) ‖μ.val.val‖ := by
  exact exists_marked_atlas_tensor_with_bound R hp₀ (norm_nonneg μ.val.val)
    (Ball.norm_lt_one μ) (planeRepresentative_isBeltramiCoeff μ.val.val)
    (planeRepresentative_isGammaCompatible μ.val)

end LowDimensionalTopology.Geometry.Teichmuller.GammaMeasurableBeltrami
