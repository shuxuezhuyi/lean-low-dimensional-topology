module

public import LowDimensionalTopology.Geometry.Teichmuller.SmoothBeltrami
public import LowDimensionalTopology.Geometry.Teichmuller.BeltramiCompactBounds
public import LowDimensionalTopology.Geometry.Surfaces.Riemann.Closed
public import Mathlib.Topology.Order.Compact

/-!
# The literal maximal dilatation on a fixed compact original surface

Use the actual smooth map's continuous Beltrami tensor, its intrinsic absolute
value, and the literal supremum over all original points. Compactness proves
that this supremum is attained and gives precisely the book's formula (1.7).
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set

namespace LowDimensionalTopology.Geometry.Teichmuller
open Surfaces
namespace SmoothSurfaceEquiv

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
variable {R : ClosedRiemannSurface X} {S : RiemannSurface Y}

/-- The coordinate-independent quotient of the actual smooth map. -/
def smoothPointwiseDilatation (f : SmoothSurfaceEquiv R.toRiemannSurface S)
    (hf : PreservesComplexOrientation R.toRiemannAtlas S.toRiemannAtlas f.toHomeomorph)
    (x : X) : ℝ :=
  (1 + (f.beltrami hf).abs x) / (1 - (f.beltrami hf).abs x)

/-- The literal supremum over every point of the same original compact source. -/
def compactMaximalDilatation (f : SmoothSurfaceEquiv R.toRiemannSurface S)
    (hf : PreservesComplexOrientation R.toRiemannAtlas S.toRiemannAtlas f.toHomeomorph) : ℝ :=
  sSup (range (f.smoothPointwiseDilatation hf))

/-- Every valid original pair of charts computes exactly this intrinsic quotient. -/
theorem smoothPointwiseDilatation_eq_chart
    (f : SmoothSurfaceEquiv R.toRiemannSurface S)
    (hf : PreservesComplexOrientation R.toRiemannAtlas S.toRiemannAtlas f.toHomeomorph)
    (e : BeltramiDifferential.Chart R.toRiemannAtlas)
    (g : OpenPartialHomeomorph Y ℂ) (hg : g ∈ S.charts)
    (x : X) (hx : x ∈ e.val.source) (hfx : f.toHomeomorph x ∈ g.source) :
    f.smoothPointwiseDilatation hf x =
      LiZhongQC.dilatationQuotient (riemannChartMap e.val f.toHomeomorph g) (e.val x) := by
  have hfx' : f.toHomeomorph (e.val.symm (e.val x)) ∈ g.source := by
    simpa only [e.val.left_inv hx] using hfx
  unfold smoothPointwiseDilatation LiZhongQC.dilatationQuotient
  rw [BeltramiDifferential.abs_eq_coeff _ e x hx,
    f.beltrami_coeff_eq_chartDilatation hf e
      ⟨e.val x, e.val.map_source hx⟩ g hg hfx']

/-- Positivity makes the literal quotient a genuine continuous function. -/
theorem continuous_smoothPointwiseDilatation
    (f : SmoothSurfaceEquiv R.toRiemannSurface S)
    (hf : PreservesComplexOrientation R.toRiemannAtlas S.toRiemannAtlas f.toHomeomorph) :
    Continuous (f.smoothPointwiseDilatation hf) := by
  exact (continuous_const.add (f.beltrami hf).abs.continuous).div
    (continuous_const.sub (f.beltrami hf).abs.continuous)
    (fun x => (sub_pos.mpr (f.beltrami_abs_lt_one hf x)).ne')

/-- The pointwise quotient is at least one, including the conformal case. -/
theorem one_le_smoothPointwiseDilatation
    (f : SmoothSurfaceEquiv R.toRiemannSurface S)
    (hf : PreservesComplexOrientation R.toRiemannAtlas S.toRiemannAtlas f.toHomeomorph)
    (x : X) : 1 ≤ f.smoothPointwiseDilatation hf x := by
  unfold smoothPointwiseDilatation
  apply (le_div_iff₀ (sub_pos.mpr (f.beltrami_abs_lt_one hf x))).2
  have h := (f.beltrami hf).abs_nonneg x
  linarith

/-- Formula (1.7) for the same original compact source, with actual attainment.
Neither a QC bound nor a maximum point is supplied as an extra premise. -/
theorem compactMaximalDilatation_eq_and_attained
    (f : SmoothSurfaceEquiv R.toRiemannSurface S)
    (hf : PreservesComplexOrientation R.toRiemannAtlas S.toRiemannAtlas f.toHomeomorph) :
    letI := R.compactSpace
    f.compactMaximalDilatation hf =
        (1 + (f.beltrami hf).supNorm) / (1 - (f.beltrami hf).supNorm) ∧
      ∃ x : X, f.smoothPointwiseDilatation hf x = f.compactMaximalDilatation hf := by
  let := R.compactSpace
  let : Nonempty X := R.nonempty
  let μ := f.beltrami hf
  let K : ℝ := (1 + μ.supNorm) / (1 - μ.supNorm)
  obtain ⟨x, _hx, hmax⟩ := isCompact_univ.exists_isMaxOn
    (Set.univ_nonempty : (univ : Set X).Nonempty) μ.abs.continuous.continuousOn
  have hmax' : ∀ y : X, μ.abs y ≤ μ.abs x := isMaxOn_univ_iff.mp hmax
  have hkx : μ.supNorm ≤ μ.abs x := by
    change ‖μ.abs‖ ≤ μ.abs x
    apply (μ.abs.norm_le (μ.abs_nonneg x)).2
    intro y
    rw [Real.norm_eq_abs, abs_of_nonneg (μ.abs_nonneg y)]
    exact hmax' y
  have hxk : μ.abs x = μ.supNorm := le_antisymm (μ.abs_le_supNorm x) hkx
  have hklt : μ.supNorm < 1 :=
    μ.supNorm_lt_one_iff.mpr (fun y => f.beltrami_abs_lt_one hf y)
  have hbound (y : X) : f.smoothPointwiseDilatation hf y ≤ K := by
    change (1 + μ.abs y) / (1 - μ.abs y) ≤
      (1 + μ.supNorm) / (1 - μ.supNorm)
    apply (div_le_div_iff₀ (sub_pos.mpr (f.beltrami_abs_lt_one hf y))
      (sub_pos.mpr hklt)).2
    nlinarith [μ.abs_le_supNorm y]
  have hxK : f.smoothPointwiseDilatation hf x = K := by
    change (1 + μ.abs x) / (1 - μ.abs x) = K
    rw [hxk]
  have hbdd : BddAbove (range (f.smoothPointwiseDilatation hf)) := by
    refine ⟨K, ?_⟩
    rintro _ ⟨y, rfl⟩
    exact hbound y
  have hsup : f.compactMaximalDilatation hf = K := by
    change sSup (range (f.smoothPointwiseDilatation hf)) = K
    apply le_antisymm
    · apply csSup_le ⟨_, mem_range_self x⟩
      rintro _ ⟨y, rfl⟩
      exact hbound y
    · exact le_csSup hbdd ⟨x, hxK⟩
  exact ⟨hsup, x, hxK.trans hsup.symm⟩

end SmoothSurfaceEquiv
end LowDimensionalTopology.Geometry.Teichmuller
