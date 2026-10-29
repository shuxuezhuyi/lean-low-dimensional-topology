module

public import LowDimensionalTopology.Geometry.Teichmuller.WeilPeterssonSmoothForm
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.FDeriv.ContinuousAlternatingMap
public import Mathlib.Geometry.Manifold.ContMDiff.Atlas

/-!
# The original WP form along an actual local flow

The time derivative is taken in the normed space of whole alternating maps in
the fixed real Bers coordinates. The result returns to the same actual tangent
fibre. Joint smoothness in time and space proves differentiability of the
pullback curve, including the time dependence of its spatial differential.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set Filter Topology
open scoped UpperHalfPlane Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
open Surfaces GammaMeasurableBeltrami

private theorem wp_flow_pullback_differentiable {n : ℕ}
    (Ω : (Fin n → ℂ) → (Fin n → ℂ) [⋀^Fin 2]→L[ℝ] ℝ)
    (Ψ : ℝ → (Fin n → ℂ) → (Fin n → ℂ)) (x : Fin n → ℂ)
    (hΨ : ContDiffAt ℝ ∞ (Function.uncurry Ψ) (0, x))
    (hΩ : ContDiffAt ℝ ∞ Ω (Ψ 0 x)) :
    DifferentiableAt ℝ
      (fun t : ℝ => (Ω (Ψ t x)).compContinuousLinearMap (fderiv ℝ (Ψ t) x)) 0 := by
  have hcurve : ContDiffAt ℝ ∞ (fun t : ℝ => Ψ t x) 0 :=
    hΨ.comp 0 (contDiffAt_id.prodMk contDiffAt_const)
  have hD : ContDiffAt ℝ 1 (fun t : ℝ => fderiv ℝ (Ψ t) x) 0 :=
    hΨ.fderiv contDiffAt_const (by simp)
  exact DifferentiableAt.continuousAlternatingMapCompContinuousLinearMap
    ((hΩ.comp 0 hcurve).differentiableAt (by simp)) hD.differentiableAt_one

variable {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {Γ : Subgroup Deck} {p : ℍ → X}
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
    (hΓ : LiZhongQC.IsFuchsian Γ) (hfree : LiZhongQC.ActsFreely Γ)
    (hsmooth : Unproved.Teichmuller.QuasiconformalSmoothing.{0})

local notation "E" => Fin (3*g-3) → ℂ
local notation "RI" => 𝓘(ℝ, E)
local notation "C" => canonicalComplexChartedSpace R hg hgenus
  (canonicalHandleGroupPresentation g) hΓ hfree hp hsmooth
local notation "χ" => nativeWeilPeterssonCoordinateChart R hp hg hgenus hΓ hfree hsmooth (basePoint R)
local notation "L" => nativeWeilPeterssonRealTangentCoordinateEquiv R hp hg hgenus hΓ hfree hsmooth
local notation "Ω" => nativeWeilPeterssonFundamentalRealCoordinateForm
  R hp hg hgenus hΓ hfree hsmooth (basePoint R)
local notation "realManifold" => Topology.IsOpenEmbedding.isManifold_singleton
  (I := RI) (n := ω)
  (canonicalBersCoordinates_isOpenEmbedding R hg hgenus
    (canonicalHandleGroupPresentation g) hΓ hfree hp hsmooth)

/-- The actual time family in the fixed canonical real Bers coordinates. -/
def nativeWeilPeterssonFormFlowCoordinates
    (Φ : ℝ → TeichmullerSpace.{0,0} R → TeichmullerSpace.{0,0} R) (t : ℝ) (x : E) : E :=
  χ (Φ t ((χ).symm x))

local notation "Ψ" => nativeWeilPeterssonFormFlowCoordinates R hp hg hgenus hΓ hfree hsmooth

/-- Pull back the whole original form by the actual differential in both slots. -/
def nativeWeilPeterssonFormFlowPullback
    (Φ : ℝ → TeichmullerSpace.{0,0} R → TeichmullerSpace.{0,0} R) (t : ℝ) (x : E) :
    E [⋀^Fin 2]→L[ℝ] ℝ :=
  (Ω (Ψ Φ t x)).compContinuousLinearMap (fderiv ℝ (Ψ Φ t) x)

local notation "PB" => nativeWeilPeterssonFormFlowPullback R hp hg hgenus hΓ hfree hsmooth

/-- Joint smoothness of the actual family makes its entire pullback curve differentiable. -/
theorem differentiableAt_nativeWeilPeterssonFormFlowPullback
    (hWP : Unproved.Teichmuller.WeilPeterssonLocalCoefficientSmoothness
      R hp hg hgenus hΓ hfree hsmooth)
    (q : TeichmullerSpace.{0,0} R) (V : TopologicalSpace.Opens (TeichmullerSpace.{0,0} R)) (hq : q ∈ V)
    (ε : ℝ) (hε : 0 < ε) (Φ : ℝ → (TeichmullerSpace.{0,0} R) → (TeichmullerSpace.{0,0} R))
    (hzero : ∀ r ∈ V, Φ 0 r = r) :
    letI := C
    letI : IsManifold RI ω (TeichmullerSpace.{0,0} R) := realManifold
    ContMDiffOn (ModelWithCorners.prod 𝓘(ℝ, ℝ) RI) RI ∞
      (fun z : ℝ × (TeichmullerSpace.{0,0} R) => Φ z.1 z.2) (Ioo (-ε) ε ×ˢ (V : Set (TeichmullerSpace.{0,0} R))) →
    DifferentiableAt ℝ (fun t : ℝ => PB Φ t (χ q)) 0 := by
  let := C
  let : IsManifold RI ω (TeichmullerSpace.{0,0} R) := realManifold
  intro hΦ
  have hqχ : q ∈ (χ).source := mem_chart_source E q
  have hx : χ q ∈ (χ).target := (χ).map_source hqχ
  have hleft : (χ).symm (χ q) = q := (χ).left_inv hqχ
  have hzero' : Ψ Φ 0 (χ q) = χ q := by
    simp only [nativeWeilPeterssonFormFlowCoordinates, hleft, hzero q hq]
  have hinv : ContMDiffAt RI RI ∞ (χ).symm (χ q) := by
    have h := contMDiffOn_chart_symm (I := RI) (n := ∞) (x := basePoint R)
    change ContMDiffOn RI RI ∞ (χ).symm (χ).target at h
    exact h.contMDiffAt ((χ).open_target.mem_nhds hx)
  have hchart (r : TeichmullerSpace.{0,0} R) : ContMDiffAt RI RI ∞ χ r := by
    change ContMDiffAt RI RI ∞ (extChartAt RI (basePoint R)) r
    exact contMDiffAt_extChartAt' (mem_chart_source E r)
  have hΦat : ContMDiffAt (ModelWithCorners.prod 𝓘(ℝ, ℝ) RI) RI ∞
      (fun z : ℝ × (TeichmullerSpace.{0,0} R) => Φ z.1 z.2) (0, (χ).symm (χ q)) := by
    rw [hleft]
    exact hΦ.contMDiffAt ((isOpen_Ioo.prod V.isOpen).mem_nhds
      ⟨⟨neg_lt_zero.mpr hε, hε⟩, hq⟩)
  have hback : ContMDiffAt (ModelWithCorners.prod 𝓘(ℝ, ℝ) RI)
      (ModelWithCorners.prod 𝓘(ℝ, ℝ) RI) ∞
      (fun z : ℝ × E => (z.1, (χ).symm z.2)) (0, χ q) := by
    exact contMDiffAt_id.prodMap hinv
  have hjoint : ContDiffAt ℝ ∞ (Function.uncurry (Ψ Φ)) (0, χ q) := by
    have h := (hchart (Φ 0 ((χ).symm (χ q)))).comp (0, χ q)
      (hΦat.comp (0, χ q) hback)
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at h
    simpa only [Function.comp_def, Function.uncurry_def, nativeWeilPeterssonFormFlowCoordinates] using h.contDiffAt
  have hΩ : ContDiffAt ℝ ∞ Ω (Ψ Φ 0 (χ q)) := by
    rw [hzero']
    exact (contDiffOn_nativeWeilPeterssonFundamentalRealCoordinateForm_of_localSmoothness
      R hp hg hgenus hΓ hfree hsmooth hWP (basePoint R)).contDiffAt
      ((χ).open_target.mem_nhds hx)
  exact wp_flow_pullback_differentiable Ω (Ψ Φ) (χ q) hjoint hΩ

/-- The whole pullback curve has its actual time derivative at zero. -/
theorem hasDerivAt_nativeWeilPeterssonFormFlowPullback
    (hWP : Unproved.Teichmuller.WeilPeterssonLocalCoefficientSmoothness
      R hp hg hgenus hΓ hfree hsmooth)
    (q : TeichmullerSpace.{0,0} R) (V : TopologicalSpace.Opens (TeichmullerSpace.{0,0} R)) (hq : q ∈ V)
    (ε : ℝ) (hε : 0 < ε) (Φ : ℝ → (TeichmullerSpace.{0,0} R) → (TeichmullerSpace.{0,0} R))
    (hzero : ∀ r ∈ V, Φ 0 r = r) :
    letI := C
    letI : IsManifold RI ω (TeichmullerSpace.{0,0} R) := realManifold
    ContMDiffOn (ModelWithCorners.prod 𝓘(ℝ, ℝ) RI) RI ∞
      (fun z : ℝ × (TeichmullerSpace.{0,0} R) => Φ z.1 z.2) (Ioo (-ε) ε ×ˢ (V : Set (TeichmullerSpace.{0,0} R))) →
    HasDerivAt (fun t : ℝ => PB Φ t (χ q))
      (deriv (fun t : ℝ => PB Φ t (χ q)) 0) 0 := by
  let := C
  let : IsManifold RI ω (TeichmullerSpace.{0,0} R) := realManifold
  intro hΦ
  exact (differentiableAt_nativeWeilPeterssonFormFlowPullback
    R hp hg hgenus hΓ hfree hsmooth hWP q V hq ε hε Φ hzero hΦ).hasDerivAt

/-- The original form's Lie derivative along the given local flow of the same field. -/
def nativeWeilPeterssonFormLieDerivativeAlong
    (q : TeichmullerSpace.{0,0} R) (V : TopologicalSpace.Opens (TeichmullerSpace.{0,0} R)) (_hq : q ∈ V)
    (ε : ℝ) (_hε : 0 < ε) (Φ : ℝ → (TeichmullerSpace.{0,0} R) → (TeichmullerSpace.{0,0} R)) :
    letI := C
    letI : IsManifold RI ω (TeichmullerSpace.{0,0} R) := realManifold
    (W : FormInterior.SmoothVectorField RI (M := (TeichmullerSpace.{0,0} R))) →
    (hzero : ∀ r ∈ V, Φ 0 r = r) →
    (hflow : ∀ s ∈ Ioo (-ε) ε, ∀ t ∈ Ioo (-ε) ε,
      ∀ r ∈ V, s + t ∈ Ioo (-ε) ε → Φ t r ∈ V → Φ (s + t) r = Φ s (Φ t r)) →
    (hΦ : ContMDiffOn (ModelWithCorners.prod 𝓘(ℝ, ℝ) RI) RI ∞
      (fun z : ℝ × (TeichmullerSpace.{0,0} R) => Φ z.1 z.2) (Ioo (-ε) ε ×ˢ (V : Set (TeichmullerSpace.{0,0} R)))) →
    (hgen : ∀ t ∈ Ioo (-ε) ε, ∀ r ∈ V,
      mfderiv 𝓘(ℝ, ℝ) RI (fun s : ℝ => Φ s r) t
        ((NormedSpace.fromTangentSpace (𝕜 := ℝ) t).symm 1) = W (Φ t r)) →
    TangentSpace RI q [⋀^Fin 2]→L[ℝ] ℝ := by
  let := C
  let : IsManifold RI ω (TeichmullerSpace.{0,0} R) := realManifold
  intro _W _hzero _hflow _hΦ _hgen
  exact (deriv (fun t : ℝ => PB Φ t (χ q)) 0).compContinuousLinearMap
    (L q).toContinuousLinearMap

end LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
