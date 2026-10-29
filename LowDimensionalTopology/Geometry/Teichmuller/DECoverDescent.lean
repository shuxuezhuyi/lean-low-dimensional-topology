module

public import LowDimensionalTopology.Geometry.Teichmuller.AnalyticCoverDescent
public import LowDimensionalTopology.Geometry.Teichmuller.DERealSmooth
public import LowDimensionalTopology.Geometry.Surfaces.Riemann.RiemannManifoldEquivalences
public import LowDimensionalTopology.External.LiZhongQC.Ch06.S24_QuasiFuchsian

/-!
# Descending the actual smooth Douady--Earle representative

The half-plane structure used here is its original Mathlib singleton atlas.
The proof checks the unique original chart, rather than asserting equality of
the choices of `chartAt` after a general atlas/manifold round trip.
This external draft has not been elaborated.
-/

@[expose] public section

noncomputable section

open Set Filter Topology
open scoped Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller

open Surfaces

universe u v

/-- The actual upper half-plane with its original complex analytic manifold atlas. -/
def upperHalfNativeSurface : RiemannSurface UpperHalfPlane :=
  RiemannSurface.ofManifold UpperHalfPlane

private theorem upperHalfNative_chart_eq (e : OpenPartialHomeomorph UpperHalfPlane ℂ)
    (he : e ∈ upperHalfNativeSurface.charts) : e = UpperHalfPlane.ofComplex.symm := by
  change e ∈ ({UpperHalfPlane.ofComplex.symm} :
    Set (OpenPartialHomeomorph UpperHalfPlane ℂ)) at he
  exact Set.mem_singleton_iff.mp he

private theorem upperHalfNative_chartMapDomain (E : UpperHalfPlane ≃ₜ UpperHalfPlane) :
    riemannChartMapDomain UpperHalfPlane.ofComplex.symm E UpperHalfPlane.ofComplex.symm =
      LiZhongQC.upperHalf := by
  ext z
  simp [riemannChartMapDomain, UpperHalfPlane.ofComplex, LiZhongQC.upperHalf]

private theorem upperHalfNative_chartMap_eventuallyEq
    (E : UpperHalfPlane ≃ₜ UpperHalfPlane) {z : ℂ} (hz : z ∈ LiZhongQC.upperHalf) :
    riemannChartMap UpperHalfPlane.ofComplex.symm E UpperHalfPlane.ofComplex.symm =ᶠ[𝓝 z]
      LiZhongQC.liftToC E := by
  filter_upwards [LiZhongQC.isOpen_upperHalf.mem_nhds hz] with w hw
  change (E (UpperHalfPlane.ofComplex w) : ℂ) = LiZhongQC.liftToC E w
  exact (LiZhongQC.h23l_liftToC_eq E hw).symm

/-- The genuine smooth plane expression on the open half-plane induces real
smoothness in the original half-plane atlas. No regularity is used outside it. -/
theorem realContMDiff_upperHalf_of_liftToC
    (E : UpperHalfPlane ≃ₜ UpperHalfPlane)
    (hE : ContDiffOn ℝ ∞ (LiZhongQC.liftToC E) LiZhongQC.upperHalf) :
    letI := upperHalfNativeSurface.toRiemannAtlas.toChartedSpace
    ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ E := by
  apply realContMDiff_of_chartMaps upperHalfNativeSurface.toRiemannAtlas
    upperHalfNativeSurface.toRiemannAtlas E E.continuous
  intro e he g hg
  rw [upperHalfNative_chart_eq e he, upperHalfNative_chart_eq g hg,
    upperHalfNative_chartMapDomain]
  apply hE.congr
  intro z hz
  change (E (UpperHalfPlane.ofComplex z) : ℂ) = LiZhongQC.liftToC E z
  exact (LiZhongQC.h23l_liftToC_eq E hz).symm

/-- Positive plane Jacobian is precisely positive Jacobian in the unique
original half-plane chart. -/
theorem upperHalf_preservesComplexOrientation_of_realJacobian_pos
    (E : UpperHalfPlane ≃ₜ UpperHalfPlane)
    (hJ : ∀ z ∈ LiZhongQC.upperHalf, 0 < realJacobian (LiZhongQC.liftToC E) z) :
    PreservesComplexOrientation upperHalfNativeSurface.toRiemannAtlas
      upperHalfNativeSurface.toRiemannAtlas E := by
  intro e he g hg z hz
  rw [upperHalfNative_chart_eq e he, upperHalfNative_chart_eq g hg] at hz ⊢
  rw [upperHalfNative_chartMapDomain] at hz
  have h := hJ z hz
  unfold realJacobian at h ⊢
  rwa [(upperHalfNative_chartMap_eventuallyEq E hz).fderiv_eq]

/-- Both actual plane regularity statements package the same original
half-plane homeomorphism as a real smooth, orientation-preserving equivalence. -/
theorem upperHalf_exists_smoothSurfaceEquiv
    (E : UpperHalfPlane ≃ₜ UpperHalfPlane)
    (hE : ContDiffOn ℝ ∞ (LiZhongQC.liftToC E) LiZhongQC.upperHalf)
    (hInv : ContDiffOn ℝ ∞ (LiZhongQC.liftToC E.symm) LiZhongQC.upperHalf)
    (hJ : ∀ z ∈ LiZhongQC.upperHalf, 0 < realJacobian (LiZhongQC.liftToC E) z) :
    ∃ F : SmoothSurfaceEquiv upperHalfNativeSurface upperHalfNativeSurface,
      F.toHomeomorph = E ∧
        PreservesComplexOrientation upperHalfNativeSurface.toRiemannAtlas
          upperHalfNativeSurface.toRiemannAtlas F.toHomeomorph := by
  let := upperHalfNativeSurface.toRiemannAtlas.toChartedSpace
  let F : SmoothSurfaceEquiv upperHalfNativeSurface upperHalfNativeSurface :=
    { toEquiv := E.toEquiv
      contMDiff_toFun := realContMDiff_upperHalf_of_liftToC E hE
      contMDiff_invFun := realContMDiff_upperHalf_of_liftToC E.symm hInv }
  exact ⟨F, rfl, upperHalf_preservesComplexOrientation_of_realJacobian_pos E hJ⟩

/-- The strict DE Wirtinger inequality gives its actual positive real
determinant, using genuine real differentiability from its C∞ conclusion. -/
theorem realJacobian_liftToC_pos_of_wirtinger
    (E : UpperHalfPlane ≃ₜ UpperHalfPlane)
    (hE : ContDiffOn ℝ ∞ (LiZhongQC.liftToC E) LiZhongQC.upperHalf)
    (hj : ∀ z ∈ LiZhongQC.upperHalf,
      ‖LiZhongQC.dzbar (LiZhongQC.liftToC E) z‖ <
        ‖LiZhongQC.dz (LiZhongQC.liftToC E) z‖) :
    ∀ z ∈ LiZhongQC.upperHalf, 0 < realJacobian (LiZhongQC.liftToC E) z := by
  intro z hz
  have hd : DifferentiableAt ℝ (LiZhongQC.liftToC E) z :=
    (hE.contDiffAt (LiZhongQC.isOpen_upperHalf.mem_nhds hz)).differentiableAt (by simp)
  change 0 < LinearMap.det (fderiv ℝ (LiZhongQC.liftToC E) z : ℂ →ₗ[ℝ] ℂ)
  rw [LiZhongQC.det_fderiv_eq_jacobian hd]
  have h := hj z hz
  unfold LiZhongQC.jacobian
  nlinarith [norm_nonneg (LiZhongQC.dzbar (LiZhongQC.liftToC E) z),
    norm_nonneg (LiZhongQC.dz (LiZhongQC.liftToC E) z)]

/-- Apply the general actual-sheet descent to the original source
uniformizations and the original native base atlases. -/
theorem uniformization_smooth_descent
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (R : RiemannSurface X) (S : RiemannSurface Y)
    {Γ₀ Γ₁ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {p₀ : UpperHalfPlane → X} {p₁ : UpperHalfPlane → Y}
    (hp₀ : letI := R.toRiemannAtlas.toChartedSpace
      LiZhongQC.IsUniformization Γ₀ p₀)
    (hp₁ : letI := S.toRiemannAtlas.toChartedSpace
      LiZhongQC.IsUniformization Γ₁ p₁)
    (E : UpperHalfPlane ≃ₜ UpperHalfPlane) (f : X ≃ₜ Y)
    (hf : LiZhongQC.IsLift p₀ p₁ f E)
    (hE : ContDiffOn ℝ ∞ (LiZhongQC.liftToC E) LiZhongQC.upperHalf)
    (hInv : ContDiffOn ℝ ∞ (LiZhongQC.liftToC E.symm) LiZhongQC.upperHalf)
    (hj : ∀ z ∈ LiZhongQC.upperHalf,
      ‖LiZhongQC.dzbar (LiZhongQC.liftToC E) z‖ <
        ‖LiZhongQC.dz (LiZhongQC.liftToC E) z‖) :
    ∃ F : SmoothSurfaceEquiv R S, F.toHomeomorph = f ∧
      PreservesComplexOrientation R.toRiemannAtlas S.toRiemannAtlas F.toHomeomorph := by
  let := R.toRiemannAtlas.toChartedSpace
  let := S.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  let := S.toRiemannAtlas.isManifold
  have hpa : RiemannAnalyticMap upperHalfNativeSurface.toRiemannAtlas R.toRiemannAtlas p₀ :=
    riemannAnalyticMap_of_contMDiff_ofManifold
      (LiZhongQC.k22u_mdifferentiable_contMDiff hp₀.2.1)
  have hqa : RiemannAnalyticMap upperHalfNativeSurface.toRiemannAtlas S.toRiemannAtlas p₁ :=
    riemannAnalyticMap_of_contMDiff_ofManifold
      (LiZhongQC.k22u_mdifferentiable_contMDiff hp₁.2.1)
  obtain ⟨F, hF, hFpos⟩ := upperHalf_exists_smoothSurfaceEquiv E hE hInv
    (realJacobian_liftToC_pos_of_wirtinger E hE hj)
  apply analyticCovering_smooth_descent upperHalfNativeSurface upperHalfNativeSurface R S
    hp₀.1 hp₁.1 hpa hqa hp₀.2.2.1 hp₁.2.2.1 F hFpos f
  intro τ
  rw [hF]
  exact hf τ

/-- The same descent for arbitrary existing complex manifold structures. The
native surfaces use their actual original chart sets; the preferred chart
choices need not be preserved when those chart sets are read back as manifolds. -/
theorem uniformization_smooth_descent_ofManifold
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    [ChartedSpace ℂ X] [ChartedSpace ℂ Y]
    [IsManifold 𝓘(ℂ) ω X] [IsManifold 𝓘(ℂ) ω Y]
    [T2Space X] [ConnectedSpace X] [T2Space Y] [ConnectedSpace Y]
    {Γ₀ Γ₁ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {p₀ : UpperHalfPlane → X} {p₁ : UpperHalfPlane → Y}
    (hp₀ : LiZhongQC.IsUniformization Γ₀ p₀)
    (hp₁ : LiZhongQC.IsUniformization Γ₁ p₁)
    (E : UpperHalfPlane ≃ₜ UpperHalfPlane) (f : X ≃ₜ Y)
    (hf : LiZhongQC.IsLift p₀ p₁ f E)
    (hE : ContDiffOn ℝ ∞ (LiZhongQC.liftToC E) LiZhongQC.upperHalf)
    (hInv : ContDiffOn ℝ ∞ (LiZhongQC.liftToC E.symm) LiZhongQC.upperHalf)
    (hj : ∀ z ∈ LiZhongQC.upperHalf,
      ‖LiZhongQC.dzbar (LiZhongQC.liftToC E) z‖ <
        ‖LiZhongQC.dz (LiZhongQC.liftToC E) z‖) :
    ∃ F : SmoothSurfaceEquiv (RiemannSurface.ofManifold X) (RiemannSurface.ofManifold Y),
      F.toHomeomorph = f ∧
        PreservesComplexOrientation (RiemannAtlas.ofManifold X)
          (RiemannAtlas.ofManifold Y) F.toHomeomorph := by
  have hpa : RiemannAnalyticMap upperHalfNativeSurface.toRiemannAtlas
      (RiemannAtlas.ofManifold X) p₀ :=
    riemannAnalyticMap_of_contMDiff_ofManifold
      (LiZhongQC.k22u_mdifferentiable_contMDiff hp₀.2.1)
  have hqa : RiemannAnalyticMap upperHalfNativeSurface.toRiemannAtlas
      (RiemannAtlas.ofManifold Y) p₁ :=
    riemannAnalyticMap_of_contMDiff_ofManifold
      (LiZhongQC.k22u_mdifferentiable_contMDiff hp₁.2.1)
  obtain ⟨F, hF, hFpos⟩ := upperHalf_exists_smoothSurfaceEquiv E hE hInv
    (realJacobian_liftToC_pos_of_wirtinger E hE hj)
  apply analyticCovering_smooth_descent upperHalfNativeSurface upperHalfNativeSurface
    (RiemannSurface.ofManifold X) (RiemannSurface.ofManifold Y)
    hp₀.1 hp₁.1 hpa hqa hp₀.2.2.1 hp₁.2.2.1 F hFpos f
  intro τ
  rw [hF]
  exact hf τ

/-- A higher-genus orientation-preserving homeomorphism has a real smooth
positive representative in its actual free homotopy class. The representative
is the actual descended DE map, whose extra C∞ regularity was proved above.

The deck-correspondence and homotopy part is adapted from Wu Xiaobin's original
LiZhongQC/Ch06/S24_QuasiFuchsian.lean at fixed revision
1c0d5473c020b66ed5106331a38a61536760b9b2, distributed under Apache 2.0.
It does not use a general smoothing axiom. -/
theorem exists_smooth_in_homotopy_class_ofManifold
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    [ChartedSpace ℂ X] [ChartedSpace ℂ Y]
    [IsManifold 𝓘(ℂ) ω X] [IsManifold 𝓘(ℂ) ω Y]
    [T2Space X] [ConnectedSpace X] [T2Space Y] [ConnectedSpace Y]
    {g : ℕ} (hg : 1 < g) (hX : LiZhongQC.HasGenus X g) (hY : LiZhongQC.HasGenus Y g)
    (f : X ≃ₜ Y) (hf : LiZhongQC.IsOrientationPreservingRS f) :
    ∃ F : SmoothSurfaceEquiv (RiemannSurface.ofManifold X) (RiemannSurface.ofManifold Y),
      PreservesComplexOrientation (RiemannAtlas.ofManifold X)
        (RiemannAtlas.ofManifold Y) F.toHomeomorph ∧
      ContinuousMap.Homotopic (_root_.toContinuousMap f)
        (_root_.toContinuousMap F.toHomeomorph) := by
  let := hX.1
  let := hY.1
  obtain ⟨Γ₀, p₀, hΓ₀, hfree₀, hp₀⟩ :=
    LiZhongQC.s22hg_exists_fuchsian_uniformization hg hX
  obtain ⟨Γ₁, p₁, hΓ₁, hfree₁, hp₁⟩ :=
    LiZhongQC.s22hg_exists_fuchsian_uniformization hg hY
  obtain ⟨τ₀⟩ : Nonempty UpperHalfPlane := inferInstance
  obtain ⟨τ₁, hτ₁⟩ := hp₁.2.2.1 (f (p₀ τ₀))
  obtain ⟨L, hL, _⟩ := LiZhongQC.exists_lift hp₀ hp₁ f τ₀ τ₁ hτ₁
  obtain ⟨φ, hφ, hφc, hor, hbd⟩ :=
    LiZhongQC.s24q_boundary hΓ₀ hfree₀ hp₀ hΓ₁ hfree₁ hp₁ hf hL
  obtain ⟨E, hE, hEreal, hInvreal, hj⟩ := de_upper_exists_smooth φ hφ hφc hor
  have hLE : ∀ γ δ : Matrix.SpecialLinearGroup (Fin 2) ℝ, γ ∈ Γ₀ →
      (∀ τ, L (γ • τ) = δ • L τ) → ∀ τ, E (γ • τ) = δ • E τ :=
    fun γ δ hγ hγδ => LiZhongQC.s24q_de_equivariant hφ hφc hE (hbd γ δ hγ hγδ)
  have h₀₁ : ∀ γ ∈ Γ₀, ∃ δ ∈ Γ₁, ∀ τ, E (γ • τ) = δ • E τ := by
    intro γ hγ
    obtain ⟨δ, hδ, hγδ⟩ := LiZhongQC.h23l_deck hp₀ hp₁ hL hγ
    exact ⟨δ, hδ, hLE γ δ hγ hγδ⟩
  have h₁₀ : ∀ δ ∈ Γ₁, ∃ γ ∈ Γ₀, ∀ τ, E (γ • τ) = δ • E τ := by
    intro δ hδ
    obtain ⟨γ, hγ, hγδ⟩ := LiZhongQC.s24q_deck_surj hp₀ hp₁ hL hδ
    exact ⟨γ, hγ, hLE γ δ hγ hγδ⟩
  obtain ⟨q, hq⟩ := LiZhongQC.s24q_descend hp₀ hp₁ E h₀₁ h₁₀
  obtain ⟨F, hF, hFpos⟩ := uniformization_smooth_descent_ofManifold
    hp₀ hp₁ E q hq hEreal hInvreal hj
  refine ⟨F, hFpos, ?_⟩
  rw [hF]
  apply (LiZhongQC.thm23_1_homotopy_iff hp₀ hp₁ f q hL hq).2
  refine ⟨1, Γ₁.one_mem, ?_⟩
  intro γ hγ τ
  obtain ⟨δ, _, hγδ⟩ := LiZhongQC.h23l_deck hp₀ hp₁ hL hγ
  have hE' := hLE γ δ hγ hγδ
  rw [one_smul, inv_one, one_smul, hγδ, hE', Homeomorph.apply_symm_apply,
    Homeomorph.apply_symm_apply]

end LowDimensionalTopology.Geometry.Teichmuller
