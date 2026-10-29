module

public import LowDimensionalTopology.Geometry.Teichmuller.DiscCoverPoincareTensor

/-!
# Pullback along the same original disk cover

The actual inverse sheet gives a local identity with the finite disk chart.
Differentiating that identity yields the required tangent cancellation and
the two-slot pullback for metrics constructed with the proved local formula.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set Filter Topology
open scoped Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller

open Surfaces Hyperbolic

variable {X : Type*} [TopologicalSpace X] {R : RiemannSurface X}

/-- The finite-coordinate inverse of an actual sheet is differentiable. -/
theorem discCoverSheetFinite_mdifferentiableAt (M : HyperbolicSurfaceModel R)
    (l : OpenPartialHomeomorph extendedUnitDisc X)
    (hl : M.discCover = (l : extendedUnitDisc → X))
    (x : X) (hx : x ∈ l.target) :
    let := R.toRiemannAtlas.toChartedSpace
    MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ)
      (l.symm.trans discFiniteChart : X → ℂ) x := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  let e : OriginalComplexChart R := ⟨chartAt ℂ x, chart_mem_atlas ℂ x⟩
  let F := discCoverSheetCoordinate e l
  have he : x ∈ e.val.source := mem_chart_source ℂ x
  have hxF : e.val x ∈ F.source := by
    change (e.val x ∈ e.val.target ∧ e.val.symm (e.val x) ∈ l.target) ∧
      l.symm (e.val.symm (e.val x)) ∈ discFiniteChart.source
    rw [e.val.left_inv he, discFiniteChart_source]
    exact ⟨⟨e.val.map_source he, hx⟩, mem_univ _⟩
  have hF : DifferentiableAt ℝ F (e.val x) :=
    ((discCoverSheetCoordinate_analytic M e l hl) (e.val x) hxF).differentiableAt.restrictScalars ℝ
  have hnear : (l.symm.trans discFiniteChart : X → ℂ) =ᶠ[𝓝 x]
      (F : ℂ → ℂ) ∘ (e.val : X → ℂ) := by
    filter_upwards [e.val.open_source.mem_nhds he] with y hy
    change discFiniteChart (l.symm y) = discFiniteChart (l.symm (e.val.symm (e.val y)))
    rw [e.val.left_inv hy]
  exact (hF.mdifferentiableAt.comp x
    (mdifferentiableAt_atlas (I := 𝓘(ℝ, ℂ)) e.property he)).congr_of_eventuallyEq hnear

/-- Differentiate the actual local identity `s ∘ π = discFiniteChart`. -/
theorem discCoverSheetFinite_mvfderiv_comp (M : HyperbolicSurfaceModel R)
    (l : OpenPartialHomeomorph extendedUnitDisc X)
    (hl : M.discCover = (l : extendedUnitDisc → X))
    (z : extendedUnitDisc) (hz : z ∈ l.source)
    (v : RealSurfaceTangent discRiemannSurface z) :
    let := discRiemannSurface.toRiemannAtlas.toChartedSpace
    let := R.toRiemannAtlas.toChartedSpace
    let s := l.symm.trans discFiniteChart
    mvfderiv 𝓘(ℝ, ℂ) (s : X → ℂ) (M.discCover z)
        (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) M.discCover z v) =
      mvfderiv 𝓘(ℝ, ℂ) (discFiniteChart : extendedUnitDisc → ℂ) z v := by
  let := discRiemannSurface.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.toChartedSpace
  let := discRiemannSurface.toRiemannAtlas.isRealManifold
  let := R.toRiemannAtlas.isRealManifold
  let s := l.symm.trans discFiniteChart
  have hx : M.discCover z ∈ l.target := by
    rw [hl]
    exact l.map_source hz
  have hs := discCoverSheetFinite_mdifferentiableAt M l hl (M.discCover z) hx
  have hπ : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) M.discCover z :=
    M.discCover_analytic.contMDiff_real.mdifferentiableAt (by simp)
  have hd := mdifferentiableAt_atlas (I := 𝓘(ℝ, ℂ)) discFiniteChart_mem
    (show z ∈ discFiniteChart.source by rw [discFiniteChart_source]; trivial)
  have hnear : (s : X → ℂ) ∘ M.discCover =ᶠ[𝓝 z]
      (discFiniteChart : extendedUnitDisc → ℂ) := by
    filter_upwards [l.open_source.mem_nhds hz] with y hy
    change discFiniteChart (l.symm (M.discCover y)) = discFiniteChart y
    rw [hl, l.left_inv hy]
  have hmf : mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ((s : X → ℂ) ∘ M.discCover) z =
      mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (discFiniteChart : extendedUnitDisc → ℂ) z :=
    (hd.hasMFDerivAt.congr_of_eventuallyEq_abuse hnear).mfderiv
  have hmv : mvfderiv 𝓘(ℝ, ℂ) ((s : X → ℂ) ∘ M.discCover) z =
      mvfderiv 𝓘(ℝ, ℂ) (discFiniteChart : extendedUnitDisc → ℂ) z := by
    unfold mvfderiv
    rw [hmf]
    ext a
    rfl
  exact (mvfderiv_comp_apply z hs hπ v).symm.trans
    (congrArg (fun L : RealSurfaceTangent discRiemannSurface z →L[ℝ] ℂ => L v) hmv)

/-- A metric constructed with the actual inverse-sheet formula has the required
pullback along that same cover, on both original tangent vectors. -/
theorem discCover_pullback_of_local_sheet_tensor (M : HyperbolicSurfaceModel R)
    (g : SmoothSurfaceMetric R)
    (hlocal : ∀ (l : OpenPartialHomeomorph extendedUnitDisc X)
      (_hl : M.discCover = (l : extendedUnitDisc → X))
      (x : X) (_hx : x ∈ l.target) (v w : RealSurfaceTangent R x),
      let := R.toRiemannAtlas.toChartedSpace
      let := R.toRiemannAtlas.isRealManifold
      let s := l.symm.trans discFiniteChart
      g.inner x v w = discPoincareTensor (s x)
        (mvfderiv 𝓘(ℝ, ℂ) (s : X → ℂ) x v)
        (mvfderiv 𝓘(ℝ, ℂ) (s : X → ℂ) x w)) :
    let := discRiemannSurface.toRiemannAtlas.toChartedSpace
    let := R.toRiemannAtlas.toChartedSpace
    let := R.toRiemannAtlas.isRealManifold
    ∀ (z : extendedUnitDisc) (v w : RealSurfaceTangent discRiemannSurface z),
      g.inner (M.discCover z)
          (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) M.discCover z v)
          (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) M.discCover z w) =
        discPoincareTensor (discFiniteChart z)
          (mvfderiv 𝓘(ℝ, ℂ) (discFiniteChart : extendedUnitDisc → ℂ) z v)
          (mvfderiv 𝓘(ℝ, ℂ) (discFiniteChart : extendedUnitDisc → ℂ) z w) := by
  let := discRiemannSurface.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  dsimp only
  intro z v w
  obtain ⟨l, hz, hl⟩ := M.discCover_covering.isLocalHomeomorph z
  have hx : M.discCover z ∈ l.target := by
    rw [hl]
    exact l.map_source hz
  have hsval : (l.symm.trans discFiniteChart) (M.discCover z) = discFiniteChart z := by
    change discFiniteChart (l.symm (M.discCover z)) = discFiniteChart z
    rw [hl, l.left_inv hz]
  rw [hlocal l hl (M.discCover z) hx, hsval,
    discCoverSheetFinite_mvfderiv_comp M l hl z hz v,
    discCoverSheetFinite_mvfderiv_comp M l hl z hz w]

end LowDimensionalTopology.Geometry.Teichmuller
