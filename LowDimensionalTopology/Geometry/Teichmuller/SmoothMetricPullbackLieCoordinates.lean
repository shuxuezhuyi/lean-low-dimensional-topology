module

public import LowDimensionalTopology.Geometry.Teichmuller.SmoothMetricPullbackTimeTensor
public import LowDimensionalTopology.Unproved.Teichmuller.OriginalClosedMetricTensorGreen
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Geometry.Manifold.ContMDiff.Atlas

/-!
# The full original-chart formula for a pullback variation

The same supplied family determines both its native velocity and the scalar
variation of its literal pullback metric. The product rule and symmetry of
the second derivative give all three original metric Lie-coordinate terms.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Bundle Set Filter Topology
open scoped Manifold ContDiff BigOperators

namespace LowDimensionalTopology.Geometry.Teichmuller
open Surfaces
universe u
namespace SmoothSurfaceMetric

local instance : NormedAddCommGroup (ℂ →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
    (σ₁₂ := RingHom.id ℝ) (E := ℂ) (F := ℝ)

local instance : NormedAddCommGroup (ℂ →L[ℝ] ℂ →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
    (σ₁₂ := RingHom.id ℝ) (E := ℂ) (F := ℂ →L[ℝ] ℝ)

private theorem metric_chart_spatialDerivative_hasDerivAt
    (P : ℝ × ℂ → ℂ) (z : ℂ) (hP : ContDiffAt ℝ ∞ P (0, z)) (v : ℂ) :
    let W : ℂ → ℂ := fun w => fderiv ℝ P (0, w) (1, 0)
    HasDerivAt (fun t : ℝ => fderiv ℝ (fun w : ℂ => P (t, w)) z v)
      (fderiv ℝ W z v) (0 : ℝ) := by
  let W : ℂ → ℂ := fun w => fderiv ℝ P (0, w) (1, 0)
  have hsecond : DifferentiableAt ℝ (fderiv ℝ P) (0, z) :=
    (hP.fderiv_right (m := 1) (by simp)).differentiableAt_one
  have htime : HasDerivAt (fun t : ℝ => (t, z)) (1, 0) 0 :=
    (hasDerivAt_id (0 : ℝ)).prodMk (hasDerivAt_const (0 : ℝ) z)
  have hWderiv (v : ℂ) :
      fderiv ℝ W z v = fderiv ℝ (fderiv ℝ P) (0, z) (0, v) (1, 0) := by
    have h := (hsecond.hasFDerivAt.comp z
      (hasFDerivAt_prodMk_right (0 : ℝ) z)).clm_apply
        (hasFDerivAt_const ((1 : ℝ), (0 : ℂ)) z)
    simpa [W] using congrArg (fun A => A v) h.fderiv
  have h := (hsecond.hasFDerivAt.comp_hasDerivAt (0 : ℝ) htime).clm_apply
    (hasDerivAt_const (0 : ℝ) ((0 : ℝ), v))
  have h' : HasDerivAt (fun t : ℝ => fderiv ℝ P (t, z) (0, v))
      (fderiv ℝ (fderiv ℝ P) (0, z) (1, 0) (0, v)) 0 := by
    simpa only [Function.comp_def, map_zero, add_zero] using h
  rw [(hP.isSymmSndFDerivAt (by simp)).eq (1, 0) (0, v), ← hWderiv v] at h'
  apply h'.congr_of_eventuallyEq
  have hnear := (hP.of_le (show (1 : ℕ∞ω) ≤ ∞ by simp)).eventually (by simp)
  filter_upwards [htime.continuousAt hnear] with t ht
  have hspace := ht.differentiableAt_one.hasFDerivAt.comp z
    (hasFDerivAt_prodMk_right t z)
  simpa only [Function.comp_def, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.inr_apply] using congrArg (fun A => A v) hspace.fderiv

set_option maxHeartbeats 800000 in
private theorem metric_chart_pullback_hasDerivAt
    (P : ℝ × ℂ → ℂ) (G : ℂ → ℂ →L[ℝ] ℂ →L[ℝ] ℝ) (z : ℂ)
    (hP : ContDiffAt ℝ ∞ P (0, z)) (hG : DifferentiableAt ℝ G z)
    (hzero : (fun w : ℂ => P (0, w)) =ᶠ[𝓝 z] id) (a b : ℂ) :
    let W : ℂ → ℂ := fun w => fderiv ℝ P (0, w) (1, 0)
    HasDerivAt
      (fun t : ℝ => G (P (t, z))
        (fderiv ℝ (fun w : ℂ => P (t, w)) z a)
        (fderiv ℝ (fun w : ℂ => P (t, w)) z b))
      (fderiv ℝ G z (W z) a b +
        G z (fderiv ℝ W z a) b + G z a (fderiv ℝ W z b)) 0 := by
  let W : ℂ → ℂ := fun w => fderiv ℝ P (0, w) (1, 0)
  have hpartial (v : ℂ) :
      HasDerivAt (fun t : ℝ => fderiv ℝ (fun w : ℂ => P (t, w)) z v)
        (fderiv ℝ W z v) 0 :=
    metric_chart_spatialDerivative_hasDerivAt P z hP v
  have htime : HasDerivAt (fun t : ℝ => (t, z)) (1, 0) 0 :=
    (hasDerivAt_id (0 : ℝ)).prodMk (hasDerivAt_const (0 : ℝ) z)
  have hPzero : P (0, z) = z := hzero.self_of_nhds
  have hDzero (v : ℂ) : fderiv ℝ (fun w : ℂ => P (0, w)) z v = v := by
    rw [hzero.fderiv_eq]
    simp only [fderiv_id, ContinuousLinearMap.id_apply]
  have hPtime : HasDerivAt (fun t : ℝ => P (t, z)) (W z) 0 := by
    exact (hP.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt (0 : ℝ) htime
  have hGat : HasFDerivAt G (fderiv ℝ G z) (P (0, z)) := by
    simpa only [hPzero] using hG.hasFDerivAt
  have hGcurve : HasDerivAt (fun t : ℝ => G (P (t, z)))
      (fderiv ℝ G z (W z)) (0 : ℝ) :=
    HasFDerivAt.comp_hasDerivAt
      (𝕜 := ℝ) (F := ℂ) (E := ℂ →L[ℝ] ℂ →L[ℝ] ℝ)
      (f := fun t : ℝ => P (t, z)) (f' := W z)
      (l := G) (l' := fderiv ℝ G z) (0 : ℝ) hGat hPtime
  have hGa : HasDerivAt
      (fun t : ℝ => G (P (t, z)) (fderiv ℝ (fun w : ℂ => P (t, w)) z a))
      (fderiv ℝ G z (W z) a + G z (fderiv ℝ W z a)) (0 : ℝ) := by
    simpa only [hPzero, hDzero] using hGcurve.clm_apply (hpartial a)
  have hmetric : HasDerivAt
      (fun t : ℝ => G (P (t, z))
        (fderiv ℝ (fun w : ℂ => P (t, w)) z a)
        (fderiv ℝ (fun w : ℂ => P (t, w)) z b))
      (fderiv ℝ G z (W z) a b +
        G z (fderiv ℝ W z a) b + G z a (fderiv ℝ W z b)) (0 : ℝ) := by
    simpa only [hPzero, hDzero, _root_.add_apply] using
      hGa.clm_apply (hpartial b)
  exact hmetric

variable {X : Type u} [TopologicalSpace X] (R : ClosedRiemannSurface X)

/-- The actual velocity and literal pullback variation satisfy the full
three-term metric Lie-coordinate law in every original complex chart. -/
theorem hasOriginalMetricLieCoordinates_of_pullbackVariation
    (Phi : ℝ → SmoothSurfaceEquiv R.toRiemannSurface R.toRiemannSurface)
    (g : SmoothSurfaceMetric R.toRiemannSurface)
    (hzero : ∀ x : X, (Phi 0).toHomeomorph x = x) :
    let := R.toRiemannAtlas.toChartedSpace
    let := R.toRiemannAtlas.isRealManifold
    (∀ x : X, ContMDiffAt (𝓘(ℝ).prod 𝓘(ℝ, ℂ)) 𝓘(ℝ, ℂ) ∞
      (fun p : ℝ × X => (Phi p.1).toHomeomorph p.2) (0, x)) →
    ∀ (V : FormInterior.SmoothVectorField 𝓘(ℝ, ℂ) (M := X)),
      (∀ (e : OriginalComplexChart R.toRiemannSurface)
          (x : X) (hx : x ∈ e.val.source),
        HasDerivAt (fun t : ℝ => e.val ((Phi t).toHomeomorph x))
          (SmoothSurfaceEquiv.originalChartDifferentialEquiv e x hx (V x)) 0) →
      ∀ (L : SmoothSymmetricTwoTensor R),
        (∀ (x : X) (a b : RealSurfaceTangent R.toRiemannSurface x),
          HasDerivAt (fun t : ℝ => (pullback (Phi t) g).inner x a b)
            (L.val x a b) 0) →
        HasOriginalMetricLieCoordinates R g V L := by
  classical
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  dsimp only
  intro hPhi V hV L hL e
  dsimp only
  let P : ℝ × ℂ → ℂ := fun p =>
    e.val ((Phi p.1).toHomeomorph (e.val.symm p.2))
  let G : ℂ → ℂ →L[ℝ] ℂ →L[ℝ] ℝ := fun z =>
    metricGramInChart g e (e.val.symm z)
  let W : ℂ → ℂ := fun z => fderiv ℝ P (0, z) (1, 0)
  let b : Fin 2 → ℂ := Complex.basisOneI
  let C : ℂ → Fin 2 → ℝ := fun z k =>
    if hz : z ∈ e.val.target then
      Complex.basisOneI.repr
        (SmoothSurfaceEquiv.originalChartDifferentialEquiv e (e.val.symm z)
          (e.val.map_target hz) (V (e.val.symm z))) k
    else 0
  have he : e.val ∈ IsManifold.maximalAtlas 𝓘(ℝ, ℂ) ∞ X :=
    IsManifold.subset_maximalAtlas e.property
  have hP (z : ℂ) (hz : z ∈ e.val.target) : ContDiffAt ℝ ∞ P (0, z) := by
    have hinv := contMDiffAt_symm_of_mem_maximalAtlas he hz
    have hback : ContMDiffAt (𝓘(ℝ).prod 𝓘(ℝ, ℂ))
        (𝓘(ℝ).prod 𝓘(ℝ, ℂ)) ∞
        (fun p : ℝ × ℂ => (p.1, e.val.symm p.2)) (0, z) :=
      contMDiffAt_id.prodMap hinv
    have hchart : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞
        e.val ((Phi 0).toHomeomorph (e.val.symm z)) := by
      rw [hzero]
      exact contMDiffAt_of_mem_maximalAtlas he (e.val.map_target hz)
    have h := hchart.comp (0, z) ((hPhi (e.val.symm z)).comp (0, z) hback)
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at h
    exact h.contDiffAt
  have hWvalue (z : ℂ) (hz : z ∈ e.val.target) :
      W z = SmoothSurfaceEquiv.originalChartDifferentialEquiv e (e.val.symm z)
        (e.val.map_target hz) (V (e.val.symm z)) := by
    have htime : HasDerivAt (fun t : ℝ => (t, z)) (1, 0) (0 : ℝ) :=
      (hasDerivAt_id (0 : ℝ)).prodMk (hasDerivAt_const (0 : ℝ) z)
    have hPt : HasFDerivAt P (fderiv ℝ P (0, z)) (0, z) :=
      ((hP z hz).differentiableAt (by simp)).hasFDerivAt
    have ht : HasDerivAt (fun t : ℝ => P (t, z)) (W z) 0 := by
      have h := hPt.comp_hasDerivAt (f := fun t : ℝ => (t, z)) (0 : ℝ) htime
      simpa only [Function.comp_def, W] using h
    exact ht.unique (hV e (e.val.symm z) (e.val.map_target hz))
  have hCvalue (z : ℂ) (hz : z ∈ e.val.target) (k : Fin 2) :
      C z k = Complex.basisOneI.repr (W z) k := by
    simp only [C, dite_eq_left hz, hWvalue z hz]
  intro z hz i j
  let x := e.val.symm z
  have hx : x ∈ e.val.source := e.val.map_target hz
  let D := SmoothSurfaceEquiv.originalChartDifferentialEquiv e x hx
  have hG : ContDiffAt ℝ ∞ G z := by
    have hg := (metricGramInChart_contMDiffOn g e).contMDiffAt
      (e.val.open_source.mem_nhds hx)
    exact (hg.comp z (contMDiffAt_symm_of_mem_maximalAtlas he hz)).contDiffAt
  have hW : DifferentiableAt ℝ W z :=
    (((hP z hz).fderiv_right (m := 1) (by simp)).differentiableAt_one.comp z
      (hasFDerivAt_prodMk_right (0 : ℝ) z).differentiableAt).clm_apply
        (differentiableAt_const ((1 : ℝ), (0 : ℂ)))
  have hzeroP : (fun w : ℂ => P (0, w)) =ᶠ[𝓝 z] id := by
    filter_upwards [e.val.open_target.mem_nhds hz] with w hw
    exact (congrArg e.val (hzero (e.val.symm w))).trans (e.val.right_inv hw)
  have hmodel := metric_chart_pullback_hasDerivAt P G z (hP z hz)
    (hG.differentiableAt (by simp)) hzeroP (b i) (b j)
  have hmetric :
      (fun t : ℝ => (pullback (Phi t) g).inner x (D.symm (b i)) (D.symm (b j)))
        =ᶠ[𝓝 0]
      (fun t : ℝ => G (P (t, z))
        (fderiv ℝ (fun w : ℂ => P (t, w)) z (b i))
        (fderiv ℝ (fun w : ℂ => P (t, w)) z (b j))) := by
    have hcurve : ContinuousAt (fun t : ℝ => (Phi t).toHomeomorph x) 0 := by
      have hparam : ContinuousAt (fun t : ℝ => (t, x)) (0 : ℝ) :=
        continuousAt_id.prodMk continuousAt_const
      exact ContinuousAt.comp (f := fun t : ℝ => (t, x)) (x := (0 : ℝ))
        (hPhi x).continuousAt hparam
    have hsource : (Phi 0).toHomeomorph x ∈ e.val.source := by rw [hzero]; exact hx
    filter_upwards [hcurve (e.val.open_source.mem_nhds hsource)] with t ht
    let y := (Phi t).toHomeomorph x
    let D' := SmoothSurfaceEquiv.originalChartDifferentialEquiv e y ht
    have hintertwine (v : ℂ) :
        D' (surfaceDifferential R.toRiemannSurface R.toRiemannSurface
          (Phi t) x (D.symm v)) = fderiv ℝ (fun w : ℂ => P (t, w)) z v := by
      have h := (Phi t).chartDifferential_intertwines e e x hx ht (D.symm v)
      change fderiv ℝ (fun w : ℂ => P (t, w)) (e.val x) (D (D.symm v)) = _ at h
      rw [D.apply_symm_apply, e.val.right_inv hz] at h
      exact h.symm
    change pullbackForm (Phi t) g x (D.symm (b i)) (D.symm (b j)) = _
    change _ = metricGramInChart g e (e.val.symm (e.val y))
      (fderiv ℝ (fun w : ℂ => P (t, w)) z (b i))
      (fderiv ℝ (fun w : ℂ => P (t, w)) z (b j))
    rw [e.val.left_inv ht, metricGramInChart_eq g e y ht]
    change _ = g.inner y (D'.symm (fderiv ℝ (fun w : ℂ => P (t, w)) z (b i)))
      (D'.symm (fderiv ℝ (fun w : ℂ => P (t, w)) z (b j)))
    rw [← hintertwine (b i), ← hintertwine (b j),
      D'.symm_apply_apply, D'.symm_apply_apply]
    rfl
  have hLvalue := (hL x (D.symm (b i)) (D.symm (b j))).unique
    (hmodel.congr_of_eventuallyEq hmetric)
  have hGcoord (a c v : ℂ) :
      fderiv ℝ (fun w : ℂ => G w a c) z v = fderiv ℝ G z v a c := by
    have h := (((hG.differentiableAt (by simp)).hasFDerivAt.clm_apply
      (hasFDerivAt_const a z)).clm_apply (hasFDerivAt_const c z))
    simpa using congrArg (fun A => A v) h.fderiv
  have hCcoord (k : Fin 2) (v : ℂ) :
      fderiv ℝ (fun w : ℂ => C w k) z v =
        Complex.basisOneI.repr (fderiv ℝ W z v) k := by
    have hnear : (fun w : ℂ => C w k) =ᶠ[𝓝 z]
        (fun w : ℂ => Complex.basisOneI.repr (W w) k) := by
      filter_upwards [e.val.open_target.mem_nhds hz] with w hw
      exact hCvalue w hw k
    rw [hnear.fderiv_eq]
    let r : ℂ →L[ℝ] ℝ := (Complex.basisOneI.coord k).toContinuousLinearMap
    have h := r.hasFDerivAt.comp z hW.hasFDerivAt
    exact congrArg (fun A => A v) h.fderiv
  have hGsymm (a c : ℂ) : G z a c = G z c a := by
    change metricGramInChart g e x a c = metricGramInChart g e x c a
    rw [metricGramInChart_eq g e x hx]
    exact g.symm x (D.symm a) (D.symm c)
  have hdir : fderiv ℝ G z (W z) (b i) (b j) =
      ∑ k : Fin 2, C z k * fderiv ℝ (fun w : ℂ => G w (b i) (b j)) z (b k) := by
    conv_lhs => rw [← Complex.basisOneI.sum_repr (W z)]
    simp only [map_sum, map_smul, _root_.sum_apply, _root_.smul_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro k hk
    rw [hCvalue z hz k, hGcoord]
  have hleft : G z (fderiv ℝ W z (b i)) (b j) =
      ∑ k : Fin 2, G z (b j) (b k) * fderiv ℝ (fun w : ℂ => C w k) z (b i) := by
    rw [hGsymm]
    conv_lhs => rw [← Complex.basisOneI.sum_repr (fderiv ℝ W z (b i))]
    simp only [map_sum, map_smul, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro k hk
    rw [hCcoord]
    exact mul_comm _ _
  have hright : G z (b i) (fderiv ℝ W z (b j)) =
      ∑ k : Fin 2, G z (b i) (b k) * fderiv ℝ (fun w : ℂ => C w k) z (b j) := by
    conv_lhs => rw [← Complex.basisOneI.sum_repr (fderiv ℝ W z (b j))]
    simp only [map_sum, map_smul, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro k hk
    rw [hCcoord]
    exact mul_comm _ _
  change L.val x (D.symm (b i)) (D.symm (b j)) =
    ∑ k : Fin 2,
      (C z k * fderiv ℝ (fun w : ℂ => G w (b i) (b j)) z (b k) +
        G z (b i) (b k) * fderiv ℝ (fun w : ℂ => C w k) z (b j) +
        G z (b j) (b k) * fderiv ℝ (fun w : ℂ => C w k) z (b i))
  rw [hLvalue, hdir, hleft, hright]
  simp only [Finset.sum_add_distrib]
  ring

/-- A family with its actual native velocity has a genuine smooth symmetric
variation tensor and the full original-chart metric Lie formula. -/
theorem exists_metricLieTensor_of_smoothFamily
    (Phi : ℝ → SmoothSurfaceEquiv R.toRiemannSurface R.toRiemannSurface)
    (g : SmoothSurfaceMetric R.toRiemannSurface)
    (hzero : ∀ x : X, (Phi 0).toHomeomorph x = x) :
    let := R.toRiemannAtlas.toChartedSpace
    let := R.toRiemannAtlas.isRealManifold
    (∀ x : X, ContMDiffAt (𝓘(ℝ).prod 𝓘(ℝ, ℂ)) 𝓘(ℝ, ℂ) ∞
      (fun p : ℝ × X => (Phi p.1).toHomeomorph p.2) (0, x)) →
    ∀ (V : FormInterior.SmoothVectorField 𝓘(ℝ, ℂ) (M := X)),
      (∀ (e : OriginalComplexChart R.toRiemannSurface)
          (x : X) (hx : x ∈ e.val.source),
        HasDerivAt (fun t : ℝ => e.val ((Phi t).toHomeomorph x))
          (SmoothSurfaceEquiv.originalChartDifferentialEquiv e x hx (V x)) 0) →
      ∃ L : SmoothSymmetricTwoTensor R,
        (∀ (x : X) (a b : RealSurfaceTangent R.toRiemannSurface x),
          HasDerivAt (fun t : ℝ => (pullback (Phi t) g).inner x a b)
            (L.val x a b) 0) ∧ HasOriginalMetricLieCoordinates R g V L := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  dsimp only
  intro hPhi V hV
  rcases exists_pullbackTimeDerivativeTensor R Phi g hPhi with ⟨L, hL⟩
  exact ⟨L, hL,
    hasOriginalMetricLieCoordinates_of_pullbackVariation R Phi g hzero hPhi V hV L hL⟩

end SmoothSurfaceMetric
end LowDimensionalTopology.Geometry.Teichmuller
