module

public import LowDimensionalTopology.Geometry.Teichmuller.ConformalSmooth
public import LowDimensionalTopology.Geometry.Surfaces.Riemann.AnalyticLifting
public import Mathlib.Analysis.Calculus.FDeriv.Congr
public import Mathlib.Geometry.Manifold.ContMDiff.Atlas

/-!
# Real smooth oriented descent through analytic covering sheets

All sheets below come from actual local homeomorphisms. Their complex analytic
inverse regularity and nonzero derivatives are proved from the existing native
analytic inverse theorem. No smoothness or Jacobian of the descended map is
postulated. This external draft has not been elaborated.
-/

@[expose] public section

noncomputable section

open Set Filter Topology
open scoped Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller

open Surfaces

universe u v w z

/-- Real smoothness follows from the actual all-chart coordinate expressions. -/
theorem realContMDiff_of_chartMaps
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (A : RiemannAtlas X) (B : RiemannAtlas Y) (f : X → Y) (hf : Continuous f)
    (hchart : ∀ e ∈ A.charts, ∀ g ∈ B.charts,
      ContDiffOn ℝ ∞ (riemannChartMap e f g) (riemannChartMapDomain e f g)) :
    letI := A.toChartedSpace
    letI := B.toChartedSpace
    ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ f := by
  let := A.toChartedSpace
  let := B.toChartedSpace
  let := A.isRealManifold
  let := B.isRealManifold
  rw [contMDiff_iff]
  refine ⟨hf, fun x y => ?_⟩
  simpa only [extChartAt, OpenPartialHomeomorph.extend_coe,
    OpenPartialHomeomorph.extend_coe_symm, OpenPartialHomeomorph.extend_target,
    OpenPartialHomeomorph.extend_source, modelWithCornersSelf_coe,
    modelWithCornersSelf_coe_symm, Function.id_comp, Function.comp_id,
    Set.preimage_id, Set.range_id, Set.inter_univ,
    riemannChartMap, riemannChartMapDomain] using
    hchart (chartAt ℂ x) (chart_mem_atlas ℂ x) (chartAt ℂ y) (chart_mem_atlas ℂ y)

/-- A real smooth map has a smooth expression in any two original charts
containing the indicated point, without equality assumptions on `chartAt`. -/
theorem realContDiffAt_chartMap
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    {A : RiemannAtlas X} {B : RiemannAtlas Y} {f : X → Y}
    (hf : letI := A.toChartedSpace
      letI := B.toChartedSpace
      ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ f)
    (e : OpenPartialHomeomorph X ℂ) (he : e ∈ A.charts)
    (g : OpenPartialHomeomorph Y ℂ) (hg : g ∈ B.charts)
    (x : X) (hx : x ∈ e.source) (hy : f x ∈ g.source) :
    ContDiffAt ℝ ∞ (riemannChartMap e f g) (e x) := by
  let := A.toChartedSpace
  let := B.toChartedSpace
  let := A.isRealManifold
  let := B.isRealManifold
  have heMax : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, ℂ) ∞ X :=
    IsManifold.subset_maximalAtlas he
  have hgMax : g ∈ IsManifold.maximalAtlas 𝓘(ℝ, ℂ) ∞ Y :=
    IsManifold.subset_maximalAtlas hg
  have h := ((contMDiffAt_iff_of_mem_maximalAtlas heMax hgMax hx hy).mp (hf x)).2
  simpa only [OpenPartialHomeomorph.extend_coe, OpenPartialHomeomorph.extend_coe_symm,
    modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
    Function.id_comp, Function.comp_id, Set.range_id, contDiffWithinAt_univ,
    riemannChartMap] using h

/-- A coordinate sheet for an actual analytic local homeomorphism. Its forward
function is the literal coordinate expression of the original map. -/
theorem analyticLocalHomeomorph_coordinateSheet
    {U : Type u} {X : Type v} [TopologicalSpace U] [TopologicalSpace X]
    {A : RiemannAtlas U} {B : RiemannAtlas X} {p : U → X}
    (hp : RiemannAnalyticMap A B p) (hpl : IsLocalHomeomorph p)
    (a : OpenPartialHomeomorph U ℂ) (ha : a ∈ A.charts)
    (e : OpenPartialHomeomorph X ℂ) (he : e ∈ B.charts)
    (u₀ : U) (hu : u₀ ∈ a.source) (hpu : p u₀ ∈ e.source) :
    ∃ P : OpenPartialHomeomorph ℂ ℂ,
      (P : ℂ → ℂ) = riemannChartMap a p e ∧ a u₀ ∈ P.source ∧
      AnalyticOnNhd ℂ P P.source ∧ P.source ⊆ riemannChartMapDomain a p e := by
  obtain ⟨l, hul, hl⟩ := hpl u₀
  let P := a.symm.trans (l.trans e)
  have hsub : P.source ⊆ riemannChartMapDomain a p e := by
    intro t ht
    refine ⟨ht.1, ?_⟩
    change p (a.symm t) ∈ e.source
    rw [hl]
    exact ht.2.2
  have hfun : (P : ℂ → ℂ) = riemannChartMap a p e := by
    funext t
    change e (l (a.symm t)) = e (p (a.symm t))
    rw [← hl]
  refine ⟨P, hfun, ?_, ?_, hsub⟩
  · change a u₀ ∈ a.target ∧ a.symm (a u₀) ∈ l.source ∧
      l (a.symm (a u₀)) ∈ e.source
    rw [a.left_inv hu, ← hl]
    exact ⟨a.map_source hu, hul, hpu⟩
  · rw [hfun]
    exact (hp.2 a ha e he).mono hsub

/-- An analytic local homeomorphism preserves the actual complex orientations.
The positive determinant is derived from the analytic coordinate sheet. -/
theorem analyticLocalHomeomorph_preservesComplexOrientation
    {U : Type u} {X : Type v} [TopologicalSpace U] [TopologicalSpace X]
    {A : RiemannAtlas U} {B : RiemannAtlas X} {p : U → X}
    (hp : RiemannAnalyticMap A B p) (hpl : IsLocalHomeomorph p) :
    PreservesComplexOrientation A B p := by
  intro a ha e he t ht
  obtain ⟨P, hfun, huP, hP, _⟩ := analyticLocalHomeomorph_coordinateSheet hp hpl
    a ha e he (a.symm t) (a.map_target ht.1) ht.2
  have htP : t ∈ P.source := by simpa only [a.right_inv ht.1] using huP
  rw [← hfun]
  rw [realJacobian_eq_norm_deriv_sq (hP t htP).differentiableAt]
  exact sq_pos_of_ne_zero (norm_ne_zero_iff.mpr
    (openPartialHomeomorph_analytic_forward_deriv_ne_zero P hP t htP))

/-- Local descent of both real smoothness and positive Jacobian through an
actual surjective analytic local homeomorphism. -/
theorem realSmoothPositive_of_comp_analytic_localHomeomorph
    {U : Type u} {X : Type v} {Y : Type w}
    [TopologicalSpace U] [TopologicalSpace X] [TopologicalSpace Y]
    {A : RiemannAtlas U} {B : RiemannAtlas X} {C : RiemannAtlas Y}
    {p : U → X} {f : X → Y}
    (hp : RiemannAnalyticMap A B p) (hpl : IsLocalHomeomorph p)
    (hps : Function.Surjective p) (hf : Continuous f)
    (hF : letI := A.toChartedSpace
      letI := C.toChartedSpace
      ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (f ∘ p))
    (hFpos : PreservesComplexOrientation A C (f ∘ p)) :
    (letI := B.toChartedSpace; letI := C.toChartedSpace;
      ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ f) ∧ PreservesComplexOrientation B C f := by
  have hlocal : ∀ e ∈ B.charts, ∀ g ∈ C.charts,
      ∀ t ∈ riemannChartMapDomain e f g,
        ContDiffAt ℝ ∞ (riemannChartMap e f g) t ∧
          0 < realJacobian (riemannChartMap e f g) t := by
    intro e he g hg t ht
    obtain ⟨u₀, hu₀⟩ := hps (e.symm t)
    obtain ⟨a, ha, hua⟩ := A.cover u₀
    have hpu : p u₀ ∈ e.source := by rw [hu₀]; exact e.map_target ht.1
    have hfg : (f ∘ p) u₀ ∈ g.source := by
      change f (p u₀) ∈ g.source
      rw [hu₀]
      exact ht.2
    obtain ⟨P, hPfun, huP, hP, hsub⟩ :=
      analyticLocalHomeomorph_coordinateSheet hp hpl a ha e he u₀ hua hpu
    have hPval : P (a u₀) = t := by
      rw [hPfun]
      change e (p (a.symm (a u₀))) = t
      rw [a.left_inv hua, hu₀, e.right_inv ht.1]
    have htP : t ∈ P.target := hPval ▸ P.map_source huP
    have hPinv : P.symm t = a u₀ := by rw [← hPval, P.left_inv huP]
    have hi := openPartialHomeomorph_analytic_inverse P hP
    let F := riemannChartMap a (f ∘ p) g
    have hFat : ContDiffAt ℝ ∞ F (P.symm t) := by
      rw [hPinv]
      exact realContDiffAt_chartMap hF a ha g hg u₀ hua hfg
    have hPat : ContDiffAt ℝ ∞ P.symm t :=
      (hi t htP).contDiffAt.restrict_scalars ℝ
    have hcomp : ContDiffAt ℝ ∞ (F ∘ P.symm) t := hFat.comp t hPat
    have heq : riemannChartMap e f g =ᶠ[𝓝 t] F ∘ P.symm := by
      filter_upwards [P.open_target.mem_nhds htP] with s hs
      have hsP := hsub (P.map_target hs)
      have hproj : p (a.symm (P.symm s)) = e.symm s := by
        calc
          p (a.symm (P.symm s)) = e.symm (e (p (a.symm (P.symm s)))) :=
            (e.left_inv hsP.2).symm
          _ = e.symm (P (P.symm s)) := by rw [hPfun]; rfl
          _ = e.symm s := congrArg e.symm (P.right_inv hs)
      change g (f (e.symm s)) = g (f (p (a.symm (P.symm s))))
      rw [hproj]
    refine ⟨hcomp.congr_of_eventuallyEq heq, ?_⟩
    have hFdom : a u₀ ∈ riemannChartMapDomain a (f ∘ p) g := by
      refine ⟨a.map_source hua, ?_⟩
      change (f ∘ p) (a.symm (a u₀)) ∈ g.source
      rw [a.left_inv hua]
      exact hfg
    have hFpositive : 0 < realJacobian F (P.symm t) := by
      rw [hPinv]
      exact hFpos a ha g hg (a u₀) hFdom
    have hPpositive : 0 < realJacobian P.symm t := by
      rw [realJacobian_eq_norm_deriv_sq (hi t htP).differentiableAt]
      exact sq_pos_of_ne_zero (norm_ne_zero_iff.mpr
        (openPartialHomeomorph_analytic_forward_deriv_ne_zero P.symm hi t htP))
    have hJac : realJacobian (riemannChartMap e f g) t =
        realJacobian F (P.symm t) * realJacobian P.symm t := by
      unfold realJacobian
      rw [heq.fderiv_eq,
        fderiv_comp t (hFat.differentiableAt (by simp)) (hPat.differentiableAt (by simp))]
      exact LinearMap.det_comp _ _
    rw [hJac]
    exact mul_pos hFpositive hPpositive
  refine ⟨realContMDiff_of_chartMaps B C f hf ?_, ?_⟩
  · intro e he g hg t ht
    exact (hlocal e he g hg t ht).1.contDiffWithinAt
  · intro e he g hg t ht
    exact (hlocal e he g hg t ht).2

/-- An actual smooth oriented homeomorphism of analytic covering surfaces
descends to a smooth oriented equivalence on the original base surfaces.
The inverse descends through the reversed genuine covering sheets. -/
theorem analyticCovering_smooth_descent
    {U : Type u} {V : Type v} {X : Type w} {Y : Type z}
    [TopologicalSpace U] [TopologicalSpace V] [TopologicalSpace X] [TopologicalSpace Y]
    (A : RiemannSurface U) (B : RiemannSurface V)
    (R : RiemannSurface X) (S : RiemannSurface Y)
    {p : U → X} {q : V → Y}
    (hp : IsCoveringMap p) (hq : IsCoveringMap q)
    (hpa : RiemannAnalyticMap A.toRiemannAtlas R.toRiemannAtlas p)
    (hqa : RiemannAnalyticMap B.toRiemannAtlas S.toRiemannAtlas q)
    (hps : Function.Surjective p) (hqs : Function.Surjective q)
    (E : SmoothSurfaceEquiv A B)
    (hE : PreservesComplexOrientation A.toRiemannAtlas B.toRiemannAtlas E.toHomeomorph)
    (f : X ≃ₜ Y) (hcomm : ∀ u₀, q (E.toHomeomorph u₀) = f (p u₀)) :
    ∃ F : SmoothSurfaceEquiv R S, F.toHomeomorph = f ∧
      PreservesComplexOrientation R.toRiemannAtlas S.toRiemannAtlas F.toHomeomorph := by
  let := A.toRiemannAtlas.toChartedSpace
  let := B.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.toChartedSpace
  let := S.toRiemannAtlas.toChartedSpace
  have hcomp : q ∘ E.toHomeomorph = f ∘ p := funext hcomm
  have hF : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (f ∘ p) := by
    rw [← hcomp]
    exact hqa.contMDiff_real.comp E.contMDiff_toFun
  have hFpos : PreservesComplexOrientation A.toRiemannAtlas S.toRiemannAtlas (f ∘ p) := by
    rw [← hcomp]
    exact (analyticLocalHomeomorph_preservesComplexOrientation hqa hq.isLocalHomeomorph).comp
      hE E.toHomeomorph.continuous
  obtain ⟨hfSmooth, hfPos⟩ := realSmoothPositive_of_comp_analytic_localHomeomorph
    hpa hp.isLocalHomeomorph hps f.continuous hF hFpos
  have hcompInv : p ∘ E.toHomeomorph.symm = f.symm ∘ q := by
    funext v₀
    have h := hcomm (E.toHomeomorph.symm v₀)
    rw [E.toHomeomorph.apply_symm_apply] at h
    exact (f.symm_apply_apply _).symm.trans (congrArg f.symm h.symm)
  have hInv : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (f.symm ∘ q) := by
    rw [← hcompInv]
    exact hpa.contMDiff_real.comp E.symm.contMDiff_toFun
  have hInvpos : PreservesComplexOrientation B.toRiemannAtlas R.toRiemannAtlas
      (f.symm ∘ q) := by
    rw [← hcompInv]
    exact (analyticLocalHomeomorph_preservesComplexOrientation hpa hp.isLocalHomeomorph).comp
      (PreservesComplexOrientation.homeomorph_symm E.toHomeomorph hE)
      E.toHomeomorph.symm.continuous
  obtain ⟨hfInvSmooth, _⟩ := realSmoothPositive_of_comp_analytic_localHomeomorph
    hqa hq.isLocalHomeomorph hqs f.symm.continuous hInv hInvpos
  let F : SmoothSurfaceEquiv R S :=
    { toEquiv := f.toEquiv
      contMDiff_toFun := hfSmooth
      contMDiff_invFun := hfInvSmooth }
  exact ⟨F, rfl, hfPos⟩

end LowDimensionalTopology.Geometry.Teichmuller
