module

public import LowDimensionalTopology.Geometry.Surfaces.Hyperbolic.HalfPlaneUniformization
public import LowDimensionalTopology.Geometry.Auxiliary.Analysis.LocalBoundedVariation
public import LowDimensionalTopology.Geometry.Hyperbolic.Models.HalfPlane.IntrinsicBoundedVariation
public import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-!
# Original-atlas rectifiability and actual covering lifts

The surface predicate uses the given Riemann atlas and genuine relative
parameter neighborhoods. Analytic coordinate expressions and actual analytic
inverses of covering charts are locally Lipschitz. They transfer BV in both
directions, and compact-interval gluing includes the parameter endpoints.
No original C1, absolute continuity, Lipschitz or global inverse-chart premise
is inserted.
-/

public section
noncomputable section
open Set Filter
open scoped UpperHalfPlane Topology Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Surfaces
open LowDimensionalTopology.Geometry.Hyperbolic

/-- A curve is rectifiable in the original analytic atlas when its coordinates
are BV on a genuine relative parameter neighborhood of every point. -/
@[expose] def RiemannAtlas.IsChartwiseBVOn
    {X : Type*} [TopologicalSpace X] (A : RiemannAtlas X)
    (α : ℝ → X) (s : Set ℝ) : Prop :=
  ∀ x ∈ s, ∃ e ∈ A.charts, α x ∈ e.source ∧
    ∃ U ∈ 𝓝[s] x, U ⊆ s ∧ MapsTo α U e.source ∧
      BoundedVariationOn (fun t => e (α t)) U

/-- Analytic local homeomorphisms transfer genuine original-atlas rectifiability
to and from intrinsic BV of a continuous half-plane lift on a compact interval. -/
theorem halfPlane_boundedVariation_iff_original_chartwiseBV
    {X : Type*} [TopologicalSpace X] (A : RiemannAtlas X) {p : ℍ → X}
    (hpa : RiemannAnalyticMap (RiemannAtlas.ofManifold ℍ) A p)
    (hpl : IsLocalHomeomorph p) {f : ℝ → ℍ} {a b : ℝ}
    (hf : ContinuousOn f (Icc a b)) :
    BoundedVariationOn f (Icc a b) ↔ A.IsChartwiseBVOn (p ∘ f) (Icc a b) := by
  rw [halfPlane_boundedVariation_iff_coe_of_continuousOn hf]
  constructor
  · intro hBV x hx
    obtain ⟨g, hg, hgx⟩ := A.cover (p (f x))
    let e := chartAt ℂ (f x)
    have he : e ∈ (RiemannAtlas.ofManifold ℍ).charts := chart_mem_atlas ℂ (f x)
    have hecoe (z : ℍ) : e z = (z : ℂ) := rfl
    have hesource (z : ℍ) : z ∈ e.source := by change z ∈ (univ : Set ℍ); trivial
    let Q := riemannChartMap e p g
    have hQa : AnalyticAt ℂ Q (e (f x)) :=
      hpa.2 e he g hg (e (f x)) (riemannChartMapDomain_mem e p g (f x) (hesource _) hgx)
    obtain ⟨C, V, hV, hLip⟩ := (hQa.contDiffAt : ContDiffAt ℂ 1 Q (e (f x))).exists_lipschitzOnWith
    rw [hecoe] at hV
    have hco : ContinuousWithinAt (fun t => (f t : ℂ)) (Icc a b) x :=
      UpperHalfPlane.continuous_coe.continuousAt.comp_continuousWithinAt (hf x hx)
    have hpc : ContinuousWithinAt (fun t => p (f t)) (Icc a b) x :=
      hpa.1.continuousAt.comp_continuousWithinAt (hf x hx)
    have hnear := (hco.eventually hV).and (hpc.eventually (g.open_source.mem_nhds hgx))
    let U := Icc a b ∩ {t : ℝ | (f t : ℂ) ∈ V ∧ p (f t) ∈ g.source}
    have hU : U ∈ 𝓝[Icc a b] x := inter_mem self_mem_nhdsWithin hnear
    have hcomp := hLip.comp_boundedVariationOn
      (show MapsTo (fun t => (f t : ℂ)) U V from fun _ ht => ht.2.1)
      (hBV.mono (show U ⊆ Icc a b from inter_subset_left))
    have hQpoint (t : ℝ) : Q (f t : ℂ) = g (p (f t)) := by
      change g (p (e.symm (f t : ℂ))) = g (p (f t))
      rw [← hecoe (f t), e.left_inv (hesource _)]
    refine ⟨g, hg, hgx, U, hU, inter_subset_left, fun _ ht => ht.2.2, ?_⟩
    change eVariationOn (fun t => g (p (f t))) U ≠ (⊤ : ENNReal)
    rw [← eVariationOn.congr (show EqOn (Q ∘ fun t => (f t : ℂ))
      (fun t => g (p (f t))) U from fun t _ => hQpoint t)]
    exact hcomp
  · intro hchart
    apply boundedVariationOn_Icc_of_nhdsWithin
    intro x hx
    obtain ⟨g, hg, hgx, U, hU, _hUsub, hUmap, hUBV⟩ := hchart x hx
    let e := chartAt ℂ (f x)
    have he : e ∈ (RiemannAtlas.ofManifold ℍ).charts := chart_mem_atlas ℂ (f x)
    have hecoe (z : ℍ) : e z = (z : ℂ) := rfl
    have hesource (z : ℍ) : z ∈ e.source := by change z ∈ (univ : Set ℍ); trivial
    obtain ⟨l, hfxl, hl⟩ := hpl (f x)
    let P := e.symm.trans (l.trans g)
    have hsub : P.source ⊆ riemannChartMapDomain e p g := by
      intro w hw
      change w ∈ e.target ∧ e.symm w ∈ l.source ∧ l (e.symm w) ∈ g.source at hw
      refine ⟨hw.1, ?_⟩
      change p (e.symm w) ∈ g.source
      rw [hl]
      exact hw.2.2
    have hP : AnalyticOnNhd ℂ P P.source := by
      apply AnalyticOnNhd.congr P.open_source ((hpa.2 e he g hg).mono hsub)
      intro w _hw
      change g (p (e.symm w)) = g (l (e.symm w))
      rw [hl]
    have hPx : e (f x) ∈ P.source := by
      change e (f x) ∈ e.target ∧ e.symm (e (f x)) ∈ l.source ∧
        l (e.symm (e (f x))) ∈ g.source
      rw [e.left_inv (hesource _), ← hl]
      exact ⟨e.map_source (hesource _), hfxl, hgx⟩
    have hPval (z : ℍ) : P (e z) = g (p z) := by
      change g (l (e.symm (e z))) = g (p z)
      rw [e.left_inv (hesource _), ← hl]
    have hPa : AnalyticAt ℂ P.symm (g (p (f x))) := by
      rw [← hPval (f x)]
      exact openPartialHomeomorph_analytic_inverse P hP _ (P.map_source hPx)
    obtain ⟨C, V, hV, hLip⟩ :=
      (hPa.contDiffAt : ContDiffAt ℂ 1 P.symm (g (p (f x)))).exists_lipschitzOnWith
    have hpc : ContinuousWithinAt (fun t => p (f t)) (Icc a b) x :=
      hpa.1.continuousAt.comp_continuousWithinAt (hf x hx)
    have hgc : ContinuousWithinAt (fun t => g (p (f t))) (Icc a b) x :=
      (g.continuousAt hgx).comp_continuousWithinAt hpc
    have hnear := ((hf x hx).eventually (l.open_source.mem_nhds hfxl)).and (hgc.eventually hV)
    let W := U ∩ {t : ℝ | f t ∈ l.source ∧ g (p (f t)) ∈ V}
    have hW : W ∈ 𝓝[Icc a b] x := inter_mem hU hnear
    have hcomp := hLip.comp_boundedVariationOn
      (show MapsTo (fun t => g (p (f t))) W V from fun _ ht => ht.2.2)
      (hUBV.mono (show W ⊆ U from inter_subset_left))
    have hPinv (t : ℝ) (ht : t ∈ W) : P.symm (g (p (f t))) = (f t : ℂ) := by
      have hPt : e (f t) ∈ P.source := by
        change e (f t) ∈ e.target ∧ e.symm (e (f t)) ∈ l.source ∧
          l (e.symm (e (f t))) ∈ g.source
        rw [e.left_inv (hesource _), ← hl]
        exact ⟨e.map_source (hesource _), ht.2.1, hUmap ht.1⟩
      have hinv := P.left_inv hPt
      rw [hPval (f t), hecoe] at hinv
      exact hinv
    refine ⟨W, hW, ?_⟩
    change eVariationOn (fun t => (f t : ℂ)) W ≠ (⊤ : ENNReal)
    rw [← eVariationOn.congr (show EqOn (P.symm ∘ fun t => g (p (f t)))
      (fun t => (f t : ℂ)) W from fun t ht => hPinv t ht)]
    exact hcomp

/-- The same original half-plane cover is analytic in the original surface
atlas, without selecting another surface or covering projection. -/
theorem HyperbolicSurfaceModel.halfPlaneCover_analytic
    {X : Type*} [TopologicalSpace X] {R : RiemannSurface X}
    (M : HyperbolicSurfaceModel R) :
    RiemannAnalyticMap (RiemannAtlas.ofManifold ℍ) R.toRiemannAtlas M.halfPlaneCover := by
  obtain ⟨e, he, _heinv⟩ := LiZhongQC.s22c6_cayley_diffeomorph
  have heq : (e : ℍ → standardUnitDiscOpens) = halfPlaneToDisc := by
    funext z
    apply Subtype.ext
    exact (he z).trans (show LiZhongQC.cayley (z : ℂ) = (halfPlaneToDisc z : ℂ) from rfl)
  have hcayley : RiemannAnalyticMap (RiemannAtlas.ofManifold ℍ)
      standardUnitDiscRiemannSurface.toRiemannAtlas halfPlaneToDisc := by
    rw [← heq]
    exact riemannAnalyticMap_of_contMDiff_ofManifold e.contMDiff_toFun
  have hE : RiemannAnalyticMap (RiemannAtlas.ofManifold ℍ)
      discRiemannSurface.toRiemannAtlas (cayleyHomeomorph.trans discFiniteHomeomorph.symm) :=
    (riemannAnalyticMap_homeomorph_symm standardUnitDiscHomeomorph
      standardUnitDiscHomeomorph_analytic).comp hcayley
  exact M.discCover_analytic.comp hE

/-- In the original surface atlas, a continuous lift is intrinsically
rectifiable exactly when the original projected curve is chartwise rectifiable. -/
theorem HyperbolicSurfaceModel.boundedVariation_iff_chartwiseBV
    {X : Type*} [TopologicalSpace X] {R : RiemannSurface X}
    (M : HyperbolicSurfaceModel R) {f : ℝ → ℍ} {a b : ℝ}
    (hf : ContinuousOn f (Icc a b)) :
    BoundedVariationOn f (Icc a b) ↔
      R.toRiemannAtlas.IsChartwiseBVOn (M.halfPlaneCover ∘ f) (Icc a b) :=
  halfPlane_boundedVariation_iff_original_chartwiseBV R.toRiemannAtlas
    M.halfPlaneCover_analytic M.halfPlaneCover_covering.isLocalHomeomorph hf

end LowDimensionalTopology.Geometry.Surfaces
