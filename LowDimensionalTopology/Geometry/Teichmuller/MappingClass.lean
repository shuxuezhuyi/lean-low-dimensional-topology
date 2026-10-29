module

public import LowDimensionalTopology.Geometry.Teichmuller.Space
public import Mathlib.Analysis.Calculus.FDeriv.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Congr

/-!
# Changing the marking of a closed Riemann surface

An orientation-preserving smooth automorphism of the reference surface acts by
precomposition of markings. This construction respects free homotopy of the
marked target maps and hence descends to Teichmüller equivalence classes.
-/

@[expose] public section

noncomputable section

open Set Filter Topology
open scoped Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller

open Surfaces

universe u v w

/-- A positive real Jacobian cannot be the totalized derivative of a
nondifferentiable map. -/
theorem differentiableAt_of_realJacobian_pos {f : ℂ → ℂ} {z : ℂ}
    (h : 0 < realJacobian f z) : DifferentiableAt ℝ f z := by
  by_contra hn
  have hz : realJacobian f z = 0 := by
    simp [realJacobian, fderiv_zero_of_not_differentiableAt hn]
  rw [hz] at h
  exact (lt_irrefl 0) h

/-- Orientation preservation composes through an actual intermediate chart. -/
theorem PreservesComplexOrientation.comp {X : Type u} {Y : Type v} {Z : Type w}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    {A : RiemannAtlas X} {B : RiemannAtlas Y} {C : RiemannAtlas Z}
    {f : X → Y} {g : Y → Z}
    (hg : PreservesComplexOrientation B C g)
    (hf : PreservesComplexOrientation A B f) (hfc : Continuous f) :
    PreservesComplexOrientation A C (g ∘ f) := by
  intro e he c hc z hz
  obtain ⟨b, hb, hy⟩ := B.cover (f (e.symm z))
  let F := riemannChartMap e f b
  let G := riemannChartMap b g c
  have hzF : z ∈ riemannChartMapDomain e f b := ⟨hz.1, hy⟩
  have hzG : F z ∈ riemannChartMapDomain b g c := by
    refine ⟨b.map_source hy, ?_⟩
    change g (b.symm (b (f (e.symm z)))) ∈ c.source
    rw [b.left_inv hy]
    exact hz.2
  have hFpos : 0 < realJacobian F z := hf e he b hb z hzF
  have hGpos : 0 < realJacobian G (F z) := hg b hb c hc (F z) hzG
  have hF := differentiableAt_of_realJacobian_pos hFpos
  have hG := differentiableAt_of_realJacobian_pos hGpos
  have hnear : ∀ᶠ t in 𝓝 z, f (e.symm t) ∈ b.source := by
    have ht : Tendsto (f ∘ e.symm) (𝓝 z) (𝓝 (f (e.symm z))) :=
      hfc.continuousAt.comp (e.continuousAt_symm hz.1)
    exact ht.eventually (b.open_source.mem_nhds hy)
  have heq : riemannChartMap e (g ∘ f) c =ᶠ[𝓝 z] G ∘ F := by
    filter_upwards [hnear] with t ht
    change c (g (f (e.symm t))) = c (g (b.symm (b (f (e.symm t)))))
    rw [b.left_inv ht]
  have hjac : realJacobian (riemannChartMap e (g ∘ f) c) z =
      realJacobian G (F z) * realJacobian F z := by
    unfold realJacobian
    rw [heq.fderiv_eq, fderiv_comp z hG hF]
    exact LinearMap.det_comp _ _
  rw [hjac]
  exact mul_pos hGpos hFpos

namespace SmoothSurfaceEquiv

variable {X : Type u} {Y : Type v} {Z : Type w}
variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
variable {A : RiemannSurface X} {B : RiemannSurface Y} {C : RiemannSurface Z}

/-- Composition of the actual real smooth surface diffeomorphisms. -/
def trans (f : SmoothSurfaceEquiv A B) (g : SmoothSurfaceEquiv B C) :
    SmoothSurfaceEquiv A C := by
  letI := A.toRiemannAtlas.toChartedSpace
  letI := B.toRiemannAtlas.toChartedSpace
  letI := C.toRiemannAtlas.toChartedSpace
  exact Diffeomorph.trans f g

@[simp]
theorem trans_toHomeomorph (f : SmoothSurfaceEquiv A B) (g : SmoothSurfaceEquiv B C) :
    (trans f g).toHomeomorph = f.toHomeomorph.trans g.toHomeomorph := rfl

end SmoothSurfaceEquiv

namespace MarkedRiemannSurface

variable {X : Type u} [TopologicalSpace X] {R : ClosedRiemannSurface X}

/-- Change only the marking, by an orientation-preserving smooth reference automorphism. -/
def precompose (f : SmoothSurfaceEquiv R.toRiemannSurface R.toRiemannSurface)
    (hf : PreservesComplexOrientation R.toRiemannAtlas R.toRiemannAtlas f.toHomeomorph)
    (M : MarkedRiemannSurface.{u, v} R) : MarkedRiemannSurface.{u, v} R where
  carrier := M.carrier
  topology := M.topology
  surface := M.surface
  marking := SmoothSurfaceEquiv.trans f M.marking
  orientation_preserving :=
    M.orientation_preserving.comp hf f.toHomeomorph.continuous

@[simp]
theorem precompose_markingMap
    (f : SmoothSurfaceEquiv R.toRiemannSurface R.toRiemannSurface)
    (hf : PreservesComplexOrientation R.toRiemannAtlas R.toRiemannAtlas f.toHomeomorph)
    (M : MarkedRiemannSurface.{u, v} R) :
    (precompose f hf M).markingMap =
      M.markingMap.comp (_root_.toContinuousMap f.toHomeomorph) := rfl

/-- Precomposition preserves the marked-target equivalence relation. -/
theorem equivalent_precompose
    (f : SmoothSurfaceEquiv R.toRiemannSurface R.toRiemannSurface)
    (hf : PreservesComplexOrientation R.toRiemannAtlas R.toRiemannAtlas f.toHomeomorph)
    {M N : MarkedRiemannSurface.{u, v} R} (hMN : Equivalent M N) :
    Equivalent (precompose f hf M) (precompose f hf N) := by
  obtain ⟨h, hanalytic, hmark⟩ := hMN
  refine ⟨h, hanalytic, ?_⟩
  exact hmark.comp (ContinuousMap.Homotopic.refl (_root_.toContinuousMap f.toHomeomorph))

@[simp]
theorem precompose_refl (M : MarkedRiemannSurface.{u, v} R) :
    precompose (SmoothSurfaceEquiv.refl R.toRiemannSurface)
      (preservesComplexOrientation_id R.toRiemannAtlas) M = M := by
  cases M
  rfl

/-- Changing a marking twice agrees with composition of the reference maps. -/
theorem precompose_trans
    (f g : SmoothSurfaceEquiv R.toRiemannSurface R.toRiemannSurface)
    (hf : PreservesComplexOrientation R.toRiemannAtlas R.toRiemannAtlas f.toHomeomorph)
    (hg : PreservesComplexOrientation R.toRiemannAtlas R.toRiemannAtlas g.toHomeomorph)
    (M : MarkedRiemannSurface.{u, v} R) :
    precompose f hf (precompose g hg M) =
      precompose (SmoothSurfaceEquiv.trans f g)
        (hg.comp hf f.toHomeomorph.continuous) M := by
  cases M
  rfl

/-- Homotopic reference automorphisms give equivalent changes of a marking. -/
theorem equivalent_precompose_of_homotopic
    (f g : SmoothSurfaceEquiv R.toRiemannSurface R.toRiemannSurface)
    (hf : PreservesComplexOrientation R.toRiemannAtlas R.toRiemannAtlas f.toHomeomorph)
    (hg : PreservesComplexOrientation R.toRiemannAtlas R.toRiemannAtlas g.toHomeomorph)
    (hfg : ContinuousMap.Homotopic (_root_.toContinuousMap f.toHomeomorph)
      (_root_.toContinuousMap g.toHomeomorph))
    (M : MarkedRiemannSurface.{u, v} R) :
    Equivalent (precompose f hf M) (precompose g hg M) := by
  refine ⟨Homeomorph.refl _, RiemannAnalyticMap.id _, ?_⟩
  exact (ContinuousMap.Homotopic.refl M.markingMap).comp hfg

end MarkedRiemannSurface

namespace TeichmullerSpace

variable {X : Type u} [TopologicalSpace X] {R : ClosedRiemannSurface X}

/-- The change of marking induced on actual Teichmüller equivalence classes. -/
def precompose (f : SmoothSurfaceEquiv R.toRiemannSurface R.toRiemannSurface)
    (hf : PreservesComplexOrientation R.toRiemannAtlas R.toRiemannAtlas f.toHomeomorph) :
    TeichmullerSpace.{u, v} R → TeichmullerSpace.{u, v} R :=
  Quotient.map (MarkedRiemannSurface.precompose f hf)
    (fun _ _ h ↦ MarkedRiemannSurface.equivalent_precompose f hf h)

@[simp]
theorem precompose_mk
    (f : SmoothSurfaceEquiv R.toRiemannSurface R.toRiemannSurface)
    (hf : PreservesComplexOrientation R.toRiemannAtlas R.toRiemannAtlas f.toHomeomorph)
    (M : MarkedRiemannSurface.{u, v} R) :
    precompose f hf (mk M) = mk (MarkedRiemannSurface.precompose f hf M) := rfl

@[simp]
theorem precompose_refl (p : TeichmullerSpace.{u, v} R) :
    precompose (SmoothSurfaceEquiv.refl R.toRiemannSurface)
      (preservesComplexOrientation_id R.toRiemannAtlas) p = p := by
  induction p using Quotient.inductionOn with
  | h M =>
      change mk (MarkedRiemannSurface.precompose _ _ M) = mk M
      rw [MarkedRiemannSurface.precompose_refl]

/-- The contravariant order of precomposition on Teichmüller points. -/
theorem precompose_trans
    (f g : SmoothSurfaceEquiv R.toRiemannSurface R.toRiemannSurface)
    (hf : PreservesComplexOrientation R.toRiemannAtlas R.toRiemannAtlas f.toHomeomorph)
    (hg : PreservesComplexOrientation R.toRiemannAtlas R.toRiemannAtlas g.toHomeomorph)
    (p : TeichmullerSpace.{u, v} R) :
    precompose f hf (precompose g hg p) =
      precompose (SmoothSurfaceEquiv.trans f g)
        (hg.comp hf f.toHomeomorph.continuous) p := by
  induction p using Quotient.inductionOn with
  | h M =>
      change mk (MarkedRiemannSurface.precompose f hf
        (MarkedRiemannSurface.precompose g hg M)) = _
      rw [MarkedRiemannSurface.precompose_trans]
      rfl

/-- The action of a reference map depends only on its free homotopy class. -/
theorem precompose_eq_of_homotopic
    (f g : SmoothSurfaceEquiv R.toRiemannSurface R.toRiemannSurface)
    (hf : PreservesComplexOrientation R.toRiemannAtlas R.toRiemannAtlas f.toHomeomorph)
    (hg : PreservesComplexOrientation R.toRiemannAtlas R.toRiemannAtlas g.toHomeomorph)
    (hfg : ContinuousMap.Homotopic (_root_.toContinuousMap f.toHomeomorph)
      (_root_.toContinuousMap g.toHomeomorph))
    (p : TeichmullerSpace.{u, v} R) : precompose f hf p = precompose g hg p := by
  induction p using Quotient.inductionOn with
  | h M =>
      exact (mk_eq_mk_iff _ _).2
        (MarkedRiemannSurface.equivalent_precompose_of_homotopic f g hf hg hfg M)

end TeichmullerSpace

end LowDimensionalTopology.Geometry.Teichmuller
