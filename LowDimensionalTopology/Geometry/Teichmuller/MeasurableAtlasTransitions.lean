module

public import LowDimensionalTopology.Geometry.Surfaces.Riemann.Atlas
public import LowDimensionalTopology.External.LiZhongQC.Ch06.S23_QCOnSurfaces

/-!
# Almost-everywhere transport through every original atlas transition

Actual holomorphic chart transitions are conformal, hence one-quasiconformal.
Their null-set pullback theorem transports measurable coefficient classes and
preserves every almost-everywhere bound after the genuine Beltrami phase.
All charts below are arbitrary members of the original native atlas.
-/

@[expose] public section
noncomputable section

open Set MeasureTheory
open scoped ComplexConjugate

namespace LowDimensionalTopology.Geometry.Surfaces.RiemannAtlas

universe u
variable {X : Type u} [TopologicalSpace X]

/-- Every original holomorphic chart transition is actually one-quasiconformal. -/
theorem transition_isKQC (A : RiemannAtlas X) (e f : OpenPartialHomeomorph X ℂ)
    (he : e ∈ A.charts) (hf : f ∈ A.charts) :
    LiZhongQC.IsKQC (e.symm.trans f) (e.symm.trans f).source 1 := by
  apply LiZhongQC.isKQC_one_of_conformal (e.symm.trans f).open_source
  exact ⟨fun z hz => (A.compatible e he f hf z hz).differentiableAt.differentiableWithinAt,
    (e.symm.trans f).injOn, rfl⟩

/-- A null assertion on the target chart remains null after the actual transition. -/
theorem transition_ae_pullback (A : RiemannAtlas X) (e f : OpenPartialHomeomorph X ℂ)
    (he : e ∈ A.charts) (hf : f ∈ A.charts) {P : ℂ → Prop}
    (hP : ∀ᵐ z ∂(volume.restrict f.target), P z) :
    ∀ᵐ z ∂(volume.restrict (e.symm.trans f).source), P ((e.symm.trans f) z) := by
  apply LiZhongQC.s23_c2_ae_pullback (A.transition_isKQC e f he hf) ?_ hP
  rintro _ ⟨z, hz, rfl⟩
  exact ((e.symm.trans f).map_source hz).1

/-- Actual measurable representatives compose through all original chart transitions. -/
theorem transition_aestronglyMeasurable (A : RiemannAtlas X) (e f : OpenPartialHomeomorph X ℂ)
    (he : e ∈ A.charts) (hf : f ∈ A.charts) {μ : ℂ → ℂ}
    (hμ : AEStronglyMeasurable μ (volume.restrict f.target)) :
    AEStronglyMeasurable (μ ∘ (e.symm.trans f))
      (volume.restrict (e.symm.trans f).source) := by
  have hm : AEStronglyMeasurable (hμ.mk μ ∘ (e.symm.trans f))
      (volume.restrict (e.symm.trans f).source) :=
    (hμ.stronglyMeasurable_mk.measurable.comp_aemeasurable
      ((e.symm.trans f).continuousOn.aemeasurable
        (e.symm.trans f).open_source.measurableSet)).aestronglyMeasurable
  have heq : μ ∘ (e.symm.trans f) =ᵐ[volume.restrict (e.symm.trans f).source]
      hμ.mk μ ∘ (e.symm.trans f) :=
    A.transition_ae_pullback e f he hf hμ.ae_eq_mk
  exact hm.congr heq.symm

/-- The actual transition factor of a Beltrami tensor. -/
def transitionBeltramiPhase (e f : OpenPartialHomeomorph X ℂ) (z : ℂ) : ℂ :=
  conj (deriv (e.symm.trans f) z) / deriv (e.symm.trans f) z

/-- The transition factor has modulus one on its genuine domain. -/
theorem norm_transitionBeltramiPhase (A : RiemannAtlas X) (e f : OpenPartialHomeomorph X ℂ)
    (he : e ∈ A.charts) (hf : f ∈ A.charts) {z : ℂ} (hz : z ∈ (e.symm.trans f).source) :
    ‖transitionBeltramiPhase e f z‖ = 1 := by
  rw [transitionBeltramiPhase, norm_div, Complex.norm_conj,
    div_self (norm_ne_zero_iff.mpr (A.transition_deriv_ne_zero e f he hf z hz))]

/-- A measurable coefficient retains its exact bound after the genuine tensor change. -/
theorem transition_isBeltramiCoeff (A : RiemannAtlas X) (e f : OpenPartialHomeomorph X ℂ)
    (he : e ∈ A.charts) (hf : f ∈ A.charts) {μ : ℂ → ℂ} {k : ℝ}
    (hμ : LiZhongQC.IsBeltramiCoeff μ f.target k) :
    LiZhongQC.IsBeltramiCoeff
      (fun z => μ ((e.symm.trans f) z) * transitionBeltramiPhase e f z)
      (e.symm.trans f).source k := by
  have hd : ContinuousOn (deriv (e.symm.trans f)) (e.symm.trans f).source :=
    (A.compatible e he f hf).deriv.continuousOn
  have hphase : ContinuousOn (transitionBeltramiPhase e f) (e.symm.trans f).source :=
    (Complex.continuous_conj.comp_continuousOn hd).div hd
      (fun z hz => A.transition_deriv_ne_zero e f he hf z hz)
  refine ⟨(A.transition_aestronglyMeasurable e f he hf hμ.1).mul
    (hphase.aestronglyMeasurable (e.symm.trans f).open_source.measurableSet), ?_⟩
  filter_upwards [A.transition_ae_pullback e f he hf hμ.2,
    ae_restrict_mem (e.symm.trans f).open_source.measurableSet] with z hb hz
  rw [norm_mul, A.norm_transitionBeltramiPhase e f he hf hz, mul_one]
  exact hb

end LowDimensionalTopology.Geometry.Surfaces.RiemannAtlas
