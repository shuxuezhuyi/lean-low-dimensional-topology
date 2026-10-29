/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Quasiconformal.WeakHolomorphic
public import LowDimensionalTopology.Geometry.Quasiconformal.AnalyticGeometric
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.Tactic.NormNum

/-!
# Genuine distributional partial derivatives

The weak derivative is tested against actual smooth compactly supported functions,
and both the function and its derivative are required to be locally integrable.
The bridge from smooth approximation uses the already proved integration-by-parts
and L2 integral-limit arguments of Wu Xiaobin's fixed external source,
commit 1c0d5473c020b66ed5106331a38a61536760b9b2. The source retains its author,
license and compatibility records.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter Topology Complex
open scoped ContDiff

namespace LowDimensionalTopology.Geometry.Quasiconformal

/-- The distributional derivative in direction `v`, with genuine local integrability
and all actual smooth compactly supported complex test functions. -/
def HasDistributionalPartial (f g : ℂ → ℂ) (U : Set ℂ) (v : ℂ) : Prop :=
  LocallyIntegrableOn f U ∧ LocallyIntegrableOn g U ∧
    ∀ ψ : ℂ → ℂ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ U →
      (∫ z in U, fderiv ℝ ψ z v * f z) = -∫ z in U, ψ z * g z

/-- Both ordinary coordinate directions carry the asserted distributional derivatives. -/
def HasDistributionalPartials (f fx fy : ℂ → ℂ) (U : Set ℂ) : Prop :=
  HasDistributionalPartial f fx U 1 ∧ HasDistributionalPartial f fy U I

/-- Local L2 smooth approximation gives genuine distributional derivatives, through
proved integration by parts and convergence of the actual test-function integrals. -/
theorem hasDistributionalPartials_of_generalized {f fx fy : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hf : LiZhongQC.HasGenPartials f fx fy U 2) :
    HasDistributionalPartials f fx fy U := by
  have hfc : ContinuousOn f U := by
    obtain ⟨_, fn, hfn, hconv, _⟩ := hf
    exact hconv.continuousOn (Filter.Frequently.of_forall fun n => (hfn n).continuousOn)
  have hfint : LocallyIntegrableOn f U := hfc.locallyIntegrableOn hU.measurableSet
  have hfxint : LocallyIntegrableOn fx U := by
    apply (locallyIntegrableOn_iff hU.isLocallyClosed).mpr
    intro C hCU hCc
    let : IsFiniteMeasure (volume.restrict C) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact hCc.measure_lt_top⟩
    exact MemLp.integrable (by norm_num) (hf.1 C hCU hCc).1
  have hfyint : LocallyIntegrableOn fy U := by
    apply (locallyIntegrableOn_iff hU.isLocallyClosed).mpr
    intro C hCU hCc
    let : IsFiniteMeasure (volume.restrict C) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact hCc.measure_lt_top⟩
    exact MemLp.integrable (by norm_num) (hf.1 C hCU hCc).2
  refine ⟨⟨hfint, hfxint, ?_⟩, ⟨hfint, hfyint, ?_⟩⟩
  · intro ψ hψ hcψ hsψ
    exact (LiZhongQC.sp_ibp hU hf (hψ.of_le (by simp)) hcψ hsψ).1
  · intro ψ hψ hcψ hsψ
    exact (LiZhongQC.sp_ibp hU hf (hψ.of_le (by simp)) hcψ hsψ).2

/-- Almost-everywhere changes of the derivative preserve the actual distributional identity. -/
theorem HasDistributionalPartial.congr_derivative {f g g' : ℂ → ℂ} {U : Set ℂ} {v : ℂ}
    (hf : HasDistributionalPartial f g U v) (hgg' : g =ᵐ[volume.restrict U] g') :
    HasDistributionalPartial f g' U v := by
  refine ⟨hf.1, LocallyIntegrableOn.congr hgg' hf.2.1, ?_⟩
  intro ψ hψ hcψ hsψ
  calc (∫ z in U, fderiv ℝ ψ z v * f z) = -∫ z in U, ψ z * g z :=
      hf.2.2 ψ hψ hcψ hsψ
    _ = -∫ z in U, ψ z * g' z := by
      apply congrArg Neg.neg
      exact integral_congr_ae (hgg'.mono fun z hz => congrArg (fun w => ψ z * w) hz)

/-- Both coordinate distributional derivatives respect almost-everywhere equality. -/
theorem HasDistributionalPartials.congr_derivatives {f fx fy fx' fy' : ℂ → ℂ} {U : Set ℂ}
    (hf : HasDistributionalPartials f fx fy U)
    (hx : fx =ᵐ[volume.restrict U] fx') (hy : fy =ᵐ[volume.restrict U] fy') :
    HasDistributionalPartials f fx' fy' U :=
  ⟨hf.1.congr_derivative hx, hf.2.congr_derivative hy⟩

/-- The actual ordinary real coordinate derivatives of a quasiconformal map lie
in L2 on every compact subset of its original open domain. -/
theorem quasiconformal_ordinary_partials_locally_L2 {f : ℂ → ℂ} {U : Set ℂ} {K : ℝ}
    (hf : LiZhongQC.IsKQC f U K) :
    ∀ C ⊆ U, IsCompact C →
      MemLp (fun z => fderiv ℝ f z 1) 2 (volume.restrict C) ∧
        MemLp (fun z => fderiv ℝ f z I) 2 (volume.restrict C) := by
  intro C hCU hCc
  have hgen := (LiZhongQC.thm9_5_L2_derivatives hf).1
  have hdiff : ∀ᵐ z ∂(volume.restrict C), DifferentiableAt ℝ f z :=
    ae_restrict_of_ae_restrict_of_subset hCU (quasiconformal_differentiable_ae hf)
  refine ⟨?_, ?_⟩
  · exact (memLp_congr_ae
      (hdiff.mono fun z hz => LiZhongQC.partialX_eq_of_differentiableAt hz)).mp
        (hgen.1 C hCU hCc).1
  · exact (memLp_congr_ae
      (hdiff.mono fun z hz => LiZhongQC.partialY_eq_of_differentiableAt hz)).mp
        (hgen.1 C hCU hCc).2

/-- The actual almost-everywhere ordinary coordinate derivatives of a quasiconformal
map are its genuine distributional derivatives against every smooth compact test. -/
theorem quasiconformal_ordinary_distributional_partials {f : ℂ → ℂ} {U : Set ℂ} {K : ℝ}
    (hf : LiZhongQC.IsKQC f U K) :
    HasDistributionalPartials f (fun z => fderiv ℝ f z 1) (fun z => fderiv ℝ f z I) U := by
  have hgen := (LiZhongQC.thm9_5_L2_derivatives hf).1
  have hweak := hasDistributionalPartials_of_generalized hf.1 hgen
  have hdiff := quasiconformal_differentiable_ae hf
  exact hweak.congr_derivatives
    (hdiff.mono fun z hz => LiZhongQC.partialX_eq_of_differentiableAt hz)
    (hdiff.mono fun z hz => LiZhongQC.partialY_eq_of_differentiableAt hz)

end LowDimensionalTopology.Geometry.Quasiconformal
