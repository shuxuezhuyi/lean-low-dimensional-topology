module

public import LowDimensionalTopology.Geometry.Quasiconformal.WeakLpRigidity
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# Affine rigidity from actual weak derivatives on the plane

The given distributional holomorphic derivative is identified almost everywhere
with the actual classical derivative of the entire function. Finite Lp distance
from one then forces the classical derivative to equal one, and the original
function differs from the identity only by its actual value at zero.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Complex Set MeasureTheory Filter Topology
open scoped ContDiff ENNReal
open LiZhongQC

namespace LowDimensionalTopology.Geometry.Quasiconformal

/-- The given genuine weak holomorphic derivative of an actual entire function
equals its actual classical derivative almost everywhere. -/
theorem distributional_dz_eq_deriv_of_entire {F g h : ℂ → ℂ}
    (hF : Differentiable ℂ F) (hw : HasDistributionalWirtingerDerivatives F g h univ) :
    g =ᵐ[volume] deriv F := by
  have hF1 : ContDiff ℝ 1 F :=
    (show ContDiff ℂ 1 F from hF.contDiff).restrict_scalars ℝ
  apply ae_eq_of_integral_contDiff_smul_eq (locallyIntegrableOn_univ.mp hw.2.1)
    hF.deriv.continuous.locallyIntegrable
  intro ψ hψ hcψ
  let ψc : ℂ → ℂ := fun z => (ψ z : ℂ)
  have hψc : ContDiff ℝ ∞ ψc := Complex.ofRealCLM.contDiff.comp hψ
  have hcψc : HasCompactSupport ψc :=
    hcψ.comp_left (g := fun x : ℝ => (x : ℂ)) rfl
  have hwtest : (∫ z, F z * dz ψc z) = -∫ z, ψc z * g z := by
    simpa only [Measure.restrict_univ] using (hw.2.2.2 ψc hψc hcψc (subset_univ _)).1
  have hψc1 : ContDiff ℝ 1 ψc := hψc.of_le (by simp)
  have hibp := (c1_wirtinger_integral_by_parts hF1 hψc1 hcψc).1
  have heq : (∫ z, ψc z * g z) = ∫ z, ψc z * dz F z :=
    neg_injective (hwtest.symm.trans hibp)
  have hdz (z : ℂ) : dz F z = deriv F z := dz_eq_deriv (hF z)
  simpa only [ψc, Complex.real_smul, hdz] using heq

/-- A genuine distributional derivative which vanishes almost everywhere
gives the same actual smooth-test zero condition used by the Weyl theorem. -/
theorem distributional_dbar_zero_of_ae_zero {F g h : ℂ → ℂ}
    (hw : HasDistributionalWirtingerDerivatives F g h univ) (hh : h =ᵐ[volume] 0) :
    HasDistributionalDbarZero F univ := by
  intro ψ hψ hcψ hsψ
  have hz : (∫ z in univ, ψ z * h z) = 0 := by
    rw [Measure.restrict_univ]
    calc
      _ = ∫ z, (0 : ℂ) := integral_congr_ae (hh.mono fun z hz => by
        rw [hz, Pi.zero_apply, mul_zero])
      _ = 0 := integral_zero ℂ ℂ (μ := (volume : Measure ℂ))
  simpa only [hz, neg_zero] using (hw.2.2.2 ψ hψ hcψ hsψ).2

/-- An entire function whose actual weak derivative differs from one in finite
Lp is the identity plus its actual value at zero. -/
theorem entire_eq_add_value_zero_of_distributional_memLp {F g h : ℂ → ℂ} {p : ℝ}
    (hp : 1 < p) (hF : Differentiable ℂ F)
    (hw : HasDistributionalWirtingerDerivatives F g h univ)
    (hmem : MemLp (fun z => g z - 1) (ENNReal.ofReal p) (volume : Measure ℂ)) :
    ∀ z, F z = z + F 0 := by
  have hgeq := distributional_dz_eq_deriv_of_entire hF hw
  have hmem' : MemLp (fun z => deriv F z - 1) (ENNReal.ofReal p)
      (volume : Measure ℂ) :=
    MemLp.ae_eq (f := fun z => g z - 1) (g := fun z => deriv F z - 1)
      (hgeq.mono fun z hz => congrArg (fun w : ℂ => w - 1) hz) hmem
  have hzero : (fun z => deriv F z - 1) = 0 :=
    entire_eq_zero_of_memLp hp (hF.deriv.sub_const 1) hmem'
  have hderiv (z : ℂ) : deriv F z = 1 := by
    have hz := congrFun hzero z
    exact sub_eq_zero.mp hz
  have hFd : Differentiable ℂ (fun z => F z - z) := hF.sub differentiable_id
  have hFd0 (z : ℂ) : deriv (fun w => F w - w) z = 0 := by
    have hd : HasDerivAt (fun w => F w - w) (deriv F z - 1) z :=
      (hF z).hasDerivAt.fun_sub (hasDerivAt_id' z)
    simpa only [hderiv z, sub_self] using hd.deriv
  intro z
  have heq : F z - z = F 0 := by
    simpa only [sub_zero] using is_const_of_deriv_eq_zero hFd hFd0 z 0
  calc
    F z = (F z - z) + z := (sub_add_cancel (F z) z).symm
    _ = F 0 + z := congrArg (fun w : ℂ => w + z) heq
    _ = z + F 0 := add_comm _ _

/-- A continuous globally weakly holomorphic function with weak derivative
at finite Lp distance from one is exactly the identity plus its value at zero. -/
theorem weak_primitive_eq_add_value_zero {F g h : ℂ → ℂ} {p : ℝ}
    (hp : 1 < p) (hF : Continuous F)
    (hw : HasDistributionalWirtingerDerivatives F g h univ) (hh : h =ᵐ[volume] 0)
    (hmem : MemLp (fun z => g z - 1) (ENNReal.ofReal p) (volume : Measure ℂ)) :
    ∀ z, F z = z + F 0 := by
  have hhol : Differentiable ℂ F := differentiableOn_univ.mp
    (holomorphic_of_distributional_dbar_zero isOpen_univ hF.continuousOn
      (distributional_dbar_zero_of_ae_zero hw hh))
  exact entire_eq_add_value_zero_of_distributional_memLp hp hhol hw hmem

end LowDimensionalTopology.Geometry.Quasiconformal
