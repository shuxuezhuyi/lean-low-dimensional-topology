/-
Proofs adapted from Wu Xiaobin's Li-Zhong-QC-formalization,
commit 1c0d5473c020b66ed5106331a38a61536760b9b2.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Quasiconformal.DistributionalPartials
public import Mathlib.MeasureTheory.Function.LpSeminorm.SMul
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum

/-!
# Ordinary and distributional Wirtinger derivatives

The actual almost-everywhere ordinary derivatives of a quasiconformal map are
locally square integrable. They represent its complex distributional derivatives
against every genuinely smooth compactly supported test function. Local
integrability is part of the distributional predicate, and all integrability
needed to combine the coordinate integration-by-parts formulas is proved.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter Topology Complex
open scoped ContDiff

namespace LowDimensionalTopology.Geometry.Quasiconformal

/-- Genuine distributional holomorphic and antiholomorphic derivatives, including
local integrability and all actual smooth compactly supported complex tests. -/
def HasDistributionalWirtingerDerivatives (f fz fzb : ℂ → ℂ) (U : Set ℂ) : Prop :=
  LocallyIntegrableOn f U ∧ LocallyIntegrableOn fz U ∧ LocallyIntegrableOn fzb U ∧
    ∀ ψ : ℂ → ℂ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ U →
      (∫ z in U, f z * LiZhongQC.dz ψ z) = -∫ z in U, ψ z * fz z ∧
        (∫ z in U, f z * LiZhongQC.dzbar ψ z) = -∫ z in U, ψ z * fzb z

/-- The ordinary Wirtinger derivatives lie in L2 on every compact subset of the
original open domain, without assuming global square integrability. -/
theorem quasiconformal_wirtinger_locally_L2 {f : ℂ → ℂ} {U : Set ℂ} {K : ℝ}
    (hf : LiZhongQC.IsKQC f U K) :
    ∀ C ⊆ U, IsCompact C →
      MemLp (LiZhongQC.dz f) 2 (volume.restrict C) ∧
        MemLp (LiZhongQC.dzbar f) 2 (volume.restrict C) := by
  intro C hCU hCc
  obtain ⟨hx, hy⟩ := quasiconformal_ordinary_partials_locally_L2 hf C hCU hCc
  refine ⟨?_, ?_⟩
  · change MemLp (fun z => (fderiv ℝ f z 1 - I * fderiv ℝ f z I) / 2)
      2 (volume.restrict C)
    simpa only [div_eq_mul_inv, Pi.sub_apply, Pi.mul_apply] using
      (hx.sub (hy.const_mul I)).mul_const ((2 : ℂ)⁻¹)
  · change MemLp (fun z => (fderiv ℝ f z 1 + I * fderiv ℝ f z I) / 2)
      2 (volume.restrict C)
    simpa only [div_eq_mul_inv, Pi.add_apply, Pi.mul_apply] using
      (hx.add (hy.const_mul I)).mul_const ((2 : ℂ)⁻¹)

private theorem locallyIntegrableOn_of_local_L2 {g : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hg : ∀ C ⊆ U, IsCompact C → MemLp g 2 (volume.restrict C)) :
    LocallyIntegrableOn g U := by
  apply (locallyIntegrableOn_iff hU.isLocallyClosed).mpr
  intro C hCU hCc
  let : IsFiniteMeasure (volume.restrict C) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hCc.measure_lt_top⟩
  exact MemLp.integrable (by norm_num) (hg C hCU hCc)

/-- Integration by parts for the ordinary holomorphic derivative. Its negative
complex coefficient is retained explicitly when combining the two real directions. -/
theorem quasiconformal_integral_dz {f : ℂ → ℂ} {U : Set ℂ} {K : ℝ}
    (hf : LiZhongQC.IsKQC f U K) {ψ : ℂ → ℂ}
    (hψ : ContDiff ℝ 1 ψ) (hcψ : HasCompactSupport ψ) (hsψ : tsupport ψ ⊆ U) :
    ∫ z in U, f z * LiZhongQC.dz ψ z = -∫ z in U, ψ z * LiZhongQC.dz f z := by
  have hv := (LiZhongQC.thm9_5_L2_derivatives hf).1
  obtain ⟨h1, hI⟩ := LiZhongQC.sp_ibp hf.1 hv hψ hcψ hsψ
  have hKc : IsCompact (tsupport ψ) := hcψ.isCompact
  have hKm : MeasurableSet (tsupport ψ) := hKc.isClosed.measurableSet
  have hψ0 : ∀ z ∉ tsupport ψ, ψ z = 0 := fun z hz => image_eq_zero_of_notMem_tsupport hz
  have hint1 : ∀ e : ℂ, IntegrableOn (fun z => fderiv ℝ ψ z e * f z) U := by
    intro e
    have hdψc : Continuous (fun z => fderiv ℝ ψ z e) :=
      (hψ.continuous_fderiv one_ne_zero).clm_apply continuous_const
    refine (LiZhongQC.sp_ibp_integrable_of_support hKm ?_ fun z hz => by
      rw [LiZhongQC.sp_fderiv_eq_zero_of_notMem_tsupport hz e, zero_mul]).integrableOn
    exact (hdψc.continuousOn.mul (hf.2.2.1.1.mono hsψ)).integrableOn_compact hKc
  have hψL : MemLp ψ 2 (volume.restrict (tsupport ψ)) :=
    (hψ.continuous.memLp_of_hasCompactSupport (μ := volume) hcψ).restrict _
  have hint2 : ∀ g : ℂ → ℂ, MemLp g 2 (volume.restrict (tsupport ψ)) →
      IntegrableOn (fun z => ψ z * g z) U := fun g hg =>
    (LiZhongQC.sp_ibp_integrable_of_support hKm (hψL.integrable_mul hg) fun z hz => by
      rw [Pi.mul_apply, hψ0 z hz, zero_mul]).integrableOn
  have hgx := hint2 _ (hv.1 _ hsψ hKc).1
  have hgy := hint2 _ (hv.1 _ hsψ hKc).2
  have hae : ∀ᵐ z ∂(volume.restrict U), ψ z * LiZhongQC.dz f z =
      (ψ z * LiZhongQC.partialX f z - I * (ψ z * LiZhongQC.partialY f z)) / 2 := by
    filter_upwards [quasiconformal_differentiable_ae hf] with z hz
    rw [LiZhongQC.partialX_eq_of_differentiableAt hz, LiZhongQC.partialY_eq_of_differentiableAt hz]
    unfold LiZhongQC.dz
    ring
  have hL : ∫ z in U, f z * LiZhongQC.dz ψ z =
      ((∫ z in U, fderiv ℝ ψ z 1 * f z) - I * ∫ z in U, fderiv ℝ ψ z I * f z) / 2 := by
    rw [← integral_const_mul, ← integral_sub (hint1 1) ((hint1 I).const_mul I), ← integral_div]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    simp only [LiZhongQC.dz]
    ring
  have hR : ∫ z in U, ψ z * LiZhongQC.dz f z =
      ((∫ z in U, ψ z * LiZhongQC.partialX f z) - I * ∫ z in U, ψ z * LiZhongQC.partialY f z) / 2 := by
    rw [integral_congr_ae hae, ← integral_const_mul, ← integral_sub hgx (hgy.const_mul I),
      ← integral_div]
  rw [hL, hR, h1, hI]
  ring

/-- Both ordinary complex partial derivatives of a quasiconformal map are genuine
distributional derivatives, with local integrability and actual smooth tests. -/
theorem quasiconformal_distributional_wirtinger_derivatives
    {f : ℂ → ℂ} {U : Set ℂ} {K : ℝ} (hf : LiZhongQC.IsKQC f U K) :
    HasDistributionalWirtingerDerivatives f (LiZhongQC.dz f) (LiZhongQC.dzbar f) U := by
  refine ⟨hf.2.2.1.1.locallyIntegrableOn hf.1.measurableSet,
    locallyIntegrableOn_of_local_L2 hf.1 (fun C hCU hCc =>
      (quasiconformal_wirtinger_locally_L2 hf C hCU hCc).1),
    locallyIntegrableOn_of_local_L2 hf.1 (fun C hCU hCc =>
      (quasiconformal_wirtinger_locally_L2 hf C hCU hCc).2), ?_⟩
  intro ψ hψ hcψ hsψ
  exact ⟨quasiconformal_integral_dz hf (hψ.of_le (by simp)) hcψ hsψ,
    LiZhongQC.abW_ibp hf (hψ.of_le (by simp)) hcψ hsψ⟩

/-- Vanishing of the actual ordinary antiholomorphic derivative almost everywhere
gives the actual smooth-test distributional condition used by the native Weyl lemma. -/
theorem quasiconformal_distributional_dbar_zero_of_ae_zero
    {f : ℂ → ℂ} {U : Set ℂ} {K : ℝ} (hf : LiZhongQC.IsKQC f U K)
    (hz : ∀ᵐ z ∂(volume.restrict U), LiZhongQC.dzbar f z = 0) :
    HasDistributionalDbarZero f U := by
  intro ψ hψ hcψ hsψ
  rw [LiZhongQC.abW_ibp hf (hψ.of_le (by simp)) hcψ hsψ]
  have hi : (∫ z in U, ψ z * LiZhongQC.dzbar f z) = 0 := by
    calc _ = ∫ _z in U, (0 : ℂ) := integral_congr_ae (hz.mono fun z h => by rw [h, mul_zero])
      _ = 0 := by simp
  rw [hi, neg_zero]

/-- The smooth-test Weyl lemma applies directly to the ordinary derivative of an
actual quasiconformal map; the distributional bridge is proved explicitly. -/
theorem quasiconformal_holomorphic_of_dbar_zero_ae
    {f : ℂ → ℂ} {U : Set ℂ} {K : ℝ} (hf : LiZhongQC.IsKQC f U K)
    (hz : ∀ᵐ z ∂(volume.restrict U), LiZhongQC.dzbar f z = 0) :
    DifferentiableOn ℂ f U :=
  holomorphic_of_distributional_dbar_zero hf.1 hf.2.2.1.1
    (quasiconformal_distributional_dbar_zero_of_ae_zero hf hz)

end LowDimensionalTopology.Geometry.Quasiconformal
