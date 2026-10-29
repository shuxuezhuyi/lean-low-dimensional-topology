/-
The actual Pompeiu formula and its Lp approximation proof are due to Wu Xiaobin,
Li-Zhong-QC-formalization commit 1c0d5473c020b66ed5106331a38a61536760b9b2.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Quasiconformal.WirtingerWeakApproximation

/-!
# Pompeiu's formula for genuine weak Wirtinger derivatives

Continuity and the actual local Lp weak derivatives, for p>2, give the boundary
circle and area formula on every compactly contained disk. The area kernel is
proved integrable and the actual boundary integrand is circle integrable.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set Metric MeasureTheory Filter Topology Complex
open scoped ENNReal Real
open LiZhongQC

namespace LowDimensionalTopology.Geometry.Quasiconformal

/-- The area term is genuinely integrable for local Lp data with p>2. -/
theorem pompeiu_area_integrable_of_local_memLp
    {h : ℂ → ℂ} {U : Set ℂ} {c z₀ : ℂ} {R p : ℝ}
    (hp : 2 < p) (hsub : closedBall c R ⊆ U)
    (hloc : ∀ C ⊆ U, IsCompact C → MemLp h (ENNReal.ofReal p) (volume.restrict C)) :
    IntegrableOn (fun z => h z / (z - z₀)) (ball c R) := by
  have hC : IsCompact (closedBall c R) := isCompact_closedBall c R
  have hball : MemLp h (ENNReal.ofReal p) (volume.restrict (ball c R)) :=
    (hloc _ hsub hC).mono_measure (Measure.restrict_mono ball_subset_closedBall le_rfl)
  have hind : MemLp ((ball c R).indicator h) (ENNReal.ofReal p) (volume : Measure ℂ) :=
    (memLp_indicator_iff_restrict measurableSet_ball.nullMeasurableSet).2 hball
  obtain ⟨S, hS, hSC⟩ := hC.isBounded.exists_pos_norm_le
  have hsupp : ∀ z, S < ‖z‖ → (ball c R).indicator h z = 0 := by
    intro z hz
    have hzB : z ∉ ball c R := fun hzB =>
      (not_le_of_gt hz) (hSC z (ball_subset_closedBall hzB))
    exact indicator_of_notMem hzB h
  have hint := integrable_cauchyT_kernel hp hS hind hsupp z₀
  have hintB : IntegrableOn (fun z => (ball c R).indicator h z / (z - z₀)) (ball c R) :=
    hint.integrableOn
  apply hintB.congr
  filter_upwards [self_mem_ae_restrict measurableSet_ball] with z hz
  rw [indicator_of_mem hz]

/-- The actual boundary term is circle integrable, since its pole is strictly
inside the disk and the original function is continuous on the closed disk. -/
theorem pompeiu_boundary_circleIntegrable {f : ℂ → ℂ} {U : Set ℂ}
    (hf : ContinuousOn f U) {c z₀ : ℂ} {R : ℝ} (hR : 0 < R)
    (hsub : closedBall c R ⊆ U) (hz₀ : z₀ ∈ ball c R) :
    CircleIntegrable (fun z => f z / (z - z₀)) c R := by
  apply ContinuousOn.circleIntegrable hR.le
  refine (hf.mono (sphere_subset_closedBall.trans hsub)).div
    (continuousOn_id.sub continuousOn_const) ?_
  intro z hz hzero
  have hzEq : z = z₀ := sub_eq_zero.mp hzero
  have hsphere := mem_sphere.mp hz
  rw [hzEq] at hsphere
  exact (mem_ball.mp hz₀).ne hsphere

/-- The full boundary-circle and area formula from genuine weak Lp Wirtinger
data. The open-domain and compact-local hypotheses also cover the global Lp case. -/
theorem pompeiu_of_distributional_wirtinger
    {f g h : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) (hf : ContinuousOn f U)
    (hw : HasDistributionalWirtingerDerivatives f g h U)
    {p : ℝ} (hp : 2 < p)
    (hloc : ∀ C ⊆ U, IsCompact C →
      MemLp g (ENNReal.ofReal p) (volume.restrict C) ∧
        MemLp h (ENNReal.ofReal p) (volume.restrict C))
    {c z₀ : ℂ} {R : ℝ} (hR : 0 < R) (hsub : closedBall c R ⊆ U)
    (hz₀ : z₀ ∈ ball c R) :
    f z₀ = (1 / (2 * π * I)) * (∮ z in C(c, R), f z / (z - z₀)) -
      (1 / π : ℂ) * ∫ z in ball c R, h z / (z - z₀) := by
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (le_trans one_le_two hp.le)
  have hreal : ∀ C ⊆ U, IsCompact C →
      MemLp (fun z => g z + h z) (ENNReal.ofReal p) (volume.restrict C) ∧
        MemLp (fun z => I * (g z - h z)) (ENNReal.ofReal p) (volume.restrict C) := by
    intro C hCU hC
    obtain ⟨hg, hh⟩ := hloc C hCU hC
    refine ⟨MemLp.ae_eq (f := g + h) (g := fun z => g z + h z)
      (Eventually.of_forall fun z => Pi.add_apply g h z) (hg.add hh), ?_⟩
    exact MemLp.ae_eq (f := fun z => I * (g - h) z)
      (g := fun z => I * (g z - h z))
      (Eventually.of_forall fun z => by
        change I * (g - h) z = I * (g z - h z)
        rw [Pi.sub_apply]) ((hg.sub hh).const_mul I)
  have hgen := hasGenPartials_of_distributional hU hf hw.real_partials hp1
    ENNReal.ofReal_ne_top hreal
  have hbar : genDzbar (fun z => g z + h z) (fun z => I * (g z - h z)) = h := by
    funext z
    change ((g z + h z) + I * (I * (g z - h z))) / 2 = h z
    have hII : I * I = -1 := by simpa only [pow_two] using I_sq
    rw [← mul_assoc, hII]
    ring
  have hformula := eq11_11_pompeiu_gen hR hU hsub hp hgen hz₀
  rw [hbar] at hformula
  exact hformula

/-- Whole-plane Pompeiu formula with the original global Lp weak-derivative
hypotheses and no extra ACL, smoothness or approximation assumption. -/
theorem pompeiu_of_global_distributional_wirtinger
    {f g h : ℂ → ℂ} (hf : Continuous f)
    (hw : HasDistributionalWirtingerDerivatives f g h univ)
    {p : ℝ} (hp : 2 < p) (hg : MemLp g (ENNReal.ofReal p) (volume : Measure ℂ))
    (hh : MemLp h (ENNReal.ofReal p) (volume : Measure ℂ)) {c z₀ : ℂ} {R : ℝ} (hR : 0 < R)
    (hz₀ : z₀ ∈ ball c R) :
    f z₀ = (1 / (2 * π * I)) * (∮ z in C(c, R), f z / (z - z₀)) -
      (1 / π : ℂ) * ∫ z in ball c R, h z / (z - z₀) :=
  pompeiu_of_distributional_wirtinger isOpen_univ hf.continuousOn hw hp
    (fun C _ _ => ⟨hg.restrict C, hh.restrict C⟩) hR (subset_univ _) hz₀

end LowDimensionalTopology.Geometry.Quasiconformal
