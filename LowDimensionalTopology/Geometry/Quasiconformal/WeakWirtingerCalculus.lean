module

public import LowDimensionalTopology.Geometry.Quasiconformal.NormalizedCauchyDistributional
public import LowDimensionalTopology.External.LiZhongQC.Lemmas.GreenDisc
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-!
# Algebra and uniqueness of genuine weak Wirtinger derivatives

All statements use actual locally integrable functions and smooth compact
tests on the plane. Addition, subtraction and almost-everywhere replacement
preserve both distributional identities. Classical C1 functions satisfy the
same identities, and weak derivative witnesses are unique almost everywhere.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Complex Set MeasureTheory Filter Topology
open scoped ContDiff
open LiZhongQC

namespace LowDimensionalTopology.Geometry.Quasiconformal

private theorem test_mul_integrable {f ψ : ℂ → ℂ}
    (hf : LocallyIntegrableOn f univ) (hψ : Continuous ψ) (hcψ : HasCompactSupport ψ) :
    Integrable (fun z => ψ z * f z) (volume : Measure ℂ) := by
  simpa only [smul_eq_mul] using
    (locallyIntegrableOn_univ.mp hf).integrable_smul_left_of_hasCompactSupport hψ hcψ

private theorem mul_test_integrable {f ψ : ℂ → ℂ}
    (hf : LocallyIntegrableOn f univ) (hψ : Continuous ψ) (hcψ : HasCompactSupport ψ) :
    Integrable (fun z => f z * ψ z) (volume : Measure ℂ) := by
  simpa only [mul_comm] using test_mul_integrable hf hψ hcψ

private theorem test_derivatives_regular {ψ : ℂ → ℂ}
    (hψ : ContDiff ℝ 1 ψ) (hcψ : HasCompactSupport ψ) :
    Continuous (dz ψ) ∧ Continuous (dzbar ψ) ∧
      HasCompactSupport (dz ψ) ∧ HasCompactSupport (dzbar ψ) := by
  refine ⟨continuous_dz hψ, continuous_dzbar hψ, ?_, ?_⟩
  · refine HasCompactSupport.intro hcψ.isCompact ?_
    intro z hz
    simp only [dz, sp_fderiv_eq_zero_of_notMem_tsupport hz 1,
      sp_fderiv_eq_zero_of_notMem_tsupport hz I, mul_zero, sub_zero, zero_div]
  · refine HasCompactSupport.intro hcψ.isCompact ?_
    intro z hz
    simp only [dzbar, sp_fderiv_eq_zero_of_notMem_tsupport hz 1,
      sp_fderiv_eq_zero_of_notMem_tsupport hz I, mul_zero, add_zero, zero_div]

private theorem weak_pairing_add {f₁ f₂ g₁ g₂ φ ψ : ℂ → ℂ}
    (hf₁ : Integrable (fun z => f₁ z * φ z))
    (hf₂ : Integrable (fun z => f₂ z * φ z))
    (hg₁ : Integrable (fun z => ψ z * g₁ z))
    (hg₂ : Integrable (fun z => ψ z * g₂ z))
    (h₁ : (∫ z, f₁ z * φ z) = -∫ z, ψ z * g₁ z)
    (h₂ : (∫ z, f₂ z * φ z) = -∫ z, ψ z * g₂ z) :
    (∫ z, (f₁ z + f₂ z) * φ z) = -∫ z, ψ z * (g₁ z + g₂ z) := by
  simp_rw [add_mul, mul_add]
  rw [integral_add hf₁ hf₂, integral_add hg₁ hg₂, h₁, h₂, neg_add]

private theorem weak_pairing_sub {f₁ f₂ g₁ g₂ φ ψ : ℂ → ℂ}
    (hf₁ : Integrable (fun z => f₁ z * φ z))
    (hf₂ : Integrable (fun z => f₂ z * φ z))
    (hg₁ : Integrable (fun z => ψ z * g₁ z))
    (hg₂ : Integrable (fun z => ψ z * g₂ z))
    (h₁ : (∫ z, f₁ z * φ z) = -∫ z, ψ z * g₁ z)
    (h₂ : (∫ z, f₂ z * φ z) = -∫ z, ψ z * g₂ z) :
    (∫ z, (f₁ z - f₂ z) * φ z) = -∫ z, ψ z * (g₁ z - g₂ z) := by
  simp_rw [sub_mul, mul_sub]
  rw [integral_sub hf₁ hf₂, integral_sub hg₁ hg₂, h₁, h₂]
  ring

/-- Both weak Wirtinger derivatives commute with actual pointwise addition. -/
theorem HasDistributionalWirtingerDerivatives.add_univ
    {f₁ g₁ h₁ f₂ g₂ h₂ : ℂ → ℂ}
    (hw₁ : HasDistributionalWirtingerDerivatives f₁ g₁ h₁ univ)
    (hw₂ : HasDistributionalWirtingerDerivatives f₂ g₂ h₂ univ) :
    HasDistributionalWirtingerDerivatives (fun z => f₁ z + f₂ z)
      (fun z => g₁ z + g₂ z) (fun z => h₁ z + h₂ z) univ := by
  refine ⟨LocallyIntegrableOn.congr
      (Eventually.of_forall fun z => Pi.add_apply f₁ f₂ z) (hw₁.1.add hw₂.1),
    LocallyIntegrableOn.congr
      (Eventually.of_forall fun z => Pi.add_apply g₁ g₂ z) (hw₁.2.1.add hw₂.2.1),
    LocallyIntegrableOn.congr
      (Eventually.of_forall fun z => Pi.add_apply h₁ h₂ z) (hw₁.2.2.1.add hw₂.2.2.1), ?_⟩
  intro ψ hψ hcψ hsψ
  have hψ1 : ContDiff ℝ 1 ψ := hψ.of_le (by simp)
  obtain ⟨hdz, hdbar, hcdz, hcdbar⟩ := test_derivatives_regular hψ1 hcψ
  have ht₁ := hw₁.2.2.2 ψ hψ hcψ hsψ
  have ht₂ := hw₂.2.2.2 ψ hψ hcψ hsψ
  simp only [Measure.restrict_univ] at ht₁ ht₂ ⊢
  exact ⟨weak_pairing_add
    (mul_test_integrable hw₁.1 hdz hcdz) (mul_test_integrable hw₂.1 hdz hcdz)
    (test_mul_integrable hw₁.2.1 hψ.continuous hcψ)
    (test_mul_integrable hw₂.2.1 hψ.continuous hcψ) ht₁.1 ht₂.1,
    weak_pairing_add
      (mul_test_integrable hw₁.1 hdbar hcdbar) (mul_test_integrable hw₂.1 hdbar hcdbar)
      (test_mul_integrable hw₁.2.2.1 hψ.continuous hcψ)
      (test_mul_integrable hw₂.2.2.1 hψ.continuous hcψ) ht₁.2 ht₂.2⟩

/-- Both weak Wirtinger derivatives commute with actual pointwise subtraction. -/
theorem HasDistributionalWirtingerDerivatives.sub_univ
    {f₁ g₁ h₁ f₂ g₂ h₂ : ℂ → ℂ}
    (hw₁ : HasDistributionalWirtingerDerivatives f₁ g₁ h₁ univ)
    (hw₂ : HasDistributionalWirtingerDerivatives f₂ g₂ h₂ univ) :
    HasDistributionalWirtingerDerivatives (fun z => f₁ z - f₂ z)
      (fun z => g₁ z - g₂ z) (fun z => h₁ z - h₂ z) univ := by
  refine ⟨LocallyIntegrableOn.congr
      (Eventually.of_forall fun z => Pi.sub_apply f₁ f₂ z) (hw₁.1.sub hw₂.1),
    LocallyIntegrableOn.congr
      (Eventually.of_forall fun z => Pi.sub_apply g₁ g₂ z) (hw₁.2.1.sub hw₂.2.1),
    LocallyIntegrableOn.congr
      (Eventually.of_forall fun z => Pi.sub_apply h₁ h₂ z) (hw₁.2.2.1.sub hw₂.2.2.1), ?_⟩
  intro ψ hψ hcψ hsψ
  have hψ1 : ContDiff ℝ 1 ψ := hψ.of_le (by simp)
  obtain ⟨hdz, hdbar, hcdz, hcdbar⟩ := test_derivatives_regular hψ1 hcψ
  have ht₁ := hw₁.2.2.2 ψ hψ hcψ hsψ
  have ht₂ := hw₂.2.2.2 ψ hψ hcψ hsψ
  simp only [Measure.restrict_univ] at ht₁ ht₂ ⊢
  exact ⟨weak_pairing_sub
    (mul_test_integrable hw₁.1 hdz hcdz) (mul_test_integrable hw₂.1 hdz hcdz)
    (test_mul_integrable hw₁.2.1 hψ.continuous hcψ)
    (test_mul_integrable hw₂.2.1 hψ.continuous hcψ) ht₁.1 ht₂.1,
    weak_pairing_sub
      (mul_test_integrable hw₁.1 hdbar hcdbar) (mul_test_integrable hw₂.1 hdbar hcdbar)
      (test_mul_integrable hw₁.2.2.1 hψ.continuous hcψ)
      (test_mul_integrable hw₂.2.2.1 hψ.continuous hcψ) ht₁.2 ht₂.2⟩

/-- Replacing either actual weak derivative almost everywhere preserves both
distributional identities of the unchanged original function. -/
theorem HasDistributionalWirtingerDerivatives.congr_derivatives_univ
    {f g h g' h' : ℂ → ℂ} (hw : HasDistributionalWirtingerDerivatives f g h univ)
    (hg : g =ᵐ[volume] g') (hh : h =ᵐ[volume] h') :
    HasDistributionalWirtingerDerivatives f g' h' univ := by
  refine ⟨hw.1,
    LocallyIntegrableOn.congr (by simpa only [Measure.restrict_univ] using hg) hw.2.1,
    LocallyIntegrableOn.congr (by simpa only [Measure.restrict_univ] using hh) hw.2.2.1, ?_⟩
  intro ψ hψ hcψ hsψ
  have ht := hw.2.2.2 ψ hψ hcψ hsψ
  have hgi : (∫ z, ψ z * g z) = ∫ z, ψ z * g' z :=
    integral_congr_ae (hg.mono fun z hz => congrArg (fun a : ℂ => ψ z * a) hz)
  have hhi : (∫ z, ψ z * h z) = ∫ z, ψ z * h' z :=
    integral_congr_ae (hh.mono fun z hz => congrArg (fun a : ℂ => ψ z * a) hz)
  simpa only [Measure.restrict_univ, hgi, hhi] using ht

/-- The actual ordinary Wirtinger derivatives of every C1 function satisfy
the same genuine distributional identities against all smooth compact tests. -/
theorem c1_hasDistributionalWirtingerDerivatives_univ {f : ℂ → ℂ}
    (hf : ContDiff ℝ 1 f) :
    HasDistributionalWirtingerDerivatives f (dz f) (dzbar f) univ := by
  refine ⟨hf.continuous.locallyIntegrable.locallyIntegrableOn univ,
    (continuous_dz hf).locallyIntegrable.locallyIntegrableOn univ,
    (continuous_dzbar hf).locallyIntegrable.locallyIntegrableOn univ, ?_⟩
  intro ψ hψ hcψ _
  have hψ1 : ContDiff ℝ 1 ψ := hψ.of_le (by simp)
  simpa only [Measure.restrict_univ] using c1_wirtinger_integral_by_parts hf hψ1 hcψ

private theorem weak_data_unique {g₁ g₂ : ℂ → ℂ}
    (hg₁ : LocallyIntegrableOn g₁ univ) (hg₂ : LocallyIntegrableOn g₂ univ)
    (heq : ∀ ψ : ℂ → ℂ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      (∫ z, ψ z * g₁ z) = ∫ z, ψ z * g₂ z) : g₁ =ᵐ[volume] g₂ := by
  apply ae_eq_of_integral_contDiff_smul_eq
    (locallyIntegrableOn_univ.mp hg₁) (locallyIntegrableOn_univ.mp hg₂)
  intro ψ hψ hcψ
  let ψc : ℂ → ℂ := fun z => (ψ z : ℂ)
  have hψc : ContDiff ℝ ∞ ψc := Complex.ofRealCLM.contDiff.comp hψ
  have hcψc : HasCompactSupport ψc :=
    hcψ.comp_left (g := fun x : ℝ => (x : ℂ)) rfl
  simpa only [ψc, Complex.real_smul] using heq ψc hψc hcψc

/-- Both genuine weak derivative witnesses of the same actual function are
unique almost everywhere. No differentiability of that function is assumed. -/
theorem distributionalWirtinger_derivatives_unique_univ {f g₁ h₁ g₂ h₂ : ℂ → ℂ}
    (hw₁ : HasDistributionalWirtingerDerivatives f g₁ h₁ univ)
    (hw₂ : HasDistributionalWirtingerDerivatives f g₂ h₂ univ) :
    g₁ =ᵐ[volume] g₂ ∧ h₁ =ᵐ[volume] h₂ := by
  constructor
  · apply weak_data_unique hw₁.2.1 hw₂.2.1
    intro ψ hψ hcψ
    have ht₁ := (hw₁.2.2.2 ψ hψ hcψ (subset_univ _)).1
    have ht₂ := (hw₂.2.2.2 ψ hψ hcψ (subset_univ _)).1
    simp only [Measure.restrict_univ] at ht₁ ht₂
    exact neg_injective (ht₁.symm.trans ht₂)
  · apply weak_data_unique hw₁.2.2.1 hw₂.2.2.1
    intro ψ hψ hcψ
    have ht₁ := (hw₁.2.2.2 ψ hψ hcψ (subset_univ _)).2
    have ht₂ := (hw₂.2.2.2 ψ hψ hcψ (subset_univ _)).2
    simp only [Measure.restrict_univ] at ht₁ ht₂
    exact neg_injective (ht₁.symm.trans ht₂)

end LowDimensionalTopology.Geometry.Quasiconformal
