/-
The actual Hilbert-transform contraction and smooth-approximation extension
are due to Wu Xiaobin, Li-Zhong-QC-formalization, fixed commit
1c0d5473c020b66ed5106331a38a61536760b9b2. Attribution and Apache-2.0 licensing
are retained in the external source and THIRD_PARTY_NOTICES.md.
-/
module

public import LowDimensionalTopology.Geometry.Quasiconformal.WeakWirtingerCalculus
public import LowDimensionalTopology.Geometry.Quasiconformal.WeakPrimitiveRigidity
public import LowDimensionalTopology.Geometry.Quasiconformal.SmoothHilbertNorm
public import LowDimensionalTopology.Geometry.Teichmuller.MeasurableBeltrami
public import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

/-!
# Normal solutions for actual compactly supported measurable coefficient classes

The exponent is the originally specified exponent, and the smallness condition
uses the literal smooth-unit-input Hilbert operator norm. The coefficient is an
actual L-infinity class with compact essential support; no chosen representative
is required to vanish pointwise outside a compact set.

The actual Lp fixed point gives existence through the normalized Cauchy
potential. Conversely, every continuous distributional candidate has the same
potential representation by weak affine rigidity. The same Lp fixed-point
uniqueness then proves equality of the actual functions.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Complex Set MeasureTheory Filter Topology
open scoped ENNReal
open LiZhongQC

namespace LowDimensionalTopology.Geometry.Quasiconformal

open LowDimensionalTopology.Geometry.Teichmuller

/-- The function vanishes almost everywhere outside some actual compact set.
This property is independent of the chosen measurable representative. -/
def HasCompactEssentialSupport (μ : ℂ → ℂ) : Prop :=
  ∃ K : Set ℂ, IsCompact K ∧ ∀ᵐ z ∂(volume : Measure ℂ), z ∉ K → μ z = 0

/-- A normal solution is continuous, vanishes at zero, and has genuine
distributional Wirtinger derivatives satisfying the equation, with its
holomorphic derivative at the specified finite Lp distance from one. -/
def IsNormalLpSolution (μ f : ℂ → ℂ) (p : ℝ) : Prop :=
  Continuous f ∧ f 0 = 0 ∧
    ∃ g h : ℂ → ℂ, HasDistributionalWirtingerDerivatives f g h univ ∧
      MemLp (fun z => g z - 1) (ENNReal.ofReal p) (volume : Measure ℂ) ∧
        h =ᵐ[volume] fun z => μ z * g z

/-- Compact essential support depends on the a.e. class, not its representative. -/
theorem hasCompactEssentialSupport_congr_ae {μ ν : ℂ → ℂ}
    (hμν : μ =ᵐ[volume] ν) : HasCompactEssentialSupport μ ↔ HasCompactEssentialSupport ν := by
  constructor
  · rintro ⟨K, hK, hμ⟩
    refine ⟨K, hK, ?_⟩
    filter_upwards [hμν, hμ] with z hz hzero
    intro hzK
    exact hz.symm.trans (hzero hzK)
  · rintro ⟨K, hK, hν⟩
    refine ⟨K, hK, ?_⟩
    filter_upwards [hμν, hν] with z hz hzero
    intro hzK
    exact hz.trans (hzero hzK)

/-- The actual distributional equation also depends only on the coefficient
a.e. class, without changing its solution or weak derivative witnesses. -/
theorem isNormalLpSolution_congr_coefficient_ae {μ ν f : ℂ → ℂ} {p : ℝ}
    (hμν : μ =ᵐ[volume] ν) : IsNormalLpSolution μ f p ↔ IsNormalLpSolution ν f p := by
  constructor
  · rintro ⟨hfc, hf0, g, h, hw, hmem, heq⟩
    refine ⟨hfc, hf0, g, h, hw, hmem, ?_⟩
    filter_upwards [heq, hμν] with z hz hμνz
    simpa only [hμνz] using hz
  · rintro ⟨hfc, hf0, g, h, hw, hmem, heq⟩
    refine ⟨hfc, hf0, g, h, hw, hmem, ?_⟩
    filter_upwards [heq, hμν] with z hz hμνz
    simpa only [hμνz] using hz

/-- An actual L-infinity class with compact essential support lies in every
Lp space, regardless of its chosen representative on null sets. -/
theorem measurableBeltrami_memLp_of_compactEssentialSupport
    (μ : MeasurableBeltramiSpace) (hμ : HasCompactEssentialSupport (μ : ℂ → ℂ))
    (p : ℝ≥0∞) : MemLp (μ : ℂ → ℂ) p (volume : Measure ℂ) := by
  obtain ⟨K, hK, hzero⟩ := hμ
  have : IsFiniteMeasure ((volume : Measure ℂ).restrict K) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hK.measure_lt_top⟩
  have hrestricted : MemLp (μ : ℂ → ℂ) p (volume.restrict K) :=
    ((Lp.memLp μ).restrict K).mono_exponent le_top
  have hindicator : MemLp (K.indicator (μ : ℂ → ℂ)) p volume :=
    (memLp_indicator_iff_restrict hK.measurableSet.nullMeasurableSet).mpr hrestricted
  apply MemLp.ae_eq (f := K.indicator (μ : ℂ → ℂ))
    (g := (μ : ℂ → ℂ)) ?_ hindicator
  filter_upwards [hzero] with z hz
  by_cases hzK : z ∈ K
  · exact indicator_of_mem hzK _
  · rw [indicator_of_notMem hzK, hz hzK]

/-- A.e. equal input data give exactly the same actual normalized potential. -/
theorem normalizedCauchyPotential_congr_ae {h g : ℂ → ℂ} (heq : h =ᵐ[volume] g) :
    normalizedCauchyPotential h = normalizedCauchyPotential g := by
  funext z
  unfold normalizedCauchyPotential
  congr 1
  apply integral_congr_ae
  filter_upwards [heq] with ζ hζ
  rw [hζ]

private theorem identity_distributional_wirtinger :
    HasDistributionalWirtingerDerivatives (fun z : ℂ => z)
      (fun _ => 1) (fun _ => 0) univ := by
  have h := c1_hasDistributionalWirtingerDerivatives_univ
    (f := fun z : ℂ => z) contDiff_id
  apply h.congr_derivatives_univ
  · filter_upwards with z
    rw [dz_eq_deriv (hasDerivAt_id' z).differentiableAt]
    exact (hasDerivAt_id' z).deriv
  · exact Eventually.of_forall fun z =>
      (cauchyRiemann_iff.mp (differentiable_id z)).2

/-- The actual potential of any Lp fixed point supplies every property of a
normal distributional solution at that same exponent. -/
theorem normalLpSolution_of_fixedPoint {μ ω : ℂ → ℂ} {p : ℝ} (hp : 2 < p)
    (hω : MemLp ω (ENNReal.ofReal p) (volume : Measure ℂ))
    (heq : ω =ᵐ[volume] fun z => μ z * hilbertH ω z + μ z) :
    IsNormalLpSolution μ (fun z => z + normalizedCauchyPotential ω z) p := by
  have hp1 : 1 < p := lt_trans one_lt_two hp
  have hHω := hilbertH_memLp hp1 hω
  have hpot := normalizedCauchyPotential_distributional hp hω
  have hsum := identity_distributional_wirtinger.add_univ hpot
  have hweak : HasDistributionalWirtingerDerivatives
      (fun z => z + normalizedCauchyPotential ω z)
      (fun z => 1 + hilbertH ω z) ω univ := by
    apply hsum.congr_derivatives_univ
    · exact EventuallyEq.rfl
    · exact Eventually.of_forall fun z => zero_add (ω z)
  have hmem : MemLp (fun z => (1 + hilbertH ω z) - 1)
      (ENNReal.ofReal p) (volume : Measure ℂ) := by
    apply MemLp.ae_eq (f := hilbertH ω)
      (g := fun z => (1 + hilbertH ω z) - 1) ?_ hHω
    exact Eventually.of_forall fun z => by ring
  refine ⟨continuous_id.add (normalizedCauchyPotential_continuous_of_memLp hp hω),
    ?_, (fun z => 1 + hilbertH ω z), ω, hweak, hmem, ?_⟩
  · simp only [normalizedCauchyPotential_zero, add_zero]
  · filter_upwards [heq] with z hz
    rw [hz]
    ring

private theorem normal_antiholomorphic_derivative_memLp
    {μ g h : ℂ → ℂ} {k p : ℝ}
    (hμ : IsBeltramiCoeff μ univ k)
    (hμLp : MemLp μ (ENNReal.ofReal p) (volume : Measure ℂ))
    (hgm : MemLp (fun z => g z - 1) (ENNReal.ofReal p) (volume : Measure ℂ))
    (heq : h =ᵐ[volume] fun z => μ z * g z) :
    MemLp h (ENNReal.ofReal p) (volume : Measure ℂ) := by
  have hμTop : MemLp μ ⊤ volume :=
    memLp_top_of_bound (by simpa only [Measure.restrict_univ] using hμ.1) k
      (by simpa only [Measure.restrict_univ] using hμ.2)
  have hprod : MemLp (fun z => μ z * (g z - 1))
      (ENNReal.ofReal p) (volume : Measure ℂ) := hμTop.fun_mul hgm
  have hsum := hprod.add hμLp
  apply MemLp.ae_eq (f := (fun z => μ z * (g z - 1)) + μ) (g := h) ?_ hsum
  filter_upwards [heq] with z hz
  change μ z * (g z - 1) + μ z = h z
  rw [hz]
  ring

/-- Every normal candidate has the actual potential representation and yields
an actual Lp fixed point. No homeomorphism, growth, or representation is assumed. -/
theorem normalLpSolution_representation {μ f : ℂ → ℂ} {k p : ℝ} (hp : 2 < p)
    (hμ : IsBeltramiCoeff μ univ k)
    (hμLp : MemLp μ (ENNReal.ofReal p) (volume : Measure ℂ))
    (hf : IsNormalLpSolution μ f p) :
    ∃ h : ℂ → ℂ, MemLp h (ENNReal.ofReal p) (volume : Measure ℂ) ∧
      (h =ᵐ[volume] fun z => μ z * hilbertH h z + μ z) ∧
        f = fun z => z + normalizedCauchyPotential h z := by
  obtain ⟨hfc, hf0, g, h, hw, hgm, heq⟩ := hf
  have hp1 : 1 < p := lt_trans one_lt_two hp
  have hh := normal_antiholomorphic_derivative_memLp hμ hμLp hgm heq
  have hHh := hilbertH_memLp hp1 hh
  have hpot := normalizedCauchyPotential_distributional hp hh
  let F : ℂ → ℂ := fun z => f z - normalizedCauchyPotential h z
  let G : ℂ → ℂ := fun z => g z - hilbertH h z
  have hdiff : HasDistributionalWirtingerDerivatives F G (fun z => h z - h z) univ :=
    hw.sub_univ hpot
  have hFcont : Continuous F :=
    hfc.sub (normalizedCauchyPotential_continuous_of_memLp hp hh)
  have hbar : (fun z => h z - h z) =ᵐ[volume] (0 : ℂ → ℂ) :=
    Eventually.of_forall fun z => sub_self (h z)
  have hGm : MemLp (fun z => G z - 1) (ENNReal.ofReal p) volume := by
    apply MemLp.ae_eq (f := (fun z => g z - 1) - hilbertH h)
      (g := fun z => G z - 1) ?_ (hgm.sub hHh)
    exact Eventually.of_forall fun z => by
      change (g z - 1) - hilbertH h z = _
      dsimp only [G]
      ring
  have hAffine := weak_primitive_eq_add_value_zero hp1 hFcont hdiff hbar hGm
  have hF0 : F 0 = 0 := by
    simp only [F, hf0, normalizedCauchyPotential_zero, sub_self]
  have hFid : F = fun z => z := by
    funext z
    simpa only [hF0, add_zero] using hAffine z
  have hidentity : HasDistributionalWirtingerDerivatives F
      (fun _ => 1) (fun _ => 0) univ := by
    rw [hFid]
    exact identity_distributional_wirtinger
  have hGactual := (distributionalWirtinger_derivatives_unique_univ hdiff hidentity).1
  refine ⟨h, hh, ?_, ?_⟩
  · filter_upwards [heq, hGactual] with z hz hGz
    have hg : g z - hilbertH h z = 1 := by
      simpa only [G] using hGz
    rw [hz, sub_eq_iff_eq_add.mp hg]
    ring
  · funext z
    have hz : f z - normalizedCauchyPotential h z = z := congrFun hFid z
    exact sub_eq_iff_eq_add.mp hz

/-- The same prescribed exponent and literal operator norm give a unique
normal solution for every bounded coefficient which itself belongs to Lp. -/
theorem existsUnique_normalLpSolution_of_memLp {μ : ℂ → ℂ} {k p : ℝ}
    (hk : 0 ≤ k) (hp : 2 < p) (hμ : IsBeltramiCoeff μ univ k)
    (hμLp : MemLp μ (ENNReal.ofReal p) (volume : Measure ℂ))
    (hsmall : k * smoothHilbertNorm p < 1) :
    ∃! f : ℂ → ℂ, IsNormalLpSolution μ f p := by
  have hp1 : 1 < p := lt_trans one_lt_two hp
  have hkp : k * hilbertNorm p < 1 := by
    simpa only [smoothHilbertNorm_eq_hilbertNorm hp1] using hsmall
  obtain ⟨ω, hω, hsol, huniq⟩ := eq12_1_solution hk hμ hp hkp hμLp
  refine ⟨(fun z => z + normalizedCauchyPotential ω z),
    normalLpSolution_of_fixedPoint hp hω hsol, ?_⟩
  intro f hf
  obtain ⟨h, hh, hfixed, hrepr⟩ := normalLpSolution_representation hp hμ hμLp hf
  have hae : h =ᵐ[volume] ω := huniq h hh hfixed
  rw [hrepr, normalizedCauchyPotential_congr_ae hae]

/-- The original normal-solution theorem for actual essentially bounded
coefficient classes with compact essential support. The exponent p is the
originally specified one; its only smallness test uses the literal C_p. -/
theorem existsUnique_normalLpSolution_of_compactEssentialSupport
    (μ : MeasurableBeltramiSpace) {k p : ℝ} (hk : k ∈ Ico (0 : ℝ) 1)
    (hμk : ‖μ‖ ≤ k) (hcomp : HasCompactEssentialSupport (μ : ℂ → ℂ))
    (hp : 2 < p) (hsmall : k * smoothHilbertNorm p < 1) :
    ∃! f : ℂ → ℂ, IsNormalLpSolution (μ : ℂ → ℂ) f p := by
  have hμ : IsBeltramiCoeff (μ : ℂ → ℂ) univ k := by
    refine ⟨(MeasurableBeltramiSpace.isBeltramiCoeff μ).1, ?_⟩
    filter_upwards [(MeasurableBeltramiSpace.isBeltramiCoeff μ).2] with z hz
    exact hz.trans hμk
  exact existsUnique_normalLpSolution_of_memLp hk.1 hp hμ
    (measurableBeltrami_memLp_of_compactEssentialSupport μ hcomp (ENNReal.ofReal p)) hsmall

end LowDimensionalTopology.Geometry.Quasiconformal
