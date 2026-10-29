module

public import LowDimensionalTopology.Geometry.Teichmuller.GenusOnePeriodBeltrami
public import LowDimensionalTopology.Geometry.Teichmuller.BeltramiBanach
public import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# The actual period-marking curve in the fixed torus tensor space

All tensors use the original atlas of the fixed source torus. The finite
cover formula identifies the genuine tensor curve with a scalar multiple of
one actual marking tensor. Its derivative is taken in the existing uniform
Banach model of those tensors.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set Filter Topology
open scoped UpperHalfPlane ComplexConjugate

namespace LowDimensionalTopology.Geometry.Teichmuller.GenusOne
open Surfaces

/-- The actual original plane covering separates continuous torus tensors. -/
theorem torusCoverBeltramiValue_injective (τ : ℍ) :
    Function.Injective (torusCoverBeltramiValue τ) := by
  intro μ ν h
  apply BeltramiDifferential.ext
  intro e w
  let A := (normalizedTorusModel τ).surface.toRiemannAtlas
  let p := (normalizedTorusModel τ).projection
  obtain ⟨z, hz⟩ := (normalizedTorusModel τ).surjective (e.val.symm w.val)
  change p z = e.val.symm w.val at hz
  have he : p z ∈ e.val.source := by
    rw [hz]
    exact e.val.map_target w.property
  have hw : e.val (p z) = w.val := by
    rw [hz]
    exact e.val.right_inv w.property
  let c := A.cover (p z)
  let E : BeltramiDifferential.Chart A := ⟨c.choose, c.choose_spec.1⟩
  have hE : p z ∈ E.val.source := c.choose_spec.2
  let d := deriv (E.val ∘ p) z
  have hd : d ≠ 0 := normalizedTorusCoverChart_deriv_ne_zero τ E z hE
  have hdc : conj d ≠ 0 := by simpa using hd
  have hc :
      μ.coeff E ⟨E.val (p z), E.val.map_source hE⟩ =
        ν.coeff E ⟨E.val (p z), E.val.map_source hE⟩ := by
    have hh := congrFun h z
    change μ.coeff E ⟨E.val (p z), E.val.map_source hE⟩ * conj d / d =
      ν.coeff E ⟨E.val (p z), E.val.map_source hE⟩ * conj d / d at hh
    exact mul_right_cancel₀ hdc ((div_left_inj' hd).mp hh)
  have hcoeff :
      μ.coeff e ⟨e.val (p z), e.val.map_source he⟩ =
        ν.coeff e ⟨e.val (p z), e.val.map_source he⟩ := by
    rw [μ.compatible e E (p z) he hE, ν.compatible e E (p z) he hE, hc]
  simpa only [hw] using hcoeff

/-- Cover evaluation respects the original tensor's scalar action. -/
theorem torusCoverBeltramiValue_smul (τ : ℍ) (a : ℂ)
    (μ : BeltramiDifferential (normalizedTorusModel τ).surface.toRiemannAtlas)
    (z : ℂ) :
    torusCoverBeltramiValue τ (a • μ) z = a * torusCoverBeltramiValue τ μ z := by
  let A := (normalizedTorusModel τ).surface.toRiemannAtlas
  let p := (normalizedTorusModel τ).projection
  let c := A.cover (p z)
  let e : BeltramiDifferential.Chart A := ⟨c.choose, c.choose_spec.1⟩
  let w : e.val.target := ⟨e.val (p z), e.val.map_source c.choose_spec.2⟩
  let d := deriv (e.val ∘ p) z
  change (a * μ.coeff e w) * conj d / d = a * (μ.coeff e w * conj d / d)
  ring

/-- The genuine nearby target period, extended away from its open domain. -/
def nearbyPeriod (τ : ℍ) (t : ℂ) : ℍ :=
  if h : 0 < ((τ : ℂ) + t).im then ⟨(τ : ℂ) + t, h⟩ else τ

private theorem nearbyPeriod_coe (τ : ℍ) (t : ℂ)
    (h : 0 < ((τ : ℂ) + t).im) : (nearbyPeriod τ t : ℂ) = (τ : ℂ) + t := by
  simp only [nearbyPeriod, dite_eq_left h]

/-- The actual finite markings, all in the fixed original source tensor space. -/
def periodBeltramiCurve (τ : ℍ) (t : ℂ) :
    BeltramiDifferential.BanachSpace
      (normalizedTorusModel τ).surface.toRiemannAtlas :=
  BeltramiDifferential.ofTensor
    ((periodMarking τ (nearbyPeriod τ t)).beltrami
      (periodMarking_spec τ (nearbyPeriod τ t)).1)

/-- An actual tensor obtained by scaling the period marking to the target tau+1.
The numerator uses the fixed source period gap plus one. -/
def periodTangentBeltrami (τ : ℍ) :
    BeltramiDifferential.BanachSpace
      (normalizedTorusModel τ).surface.toRiemannAtlas :=
  (((periodGap τ) + (1 : ℂ)) / periodGap τ) •
    BeltramiDifferential.ofTensor
      ((periodMarking τ ((1 : ℝ) +ᵥ τ)).beltrami
        (periodMarking_spec τ ((1 : ℝ) +ᵥ τ)).1)

/-- The genuine infinitesimal tensor has the source coefficient on every
point of the actual original covering plane. -/
theorem torusCoverBeltramiValue_periodTangentBeltrami (τ : ℍ) (z : ℂ) :
    torusCoverBeltramiValue τ
      (BeltramiDifferential.toTensor (periodTangentBeltrami τ)) z =
        tangentBeltrami τ := by
  have hT : BeltramiDifferential.toTensor (periodTangentBeltrami τ) =
      (((periodGap τ) + (1 : ℂ)) / periodGap τ) •
        ((periodMarking τ ((1 : ℝ) +ᵥ τ)).beltrami
          (periodMarking_spec τ ((1 : ℝ) +ᵥ τ)).1) := by
    apply BeltramiDifferential.ext
    intro e w
    rfl
  have hinc : (((1 : ℝ) +ᵥ τ : ℍ) : ℂ) - (τ : ℂ) = 1 := by
    simp only [UpperHalfPlane.coe_vadd, Complex.ofReal_one, add_sub_cancel_right]
  have hd1 : periodGap τ + (1 : ℂ) ≠ 0 := by
    intro h
    have hr := congrArg Complex.re h
    simp [periodGap] at hr
  rw [hT, torusCoverBeltramiValue_smul, torusCoverBeltramiValue_periodMarking,
    hinc, affineBeltrami_eq]
  calc
    ((periodGap τ + 1) / periodGap τ) * (-1 / (periodGap τ + 1)) =
        (-1 / periodGap τ) * ((periodGap τ + 1) / (periodGap τ + 1)) := by ring
    _ = tangentBeltrami τ := by simp only [div_self hd1, mul_one, tangentBeltrami]

private theorem tangentBeltrami_ne_zero (τ : ℍ) : tangentBeltrami τ ≠ 0 :=
  div_ne_zero (neg_ne_zero.mpr one_ne_zero) (periodGap_ne_zero τ)

private theorem periodBeltramiCurve_eq_smul (τ : ℍ) (t : ℂ)
    (ht : 0 < ((τ : ℂ) + t).im) :
    periodBeltramiCurve τ t =
      (affineBeltrami τ t / tangentBeltrami τ) • periodTangentBeltrami τ := by
  apply BeltramiDifferential.toTensor_injective
  apply torusCoverBeltramiValue_injective τ
  funext z
  have hT : BeltramiDifferential.toTensor
      ((affineBeltrami τ t / tangentBeltrami τ) • periodTangentBeltrami τ) =
        (affineBeltrami τ t / tangentBeltrami τ) •
          BeltramiDifferential.toTensor (periodTangentBeltrami τ) := by
    apply BeltramiDifferential.ext
    intro e w
    rfl
  have hinc : (nearbyPeriod τ t : ℂ) - (τ : ℂ) = t := by
    rw [nearbyPeriod_coe τ t ht]
    exact add_sub_cancel_left _ _
  rw [hT, torusCoverBeltramiValue_smul,
    torusCoverBeltramiValue_periodTangentBeltrami]
  rw [periodBeltramiCurve, BeltramiDifferential.toTensor_ofTensor,
    torusCoverBeltramiValue_periodMarking, hinc,
    div_mul_cancel₀ _ (tangentBeltrami_ne_zero τ)]

/-- The original period-marking family has this derivative in the actual
uniform Banach space of source-atlas Beltrami tensors. -/
theorem hasDerivAt_periodBeltramiCurve_zero (τ : ℍ) :
    HasDerivAt (periodBeltramiCurve τ) (periodTangentBeltrami τ) 0 := by
  have hcont : ContinuousAt (fun t : ℂ => ((τ : ℂ) + t).im) 0 :=
    (Complex.continuous_im.comp (continuous_const.add continuous_id)).continuousAt
  have hpos : ∀ᶠ t : ℂ in 𝓝 0, 0 < ((τ : ℂ) + t).im :=
    (continuousAt_const : ContinuousAt (fun _ : ℂ => (0 : ℝ)) 0).eventually_lt hcont
      (by simpa only [add_zero, UpperHalfPlane.coe_im] using τ.im_pos)
  have hscalar : HasDerivAt
      (fun t : ℂ => affineBeltrami τ t / tangentBeltrami τ) 1 0 := by
    simpa only [div_self (tangentBeltrami_ne_zero τ)] using
      (hasDerivAt_affineBeltrami_zero τ).div_const (tangentBeltrami τ)
  have h : HasDerivAt
      (fun t : ℂ => (affineBeltrami τ t / tangentBeltrami τ) • periodTangentBeltrami τ)
      (periodTangentBeltrami τ) 0 := by
    simpa only [one_smul] using hscalar.smul_const (periodTangentBeltrami τ)
  apply h.congr_of_eventuallyEq
  filter_upwards [hpos] with t ht
  exact periodBeltramiCurve_eq_smul τ t ht

end LowDimensionalTopology.Geometry.Teichmuller.GenusOne
