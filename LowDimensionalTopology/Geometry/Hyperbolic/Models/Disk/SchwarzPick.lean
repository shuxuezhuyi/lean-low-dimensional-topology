module

public import LowDimensionalTopology.External.LiZhongQC.Lemmas.DiscAutomorphism
public import Mathlib.Analysis.Complex.Schwarz
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Schwarz--Pick and one-point infinitesimal rigidity

The disk and the density 2/(1-|z|^2) are literal. Normalization uses the actual
Blaschke maps and their inverses; equality produces a genuine conformal bijection.
The Blaschke identities reused here are due to Wu Xiaobin, fixed source commit
1c0d5473c020b66ed5106331a38a61536760b9b2, Apache-2.0.
-/

@[expose] public section
noncomputable section

open Set Metric Complex
open scoped ComplexConjugate

namespace LowDimensionalTopology.Geometry.Hyperbolic

open LiZhongQC

private theorem disc_defect_pos {a : ℂ} (ha : ‖a‖ < 1) : 0 < 1 - ‖a‖ ^ 2 := by
  nlinarith [norm_nonneg a]

private theorem norm_one_sub_mul_conj {a : ℂ} (ha : ‖a‖ < 1) :
    ‖1 - a * conj a‖ = 1 - ‖a‖ ^ 2 := by
  have h : (1 - a * conj a : ℂ) = ((1 - ‖a‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.mul_conj']
    push_cast
    rfl
  rw [h, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (disc_defect_pos ha)]

private theorem blaschke_center_derivative {a : ℂ} (ha : ‖a‖ < 1) :
    HasDerivAt (blaschke a) (1 / (1 - a * conj a)) a := by
  convert hasDerivAt_blaschke ha ha using 1
  rw [mul_comm (conj a) a]
  field_simp [one_sub_mul_conj_ne_zero ha]

private theorem blaschke_inverse_zero_derivative {a : ℂ} (ha : ‖a‖ < 1) :
    HasDerivAt (blaschke (-a)) (1 - a * conj a) 0 := by
  simpa only [map_neg, neg_mul_neg, mul_zero, sub_zero, one_pow, div_one] using
    (hasDerivAt_blaschke (a := -a) (z := 0) (by simpa using ha) (by simp))

/-- Move the source point and its image to zero by actual disk automorphisms. -/
def discNormalizedMap (f : ℂ → ℂ) (z : ℂ) : ℂ → ℂ :=
  blaschke (f z) ∘ f ∘ blaschke (-z)

private theorem discNormalizedMap_mapsTo {f : ℂ → ℂ}
    (hf : MapsTo f unitDisc unitDisc) {z : ℂ} (hz : z ∈ unitDisc) :
    MapsTo (discNormalizedMap f z) unitDisc unitDisc := by
  have hz' : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
  have hfz : ‖f z‖ < 1 := mem_ball_zero_iff.mp (hf hz)
  intro w hw
  exact mem_ball_zero_iff.mpr (blaschke_mem_unitDisc hfz
    (mem_ball_zero_iff.mp (hf (mem_ball_zero_iff.mpr
      (blaschke_mem_unitDisc (by simpa using hz') (mem_ball_zero_iff.mp hw))))))

private theorem discNormalizedMap_differentiable {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f unitDisc) (hm : MapsTo f unitDisc unitDisc)
    {z : ℂ} (hz : z ∈ unitDisc) :
    DifferentiableOn ℂ (discNormalizedMap f z) unitDisc := by
  have hz' : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
  have hfz : ‖f z‖ < 1 := mem_ball_zero_iff.mp (hm hz)
  have hi : MapsTo (blaschke (-z)) unitDisc unitDisc := fun w hw =>
    mem_ball_zero_iff.mpr (blaschke_mem_unitDisc (by simpa using hz')
      (mem_ball_zero_iff.mp hw))
  exact (differentiableOn_blaschke hfz).comp
    (hf.comp (differentiableOn_blaschke (by simpa using hz')) hi) (hm.comp hi)

private theorem discNormalizedMap_zero (f : ℂ → ℂ) (z : ℂ) :
    discNormalizedMap f z 0 = 0 := by
  simp [discNormalizedMap, blaschke]

private theorem discNormalizedMap_norm_derivative {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f unitDisc) (hm : MapsTo f unitDisc unitDisc)
    {z : ℂ} (hz : z ∈ unitDisc) :
    ‖deriv (discNormalizedMap f z) 0‖ =
      ‖deriv f z‖ * (1 - ‖z‖ ^ 2) / (1 - ‖f z‖ ^ 2) := by
  have hz' : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
  have hfz : ‖f z‖ < 1 := mem_ball_zero_iff.mp (hm hz)
  have hi := blaschke_inverse_zero_derivative hz'
  have hf' : HasDerivAt f (deriv f z) (blaschke (-z) 0) := by
    simpa [blaschke] using (hf.differentiableAt (isOpen_ball.mem_nhds hz)).hasDerivAt
  have ho : HasDerivAt (blaschke (f z)) (1 / (1 - f z * conj (f z)))
      (f (blaschke (-z) 0)) := by
    simpa [blaschke] using blaschke_center_derivative hfz
  have hd := ho.comp 0 (hf'.comp 0 hi)
  change HasDerivAt (discNormalizedMap f z)
    (1 / (1 - f z * conj (f z)) * (deriv f z * (1 - z * conj z))) 0 at hd
  rw [hd.deriv, norm_mul, norm_mul, norm_div, norm_one,
    norm_one_sub_mul_conj hfz, norm_one_sub_mul_conj hz']
  ring

/-- The full infinitesimal Schwarz--Pick inequality at every point of the disk. -/
theorem disc_schwarz_pick_cross {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f unitDisc) (hm : MapsTo f unitDisc unitDisc)
    {z : ℂ} (hz : z ∈ unitDisc) :
    ‖deriv f z‖ * (1 - ‖z‖ ^ 2) ≤ 1 - ‖f z‖ ^ 2 := by
  have hN := discNormalizedMap_differentiable hf hm hz
  have hmap : MapsTo (discNormalizedMap f z) (ball 0 1)
      (closedBall (discNormalizedMap f z 0) 1) := by
    rw [discNormalizedMap_zero]
    exact fun w hw => ball_subset_closedBall (discNormalizedMap_mapsTo hm hz hw)
  have hb := Complex.norm_deriv_le_one_of_mapsTo_ball hN hmap one_pos
  rw [discNormalizedMap_norm_derivative hf hm hz] at hb
  exact (div_le_one (disc_defect_pos (mem_ball_zero_iff.mp (hm hz)))).mp hb

/-- The Poincare density contracts under every holomorphic disk self-map. -/
theorem disc_schwarz_pick_density {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f unitDisc) (hm : MapsTo f unitDisc unitDisc)
    {z : ℂ} (hz : z ∈ unitDisc) :
    2 / (1 - ‖f z‖ ^ 2) * ‖deriv f z‖ ≤ 2 / (1 - ‖z‖ ^ 2) := by
  rw [div_mul_eq_mul_div]
  apply (div_le_div_iff₀ (disc_defect_pos (mem_ball_zero_iff.mp (hm hz)))
    (disc_defect_pos (mem_ball_zero_iff.mp hz))).2
  nlinarith [disc_schwarz_pick_cross hf hm hz]

private theorem rotation_conformal {c : ℂ} (hc : ‖c‖ = 1) :
    IsConformalOnto (fun z : ℂ => c * z) unitDisc unitDisc := by
  have hc0 : c ≠ 0 := by intro h; simp [h] at hc
  refine ⟨((differentiable_const c).mul differentiable_id).differentiableOn,
    fun _ _ _ _ h => mul_left_cancel₀ hc0 h, ?_⟩
  apply Subset.antisymm
  · rintro w ⟨z, hz, rfl⟩
    simpa only [unitDisc, mem_ball_zero_iff, norm_mul, hc, one_mul] using hz
  · intro w hw
    refine ⟨c⁻¹ * w, ?_, ?_⟩
    · simpa only [unitDisc, mem_ball_zero_iff, norm_mul, norm_inv, hc, inv_one, one_mul] using hw
    · simp only [← mul_assoc, mul_inv_cancel₀ hc0, one_mul]

/-- Equality at a single point forces a genuine conformal bijection of the
whole disk. The normalized equality case is Mathlib's Schwarz rigidity. -/
theorem disc_schwarz_pick_rigidity {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f unitDisc) (hm : MapsTo f unitDisc unitDisc)
    {z : ℂ} (hz : z ∈ unitDisc)
    (heq : ‖deriv f z‖ * (1 - ‖z‖ ^ 2) = 1 - ‖f z‖ ^ 2) :
    IsConformalOnto f unitDisc unitDisc := by
  have hz' : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
  have hfz : ‖f z‖ < 1 := mem_ball_zero_iff.mp (hm hz)
  have hN := discNormalizedMap_differentiable hf hm hz
  have hN0 := discNormalizedMap_zero f z
  have hmap : MapsTo (discNormalizedMap f z) (ball 0 1)
      (closedBall (discNormalizedMap f z 0) 1) := by
    rw [hN0]
    exact fun w hw => ball_subset_closedBall (discNormalizedMap_mapsTo hm hz hw)
  have hderiv : ‖dslope (discNormalizedMap f z) 0 0‖ = (1 : ℝ) / 1 := by
    rw [dslope_same, discNormalizedMap_norm_derivative hf hm hz, heq,
      div_self (disc_defect_pos hfz).ne']
    norm_num
  let c : ℂ := dslope (discNormalizedMap f z) 0 0
  have hc : ‖c‖ = 1 := by simpa only [c, div_one] using hderiv
  have hlin := Complex.affine_of_mapsTo_ball_of_norm_dslope_eq_div
    hN hmap (mem_ball_self one_pos) hderiv
  have heqf : EqOn f (blaschke (-(f z)) ∘ (fun w : ℂ => c * w) ∘ blaschke z) unitDisc := by
    intro w hw
    have hw' : blaschke z w ∈ unitDisc :=
      mem_ball_zero_iff.mpr (blaschke_mem_unitDisc hz' (mem_ball_zero_iff.mp hw))
    have hrot : discNormalizedMap f z (blaschke z w) = c * blaschke z w := by
      calc
        discNormalizedMap f z (blaschke z w) = blaschke z w * c := by
          simpa only [hN0, zero_add, sub_zero, smul_eq_mul] using hlin hw'
        _ = c * blaschke z w := mul_comm _ _
    have h' := congrArg (blaschke (-(f z))) hrot
    simpa only [discNormalizedMap, Function.comp_apply,
      blaschke_neg_blaschke hz' (mem_ball_zero_iff.mp hw),
      blaschke_neg_blaschke hfz (mem_ball_zero_iff.mp (hm hw))] using h'
  have hconf : IsConformalOnto
      (blaschke (-(f z)) ∘ (fun w : ℂ => c * w) ∘ blaschke z) unitDisc unitDisc :=
    (isConformalOnto_blaschke (a := -(f z)) (by simpa using hfz)).comp
      ((rotation_conformal hc).comp (isConformalOnto_blaschke hz'))
  refine ⟨hf, ?_, ?_⟩
  · intro u hu v hv huv
    apply hconf.2.1 hu hv
    rw [← heqf hu, ← heqf hv]
    exact huv
  · exact (Set.image_congr heqf).trans hconf.2.2

end LowDimensionalTopology.Geometry.Hyperbolic
