module

public import LowDimensionalTopology.Geometry.Teichmuller.WeilPeterssonInnerPrincipalValue
public import LowDimensionalTopology.Geometry.Teichmuller.WeilPeterssonInnerL2Identification
public import LowDimensionalTopology.Geometry.Teichmuller.WeilPeterssonCauchySquareComposition
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Analysis.Complex.Liouville
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

/-!
# Local estimates for the actual weighted harmonic input

These finite Cauchy estimates use the original lifted quadratic differential.
They are intended for comparison of two positive exclusions of its Cauchy
square kernel. No parameter differentiation or general singular integral
operator is introduced.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Complex Set Metric Filter MeasureTheory
open scoped UpperHalfPlane ComplexConjugate Manifold ContDiff Topology

namespace LowDimensionalTopology.Geometry.Teichmuller.WeilPetersson.SourceKernel

open Surfaces LiZhongQC QuadraticBergman

variable {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {Γ : Subgroup GammaMeasurableBeltrami.Deck} (p : ℍ → X)
    (hp : let := R.toRiemannAtlas.toChartedSpace; IsUniformization Γ p)
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas)

include hp in
private theorem actualPhi_holomorphic :
    DifferentiableOn ℂ (uniformizedQuadratic R p q) upperHalf := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  exact utm_liftQD_differentiableOn q.property hp

private theorem actual_nearby_im_lower (ξ : ℍ) {w : ℂ}
    (hw : ‖w - (ξ : ℂ)‖ ≤ ξ.im / 2) : ξ.im / 2 ≤ w.im := by
  have him : |w.im - ξ.im| ≤ ξ.im / 2 := by
    have hnorm : |w.im - ξ.im| ≤ ‖w - (ξ : ℂ)‖ := by
      simpa only [sub_im, UpperHalfPlane.coe_im] using Complex.abs_im_le_norm (w - (ξ : ℂ))
    exact hnorm.trans hw
  linarith [(abs_le.mp him).1]

include hp in
private theorem actualPhi_deriv_bound (M : ℝ) (_hM : 0 ≤ M)
    (hb : ∀ a ∈ upperHalf, ‖uniformizedQuadratic R p q a‖ * a.im ^ 2 ≤ M)
    (ξ : ℍ) {w : ℂ} (hw : w ∈ closedBall (ξ : ℂ) (ξ.im / 4)) :
    ‖deriv (uniformizedQuadratic R p q) w‖ ≤ 16 * M / ξ.im ^ 3 := by
  have hwDist : ‖w - (ξ : ℂ)‖ ≤ ξ.im / 4 := by
    simpa only [mem_closedBall, dist_eq_norm] using hw
  have hnear (a : ℂ) (ha : a ∈ closedBall w (ξ.im / 4)) :
      ξ.im / 2 ≤ a.im := by
    have haDist : ‖a - w‖ ≤ ξ.im / 4 := by
      simpa only [mem_closedBall, dist_eq_norm] using ha
    apply actual_nearby_im_lower ξ
    calc
      ‖a - (ξ : ℂ)‖ ≤ ‖a - w‖ + ‖w - (ξ : ℂ)‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ ξ.im / 2 := by linarith
  have hupper (a : ℂ) (ha : a ∈ closedBall w (ξ.im / 4)) : a ∈ upperHalf := by
    exact lt_of_lt_of_le (by positivity : 0 < ξ.im / 2) (hnear a ha)
  have hdc := (actualPhi_holomorphic R p hp q).diffContOnCl_ball hupper
  have hcircle (a : ℂ) (ha : a ∈ sphere w (ξ.im / 4)) :
      ‖uniformizedQuadratic R p q a‖ ≤ 4 * M / ξ.im ^ 2 := by
    have haClosed : a ∈ closedBall w (ξ.im / 4) := sphere_subset_closedBall ha
    have haIm := hnear a haClosed
    have hsq : (ξ.im / 2) ^ 2 ≤ a.im ^ 2 :=
      pow_le_pow_left₀ (by positivity) haIm 2
    have hweight := hb a (hupper a haClosed)
    apply (le_div_iff₀ (sq_pos_of_pos ξ.im_pos)).2
    calc
      ‖uniformizedQuadratic R p q a‖ * ξ.im ^ 2 ≤
          ‖uniformizedQuadratic R p q a‖ * (4 * a.im ^ 2) :=
        mul_le_mul_of_nonneg_left (by nlinarith [hsq]) (norm_nonneg _)
      _ ≤ 4 * M := by nlinarith [hweight]
  calc
    _ ≤ (4 * M / ξ.im ^ 2) / (ξ.im / 4) :=
      Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (by positivity) hdc hcircle
    _ = _ := by field_simp [ξ.im_pos.ne']; ring

include hp in
private theorem actualPhi_local_lipschitz (M : ℝ) (hM : 0 ≤ M)
    (hb : ∀ a ∈ upperHalf, ‖uniformizedQuadratic R p q a‖ * a.im ^ 2 ≤ M)
    (ξ : ℍ) {w : ℂ} (hw : w ∈ closedBall (ξ : ℂ) (ξ.im / 4)) :
    ‖uniformizedQuadratic R p q w - uniformizedQuadratic R p q ξ‖ ≤
      (16 * M / ξ.im ^ 3) * ‖w - (ξ : ℂ)‖ := by
  have hdiff (a : ℂ) (ha : a ∈ closedBall (ξ : ℂ) (ξ.im / 4)) :
      DifferentiableAt ℂ (uniformizedQuadratic R p q) a := by
    have hdist : ‖a - (ξ : ℂ)‖ ≤ ξ.im / 2 := by
      have h := mem_closedBall.mp ha
      rw [dist_eq_norm] at h
      linarith [ξ.im_pos]
    have him := actual_nearby_im_lower ξ hdist
    exact (actualPhi_holomorphic R p hp q).differentiableAt
      (isOpen_upperHalf.mem_nhds (lt_of_lt_of_le (by positivity) him))
  exact Convex.norm_image_sub_le_of_norm_deriv_le hdiff
    (fun a ha => actualPhi_deriv_bound R p hp q M hM hb ξ ha)
    (convex_closedBall (ξ : ℂ) (ξ.im / 4)) (mem_closedBall_self (by positivity)) hw

private theorem actualPhi_value_bound (M : ℝ) (_hM : 0 ≤ M)
    (hb : ∀ a ∈ upperHalf, ‖uniformizedQuadratic R p q a‖ * a.im ^ 2 ≤ M)
    (ξ w : ℍ) (hw : ‖(w : ℂ) - ξ‖ ≤ ξ.im / 4) :
    ‖uniformizedQuadratic R p q w‖ ≤ 4 * M / ξ.im ^ 2 := by
  have hnear : ξ.im / 2 ≤ w.im := actual_nearby_im_lower ξ (by linarith [ξ.im_pos])
  have hsq : (ξ.im / 2) ^ 2 ≤ w.im ^ 2 :=
    pow_le_pow_left₀ (by positivity) hnear 2
  have hweight : ‖uniformizedQuadratic R p q w‖ * w.im ^ 2 ≤ M := hb (w : ℂ) w.im_pos
  apply (le_div_iff₀ (sq_pos_of_pos ξ.im_pos)).2
  calc
    ‖uniformizedQuadratic R p q w‖ * ξ.im ^ 2 ≤
        ‖uniformizedQuadratic R p q w‖ * (4 * w.im ^ 2) :=
      mul_le_mul_of_nonneg_left (by nlinarith [hsq]) (norm_nonneg _)
    _ ≤ 4 * M := by nlinarith [hweight, _hM]

include hp in
private theorem actualCoefficient_local_lipschitz (M : ℝ) (hM : 0 ≤ M)
    (hb : ∀ a ∈ upperHalf, ‖uniformizedQuadratic R p q a‖ * a.im ^ 2 ≤ M)
    (ξ w : ℍ) (hw : ‖(w : ℂ) - ξ‖ ≤ ξ.im / 4) :
    ‖NativeHarmonicBeltrami.coefficient R p q w -
      NativeHarmonicBeltrami.coefficient R p q ξ‖ ≤
        (32 * M / ξ.im) * ‖(w : ℂ) - ξ‖ := by
  have hnear : |w.im - ξ.im| ≤ ‖(w : ℂ) - ξ‖ := by
    simpa only [sub_im, UpperHalfPlane.coe_im] using
      Complex.abs_im_le_norm ((w : ℂ) - ξ)
  have hupper : w.im + ξ.im ≤ 3 * ξ.im := by
    have h := hnear.trans hw
    linarith [(abs_le.mp h).2, ξ.im_pos]
  have hsquares : |w.im ^ 2 - ξ.im ^ 2| ≤
      (3 * ξ.im) * ‖(w : ℂ) - ξ‖ := by
    rw [show w.im ^ 2 - ξ.im ^ 2 = (w.im - ξ.im) * (w.im + ξ.im) by ring,
      abs_mul, abs_of_pos (add_pos w.im_pos ξ.im_pos)]
    calc
      _ ≤ ‖(w : ℂ) - ξ‖ * (3 * ξ.im) :=
        mul_le_mul hnear hupper (by positivity) (norm_nonneg _)
      _ = _ := by ring
  have hphi := actualPhi_value_bound R p q M hM hb ξ w hw
  have hphiLip := actualPhi_local_lipschitz R p hp q M hM hb ξ
    (by simpa only [mem_closedBall, dist_eq_norm] using hw)
  have he : NativeHarmonicBeltrami.coefficient R p q w -
      NativeHarmonicBeltrami.coefficient R p q ξ =
      ((w.im ^ 2 - ξ.im ^ 2 : ℝ) : ℂ) * conj (uniformizedQuadratic R p q w) +
        ((ξ.im ^ 2 : ℝ) : ℂ) *
          conj (uniformizedQuadratic R p q w - uniformizedQuadratic R p q ξ) := by
    rw [NativeHarmonicBeltrami.coefficient_eq_uniformized,
      NativeHarmonicBeltrami.coefficient_eq_uniformized]
    simp only [map_sub]
    push_cast
    ring
  calc
    _ = ‖((w.im ^ 2 - ξ.im ^ 2 : ℝ) : ℂ) * conj (uniformizedQuadratic R p q w) +
        ((ξ.im ^ 2 : ℝ) : ℂ) *
          conj (uniformizedQuadratic R p q w - uniformizedQuadratic R p q ξ)‖ :=
      congrArg norm he
    _ ≤ ‖((w.im ^ 2 - ξ.im ^ 2 : ℝ) : ℂ) * conj (uniformizedQuadratic R p q w)‖ +
        ‖((ξ.im ^ 2 : ℝ) : ℂ) *
          conj (uniformizedQuadratic R p q w - uniformizedQuadratic R p q ξ)‖ :=
      norm_add_le _ _
    _ = |w.im ^ 2 - ξ.im ^ 2| * ‖uniformizedQuadratic R p q w‖ +
        ξ.im ^ 2 * ‖uniformizedQuadratic R p q w - uniformizedQuadratic R p q ξ‖ := by
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        Complex.norm_conj, abs_of_nonneg (sq_nonneg ξ.im)]
    _ ≤ ((3 * ξ.im) * ‖(w : ℂ) - ξ‖) * (4 * M / ξ.im ^ 2) +
        ξ.im ^ 2 * ((16 * M / ξ.im ^ 3) * ‖(w : ℂ) - ξ‖) :=
      add_le_add
        (mul_le_mul hsquares hphi (norm_nonneg _)
          (mul_nonneg (by positivity) (norm_nonneg _)))
        (mul_le_mul_of_nonneg_left hphiLip (sq_nonneg _))
    _ = (28 * M / ξ.im) * ‖(w : ℂ) - ξ‖ := by field_simp [ξ.im_pos.ne']; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      ((div_le_div_iff_of_pos_right ξ.im_pos).2 (by linarith)) (norm_nonneg _)

private theorem actual_anchor_distance (ξ z : ℍ) :
    ξ.im ≤ ‖(ξ : ℂ) - conj (z : ℂ)‖ := by
  calc
    ξ.im ≤ ξ.im + z.im := le_add_of_nonneg_right z.im_pos.le
    _ = ((ξ : ℂ) - conj (z : ℂ)).im := by
      simp only [sub_im, conj_im, UpperHalfPlane.coe_im, sub_neg_eq_add]
    _ ≤ |((ξ : ℂ) - conj (z : ℂ)).im| := le_abs_self _
    _ ≤ _ := Complex.abs_im_le_norm _

private theorem actual_anchor_value_bound (ξ z : ℍ) {a : ℂ}
    (ha : ‖a - (ξ : ℂ)‖ ≤ ξ.im / 2) :
    ‖cauchySquare a (conj (z : ℂ))‖ ≤
      4 * ‖cauchySquare ξ (conj (z : ℂ))‖ := by
  have hd := actual_anchor_distance ξ z
  have htri : ‖(ξ : ℂ) - conj (z : ℂ)‖ ≤
      ‖a - (ξ : ℂ)‖ + ‖a - conj (z : ℂ)‖ := by
    simpa only [norm_sub_rev] using norm_sub_le_norm_sub_add_norm_sub (ξ : ℂ) a (conj (z : ℂ))
  have hhalf : ‖(ξ : ℂ) - conj (z : ℂ)‖ / 2 ≤ ‖a - conj (z : ℂ)‖ := by
    linarith
  have hd0 : 0 < ‖(ξ : ℂ) - conj (z : ℂ)‖ := ξ.im_pos.trans_le hd
  have ha0 : 0 < ‖a - conj (z : ℂ)‖ := lt_of_lt_of_le (by positivity) hhalf
  have hsq := pow_le_pow_left₀ (by positivity) hhalf 2
  simp only [cauchySquare, norm_div, norm_one, norm_pow]
  rw [mul_one_div]
  apply (div_le_div_iff₀ (sq_pos_of_pos ha0) (sq_pos_of_pos hd0)).2
  nlinarith [hsq]

private theorem actual_anchor_holomorphic (z : ℍ) :
    DifferentiableOn ℂ (fun a : ℂ => cauchySquare a (conj (z : ℂ))) upperHalf := by
  intro a ha
  have hne : a - conj (z : ℂ) ≠ 0 := by
    intro he
    have him := congrArg Complex.im he
    simp only [sub_im, conj_im, UpperHalfPlane.coe_im, Complex.zero_im] at him
    linarith [show 0 < a.im from ha, z.im_pos]
  unfold cauchySquare
  exact ((differentiableAt_const (1 : ℂ)).div
    ((differentiableAt_id.sub_const (conj (z : ℂ))).pow 2)
      (pow_ne_zero 2 hne)).differentiableWithinAt

private theorem actual_anchor_deriv_bound (ξ z : ℍ) {w : ℂ}
    (hw : w ∈ closedBall (ξ : ℂ) (ξ.im / 4)) :
    ‖deriv (fun a : ℂ => cauchySquare a (conj (z : ℂ))) w‖ ≤
      (16 / ξ.im) * ‖cauchySquare ξ (conj (z : ℂ))‖ := by
  have hwDist : ‖w - (ξ : ℂ)‖ ≤ ξ.im / 4 := by
    simpa only [mem_closedBall, dist_eq_norm] using hw
  have hnear (a : ℂ) (ha : a ∈ closedBall w (ξ.im / 4)) :
      ‖a - (ξ : ℂ)‖ ≤ ξ.im / 2 := by
    have haDist : ‖a - w‖ ≤ ξ.im / 4 := by
      simpa only [mem_closedBall, dist_eq_norm] using ha
    exact (norm_sub_le_norm_sub_add_norm_sub a w (ξ : ℂ)).trans (by linarith)
  have hupper (a : ℂ) (ha : a ∈ closedBall w (ξ.im / 4)) : a ∈ upperHalf :=
    lt_of_lt_of_le (by positivity : 0 < ξ.im / 2)
      (actual_nearby_im_lower ξ (hnear a ha))
  have hdc := (actual_anchor_holomorphic z).diffContOnCl_ball hupper
  have hcircle (a : ℂ) (ha : a ∈ sphere w (ξ.im / 4)) :
      ‖cauchySquare a (conj (z : ℂ))‖ ≤ 4 * ‖cauchySquare ξ (conj (z : ℂ))‖ :=
    actual_anchor_value_bound ξ z (hnear a (sphere_subset_closedBall ha))
  calc
    _ ≤ (4 * ‖cauchySquare ξ (conj (z : ℂ))‖) / (ξ.im / 4) :=
      Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (by positivity) hdc hcircle
    _ = _ := by field_simp [ξ.im_pos.ne']; ring

private theorem actual_anchor_local_lipschitz (ξ z w : ℍ)
    (hw : ‖(w : ℂ) - ξ‖ ≤ ξ.im / 4) :
    ‖cauchySquare w (conj (z : ℂ)) - cauchySquare ξ (conj (z : ℂ))‖ ≤
      ((16 / ξ.im) * ‖cauchySquare ξ (conj (z : ℂ))‖) * ‖(w : ℂ) - ξ‖ := by
  have hdiff (a : ℂ) (ha : a ∈ closedBall (ξ : ℂ) (ξ.im / 4)) :
      DifferentiableAt ℂ (fun b : ℂ => cauchySquare b (conj (z : ℂ))) a := by
    have hdist : ‖a - (ξ : ℂ)‖ ≤ ξ.im / 2 := by
      have h := mem_closedBall.mp ha
      rw [dist_eq_norm] at h
      linarith [ξ.im_pos]
    have him := actual_nearby_im_lower ξ hdist
    exact (actual_anchor_holomorphic z).differentiableAt
      (isOpen_upperHalf.mem_nhds (lt_of_lt_of_le (by positivity) him))
  exact Convex.norm_image_sub_le_of_norm_deriv_le hdiff
    (fun a ha => actual_anchor_deriv_bound ξ z ha)
    (convex_closedBall (ξ : ℂ) (ξ.im / 4)) (mem_closedBall_self (by positivity))
    (by simpa only [mem_closedBall, dist_eq_norm] using hw)

include hp in
private theorem actual_weighted_input_local_lipschitz (M : ℝ) (hM : 0 ≤ M)
    (hb : ∀ a ∈ upperHalf, ‖uniformizedQuadratic R p q a‖ * a.im ^ 2 ≤ M)
    (ξ z w : ℍ) (hw : ‖(w : ℂ) - ξ‖ ≤ ξ.im / 4) :
    ‖NativeHarmonicBeltrami.coefficient R p q w * cauchySquare w (conj (z : ℂ)) -
        NativeHarmonicBeltrami.coefficient R p q ξ * cauchySquare ξ (conj (z : ℂ))‖ ≤
      ((256 * M / ξ.im) * ‖cauchySquare ξ (conj (z : ℂ))‖) * ‖(w : ℂ) - ξ‖ := by
  have hmu := actualCoefficient_local_lipschitz R p hp q M hM hb ξ w hw
  have hmu0 : ‖NativeHarmonicBeltrami.coefficient R p q ξ‖ ≤ M := by
    rw [NativeHarmonicBeltrami.norm_coefficient]
    exact hb (ξ : ℂ) ξ.im_pos
  have hk := actual_anchor_value_bound ξ z (by linarith [ξ.im_pos] : ‖(w : ℂ) - ξ‖ ≤ ξ.im / 2)
  have hkLip := actual_anchor_local_lipschitz ξ z w hw
  have he : NativeHarmonicBeltrami.coefficient R p q w * cauchySquare w (conj (z : ℂ)) -
        NativeHarmonicBeltrami.coefficient R p q ξ * cauchySquare ξ (conj (z : ℂ)) =
      (NativeHarmonicBeltrami.coefficient R p q w -
        NativeHarmonicBeltrami.coefficient R p q ξ) * cauchySquare w (conj (z : ℂ)) +
      NativeHarmonicBeltrami.coefficient R p q ξ *
        (cauchySquare w (conj (z : ℂ)) - cauchySquare ξ (conj (z : ℂ))) := by ring
  calc
    _ ≤ ‖(NativeHarmonicBeltrami.coefficient R p q w -
          NativeHarmonicBeltrami.coefficient R p q ξ) * cauchySquare w (conj (z : ℂ))‖ +
        ‖NativeHarmonicBeltrami.coefficient R p q ξ *
          (cauchySquare w (conj (z : ℂ)) - cauchySquare ξ (conj (z : ℂ)))‖ := by
      rw [he]
      exact norm_add_le _ _
    _ = ‖NativeHarmonicBeltrami.coefficient R p q w -
          NativeHarmonicBeltrami.coefficient R p q ξ‖ * ‖cauchySquare w (conj (z : ℂ))‖ +
        ‖NativeHarmonicBeltrami.coefficient R p q ξ‖ *
          ‖cauchySquare w (conj (z : ℂ)) - cauchySquare ξ (conj (z : ℂ))‖ := by
      rw [norm_mul, norm_mul]
    _ ≤ ((32 * M / ξ.im) * ‖(w : ℂ) - ξ‖) *
          (4 * ‖cauchySquare ξ (conj (z : ℂ))‖) +
        M * (((16 / ξ.im) * ‖cauchySquare ξ (conj (z : ℂ))‖) * ‖(w : ℂ) - ξ‖) :=
      add_le_add
        (mul_le_mul hmu hk (norm_nonneg _) (by positivity))
        (mul_le_mul hmu0 hkLip (norm_nonneg _) hM)
    _ = ((144 * M / ξ.im) * ‖cauchySquare ξ (conj (z : ℂ))‖) *
        ‖(w : ℂ) - ξ‖ := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        ((div_le_div_iff_of_pos_right ξ.im_pos).2 (by linarith)) (norm_nonneg _))
      (norm_nonneg _)

theorem actual_input_ae (z : ℍ) :
    innerInput (fun η => (NativeHarmonicBeltrami.ofQuadratic R p hp q).val η) z =ᵐ[volume]
      innerInput (NativeHarmonicBeltrami.coefficient R p q) z := by
  apply ae_of_ae_restrict_of_ae_restrict_compl upperHalf
  · rw [← GammaMeasurableBeltrami.map_flat_coe,
      UpperHalfPlane.measurableEmbedding_coe.ae_map_iff]
    filter_upwards [GammaMeasurableBeltrami.ae_hyperbolic_iff.mp
      (NativeHarmonicBeltrami.ofQuadratic_coe_ae R p hp q)] with η hη
    simpa only [innerInput, upperExtension,
      dite_eq_left (show 0 < (η : ℂ).im from η.im_pos)] using
      congrArg (fun a : ℂ => a * cauchySquare η (conj (z : ℂ))) hη
  · apply ae_restrict_of_forall_mem isOpen_upperHalf.measurableSet.compl
    intro η hη
    simp only [innerInput, upperExtension, show ¬0 < η.im from hη, dite_false]

include hp in
private theorem actual_literal_PV (z ξ : ℍ) :
    PrincipalValueExists (innerInput (NativeHarmonicBeltrami.coefficient R p q) z) ξ := by
  have h := actual_input_ae R p hp q z
  have hpv := innerInput_ofQuadratic_principalValueExists R hp q z ξ
  have he (r : ℝ) :
      (∫ η in {η : ℂ | r < ‖η - ξ‖},
        innerInput (fun w => (NativeHarmonicBeltrami.ofQuadratic R p hp q).val w) z η /
          (η - ξ) ^ 2) =
        ∫ η in {η : ℂ | r < ‖η - ξ‖},
          innerInput (NativeHarmonicBeltrami.coefficient R p q) z η / (η - ξ) ^ 2 := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae h] with η hη
    rw [hη]
  refine ⟨fun r hr => (hpv.1 r hr).congr ?_, ?_⟩
  · filter_upwards [ae_restrict_of_ae h] with η hη
    rw [hη]
  · have hH := congrFun (hilbertHSmooth_congr_ae h) (ξ : ℂ)
    simpa only [he, hH] using hpv.2

theorem actual_literal_input_value (z ξ : ℍ) :
    innerInput (NativeHarmonicBeltrami.coefficient R p q) z ξ =
      NativeHarmonicBeltrami.coefficient R p q ξ * cauchySquare ξ (conj (z : ℂ)) := by
  simp only [innerInput, upperExtension, dite_eq_left (show 0 < (ξ : ℂ).im from ξ.im_pos)]

include hp in
private theorem actual_remainder_ball_bound (M : ℝ) (hM : 0 ≤ M)
    (hb : ∀ a ∈ upperHalf, ‖uniformizedQuadratic R p q a‖ * a.im ^ 2 ≤ M)
    (ξ z : ℍ) {r : ℝ} (hr : 0 < r) (hrY : r ≤ ξ.im / 4) :
    IntegrableOn (fun η : ℂ =>
      (innerInput (NativeHarmonicBeltrami.coefficient R p q) z η -
        innerInput (NativeHarmonicBeltrami.coefficient R p q) z ξ) / (η - ξ) ^ 2)
      (ball (ξ : ℂ) r) ∧
    (∫ η : ℂ in ball (ξ : ℂ) r,
      ‖(innerInput (NativeHarmonicBeltrami.coefficient R p q) z η -
        innerInput (NativeHarmonicBeltrami.coefficient R p q) z ξ) / (η - ξ) ^ 2‖) ≤
      2 * Real.pi * ((256 * M / ξ.im) * ‖cauchySquare ξ (conj (z : ℂ))‖) * r := by
  let f : ℂ → ℂ := innerInput (NativeHarmonicBeltrami.coefficient R p q) z
  let L : ℝ := (256 * M / ξ.im) * ‖cauchySquare ξ (conj (z : ℂ))‖
  let rem : ℂ → ℂ := fun η => (f η - f ξ) / (η - ξ) ^ 2
  let G : ℂ → ℂ := (ball (ξ : ℂ) (ξ.im / 4)).indicator rem
  have hL : 0 ≤ L := by dsimp only [L]; positivity
  have hf : MemLp f 2 (volume : Measure ℂ) :=
    (memLp_congr_ae (actual_input_ae R p hp q z)).mp
      (innerInput_memLp_two (NativeHarmonicBeltrami.ofQuadratic R p hp q).val z)
  have hrem : AEStronglyMeasurable rem volume :=
    ((hf.aestronglyMeasurable.aemeasurable.sub_const _).div
      ((measurable_id.sub_const (ξ : ℂ)).pow_const 2).aemeasurable).aestronglyMeasurable
  have hG : AEStronglyMeasurable G volume := hrem.indicator measurableSet_ball
  have hGb (η : ℂ) (hne : η ≠ (ξ : ℂ)) : ‖G η‖ ≤ L / ‖η - ξ‖ := by
    have hd : 0 < ‖η - (ξ : ℂ)‖ := norm_pos_iff.2 (sub_ne_zero.2 hne)
    by_cases hη : η ∈ ball (ξ : ℂ) (ξ.im / 4)
    · have hηDist : ‖η - (ξ : ℂ)‖ < ξ.im / 4 := by
        simpa only [mem_ball, dist_eq_norm] using hη
      have hηIm : 0 < η.im := lt_of_lt_of_le (by positivity : 0 < ξ.im / 2)
        (actual_nearby_im_lower ξ (by linarith))
      let ηH : ℍ := ⟨η, hηIm⟩
      have hvalη : f η = NativeHarmonicBeltrami.coefficient R p q ηH *
          cauchySquare ηH (conj (z : ℂ)) := actual_literal_input_value R p q z ηH
      have hvalξ : f ξ = NativeHarmonicBeltrami.coefficient R p q ξ *
          cauchySquare ξ (conj (z : ℂ)) := actual_literal_input_value R p q z ξ
      have hLip : ‖f η - f ξ‖ ≤ L * ‖η - ξ‖ := by
        rw [hvalη, hvalξ]
        exact actual_weighted_input_local_lipschitz R p hp q M hM hb ξ z ηH hηDist.le
      change ‖(ball (ξ : ℂ) (ξ.im / 4)).indicator rem η‖ ≤ L / ‖η - ξ‖
      rw [indicator_of_mem hη]
      change ‖(f η - f ξ) / (η - ξ) ^ 2‖ ≤ L / ‖η - ξ‖
      rw [norm_div, norm_pow]
      calc
        _ ≤ (L * ‖η - ξ‖) / ‖η - ξ‖ ^ 2 :=
          div_le_div_of_nonneg_right hLip (sq_nonneg _)
        _ = _ := by field_simp [hd.ne']
    · change ‖(ball (ξ : ℂ) (ξ.im / 4)).indicator rem η‖ ≤ L / ‖η - ξ‖
      rw [indicator_of_notMem hη, norm_zero]
      exact div_nonneg hL (norm_nonneg _)
  have hGint : IntegrableOn G (ball (ξ : ℂ) r) :=
    integrableOn_ball_of_norm_le_div hL hr hG hGb
  have hnormG : (∫ η in ball (ξ : ℂ) r, ‖G η‖) ≤ 2 * Real.pi * L * r := by
    have hlin := lintegral_enorm_le_of_norm_le_div hL (ball (ξ : ℂ) r) hGb
    rw [lintegral_ball_sub_enorm_rpow_neg (a := 1) (by norm_num) hr (ξ : ℂ)] at hlin
    have hfin : ENNReal.ofReal L *
        (ENNReal.ofReal (2 * Real.pi) * ENNReal.ofReal (r ^ (2 - (1 : ℝ)) / (2 - 1))) ≠ ⊤ := by
      finiteness
    have hreal := ENNReal.toReal_mono hfin hlin
    rw [← integral_norm_eq_lintegral_enorm hG.restrict] at hreal
    calc
      _ ≤ L * ((2 * Real.pi) * r) := by
        simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hL,
          show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one, div_one,
          ENNReal.toReal_ofReal (by positivity : 0 ≤ 2 * Real.pi),
          ENNReal.toReal_ofReal hr.le, mul_assoc] using hreal
      _ = _ := by ring
  have he (η : ℂ) (hη : η ∈ ball (ξ : ℂ) r) : G η = rem η :=
    indicator_of_mem ((ball_subset_ball hrY) hη) rem
  have hremInt : IntegrableOn rem (ball (ξ : ℂ) r) :=
    hGint.congr_fun he measurableSet_ball
  refine ⟨hremInt, ?_⟩
  calc
    _ = ∫ η in ball (ξ : ℂ) r, ‖G η‖ := by
      apply integral_congr_ae
      exact ae_restrict_of_forall_mem measurableSet_ball fun η hη => congrArg norm (he η hη).symm
    _ ≤ _ := hnormG

private theorem actual_exterior_sdiff_ae (ξ : ℂ) (s r : ℝ) :
    ({η : ℂ | s < ‖η - ξ‖} \ {η : ℂ | r < ‖η - ξ‖}) =ᵐ[volume] annulusAt ξ s r := by
  refine ae_eq_set.2 ⟨measure_mono_null (fun η hη => ?_)
    (Measure.addHaar_sphere volume ξ r), measure_mono_null (fun η hη => ?_) measure_empty⟩
  · rw [mem_sphere, dist_eq_norm]
    have hle : ‖η - ξ‖ ≤ r := le_of_not_gt hη.1.2
    have hge : r ≤ ‖η - ξ‖ := by
      apply le_of_not_gt
      intro hlt
      exact hη.2 ⟨hη.1.1, hlt⟩
    exact le_antisymm hle hge
  · exact False.elim (hη.2 ⟨hη.1.1, not_lt.mpr hη.1.2.le⟩)

include hp in
private theorem actual_centered_radial_error (M : ℝ) (hM : 0 ≤ M)
    (hb : ∀ a ∈ upperHalf, ‖uniformizedQuadratic R p q a‖ * a.im ^ 2 ≤ M)
    (ξ z : ℍ) {r : ℝ} (hr : 0 < r) (hrY : r ≤ ξ.im / 4) :
    ‖(-(1 / (Real.pi : ℂ)) * ∫ η in {η : ℂ | r < ‖η - ξ‖},
        innerInput (NativeHarmonicBeltrami.coefficient R p q) z η / (η - ξ) ^ 2) -
      hilbertHSmooth (innerInput (NativeHarmonicBeltrami.coefficient R p q) z) ξ‖ ≤
      2 * ((256 * M / ξ.im) * ‖cauchySquare ξ (conj (z : ℂ))‖) * r := by
  let f : ℂ → ℂ := innerInput (NativeHarmonicBeltrami.coefficient R p q) z
  let L : ℝ := (256 * M / ξ.im) * ‖cauchySquare ξ (conj (z : ℂ))‖
  let rem : ℂ → ℂ := fun η => (f η - f ξ) / (η - ξ) ^ 2
  let T : ℝ → ℂ := fun s => -(1 / (Real.pi : ℂ)) *
    ∫ η in {η : ℂ | s < ‖η - ξ‖}, f η / (η - ξ) ^ 2
  have hpv := actual_literal_PV R p hp q z ξ
  have hbrem := actual_remainder_ball_bound R p hp q M hM hb ξ z hr hrY
  have hpi : ‖-(1 / (Real.pi : ℂ))‖ = 1 / Real.pi := by
    rw [norm_neg, norm_div, norm_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos]
  have hfinite (s : ℝ) (hs : 0 < s) (hsr : s < r) : ‖T s - T r‖ ≤ 2 * L * r := by
    have hsub : {η : ℂ | r < ‖η - ξ‖} ⊆ {η : ℂ | s < ‖η - ξ‖} :=
      fun η hη => hsr.trans hη
    have hF : IntegrableOn (fun η : ℂ => f η / (η - ξ) ^ 2) (annulusAt ξ s r) :=
      (hpv.1 s hs).mono_set (fun η hη => hη.1)
    have hAnnBall : annulusAt (ξ : ℂ) s r ⊆ ball (ξ : ℂ) r := by
      intro η hη
      simpa only [mem_ball, dist_eq_norm] using hη.2
    have hRem : IntegrableOn rem (annulusAt (ξ : ℂ) s r) := hbrem.1.mono_set hAnnBall
    have hconstant : (∫ η in annulusAt (ξ : ℂ) s r, f η / (η - ξ) ^ 2) -
        (∫ η in annulusAt (ξ : ℂ) s r, rem η) = 0 := by
      rw [← integral_sub hF hRem]
      calc
        _ = f ξ * ∫ η in annulusAt (ξ : ℂ) s r, 1 / (η - ξ) ^ 2 := by
          rw [← integral_const_mul]
          apply integral_congr_ae
          exact Eventually.of_forall fun η => by
            change f η / (η - ξ) ^ 2 - (f η - f ξ) / (η - ξ) ^ 2 =
              f ξ * (1 / (η - ξ) ^ 2)
            ring
        _ = 0 := by rw [integral_annulus_inv_sq (ξ : ℂ) hs hsr, mul_zero]
    have hdiff : (∫ η in {η : ℂ | s < ‖η - ξ‖}, f η / (η - ξ) ^ 2) -
        (∫ η in {η : ℂ | r < ‖η - ξ‖}, f η / (η - ξ) ^ 2) =
          ∫ η in annulusAt (ξ : ℂ) s r, rem η := by
      calc
        _ = ∫ η in {η : ℂ | s < ‖η - ξ‖} \ {η : ℂ | r < ‖η - ξ‖},
            f η / (η - ξ) ^ 2 :=
          (setIntegral_sdiff (measurableSet_lt measurable_const (by fun_prop))
            (hpv.1 s hs) hsub).symm
        _ = ∫ η in annulusAt (ξ : ℂ) s r, f η / (η - ξ) ^ 2 :=
          setIntegral_congr_set (actual_exterior_sdiff_ae (ξ : ℂ) s r)
        _ = _ := sub_eq_zero.mp hconstant
    have hnormRem : ‖∫ η in annulusAt (ξ : ℂ) s r, rem η‖ ≤ 2 * Real.pi * L * r := by
      calc
        _ ≤ ∫ η in annulusAt (ξ : ℂ) s r, ‖rem η‖ := norm_integral_le_integral_norm _
        _ ≤ ∫ η in ball (ξ : ℂ) r, ‖rem η‖ :=
          integral_mono_measure (Measure.restrict_mono hAnnBall le_rfl)
            (Eventually.of_forall fun η => norm_nonneg _) hbrem.1.norm
        _ ≤ _ := hbrem.2
    have he : T s - T r = -(1 / (Real.pi : ℂ)) *
        ∫ η in annulusAt (ξ : ℂ) s r, rem η := by
      change -(1 / (Real.pi : ℂ)) * _ - -(1 / (Real.pi : ℂ)) * _ = _
      rw [← mul_sub, hdiff]
    calc
      _ = (1 / Real.pi) * ‖∫ η in annulusAt (ξ : ℂ) s r, rem η‖ := by
        rw [he, norm_mul, hpi]
      _ ≤ (1 / Real.pi) * (2 * Real.pi * L * r) :=
        mul_le_mul_of_nonneg_left hnormRem (by positivity)
      _ = _ := by field_simp [Real.pi_ne_zero]
  have hlim : Tendsto (fun s => ‖T s - T r‖) (𝓝[>] (0 : ℝ))
      (𝓝 ‖hilbertHSmooth f ξ - T r‖) := (hpv.2.sub_const (T r)).norm
  have hevent : ∀ᶠ s in 𝓝[>] (0 : ℝ), ‖T s - T r‖ ≤ 2 * L * r := by
    filter_upwards [Ioo_mem_nhdsGT hr] with s hs
    exact hfinite s hs.1 hs.2
  have h := le_of_tendsto hlim hevent
  simpa only [norm_sub_rev] using h

def actualInvariantExterior (ξ : ℍ) (e : ℝ) : Set ℂ :=
  {w : ℂ | e * ‖w - conj (ξ : ℂ)‖ < ‖w - (ξ : ℂ)‖}

private theorem actual_conjugate_distance_le (ξ : ℍ) :
    ‖(ξ : ℂ) - conj (ξ : ℂ)‖ ≤ 2 * ξ.im := by
  have h := Complex.norm_le_abs_re_add_abs_im ((ξ : ℂ) - conj (ξ : ℂ))
  have he : |((ξ : ℂ) - conj (ξ : ℂ)).re| +
      |((ξ : ℂ) - conj (ξ : ℂ)).im| = 2 * ξ.im := by
    simp only [sub_re, conj_re, sub_self, abs_zero, zero_add,
      sub_im, conj_im, UpperHalfPlane.coe_im, sub_neg_eq_add]
    rw [← two_mul, abs_of_pos (by positivity)]
  exact h.trans_eq he

private theorem actual_cross_distance_bounds (ξ : ℍ) (w : ℂ) :
    2 * ξ.im ≤ ‖w - (ξ : ℂ)‖ + ‖w - conj (ξ : ℂ)‖ ∧
      ‖w - conj (ξ : ℂ)‖ ≤ ‖w - (ξ : ℂ)‖ + 2 * ξ.im := by
  have hleft : -(w.im - ξ.im) ≤ ‖w - (ξ : ℂ)‖ := by
    have him : |w.im - ξ.im| ≤ ‖w - (ξ : ℂ)‖ := by
      simpa only [sub_im, UpperHalfPlane.coe_im] using Complex.abs_im_le_norm (w - (ξ : ℂ))
    exact (neg_le_abs _).trans him
  have hright : w.im + ξ.im ≤ ‖w - conj (ξ : ℂ)‖ := by
    have him : |w.im + ξ.im| ≤ ‖w - conj (ξ : ℂ)‖ := by
      simpa only [sub_im, conj_im, UpperHalfPlane.coe_im, sub_neg_eq_add] using
        Complex.abs_im_le_norm (w - conj (ξ : ℂ))
    exact (le_abs_self _).trans him
  refine ⟨by linarith, ?_⟩
  calc
    _ ≤ ‖w - (ξ : ℂ)‖ + ‖(ξ : ℂ) - conj (ξ : ℂ)‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ _ := add_le_add le_rfl (actual_conjugate_distance_le ξ)

private theorem actualInvariantExterior_between (ξ : ℍ) {e : ℝ}
    (he0 : 0 < e) (he1 : e < 1) :
    {w : ℂ | 2 * e * ξ.im / (1 - e) < ‖w - (ξ : ℂ)‖} ⊆
        actualInvariantExterior ξ e ∧
      actualInvariantExterior ξ e ⊆
        {w : ℂ | 2 * e * ξ.im / (1 + e) < ‖w - (ξ : ℂ)‖} := by
  constructor
  · intro w hw
    have hmul : 2 * e * ξ.im < ‖w - (ξ : ℂ)‖ * (1 - e) :=
      (div_lt_iff₀ (by linarith : 0 < 1 - e)).mp hw
    have hcross := (actual_cross_distance_bounds ξ w).2
    have hweighted := mul_le_mul_of_nonneg_left hcross he0.le
    change e * ‖w - conj (ξ : ℂ)‖ < ‖w - (ξ : ℂ)‖
    nlinarith
  · intro w hw
    have hcross := (actual_cross_distance_bounds ξ w).1
    have hweighted := mul_le_mul_of_nonneg_left hcross he0.le
    change e * ‖w - conj (ξ : ℂ)‖ < ‖w - (ξ : ℂ)‖ at hw
    change 2 * e * ξ.im / (1 + e) < ‖w - (ξ : ℂ)‖
    apply (div_lt_iff₀ (by linarith : 0 < 1 + e)).2
    nlinarith

private theorem actual_literal_input_ball_bound (M : ℝ) (hM : 0 ≤ M)
    (hb : ∀ a ∈ upperHalf, ‖uniformizedQuadratic R p q a‖ * a.im ^ 2 ≤ M)
    (ξ z : ℍ) {η : ℂ} (hη : ‖η - (ξ : ℂ)‖ ≤ ξ.im / 4) :
    ‖innerInput (NativeHarmonicBeltrami.coefficient R p q) z η‖ ≤
      4 * M * ‖cauchySquare ξ (conj (z : ℂ))‖ := by
  have hηIm : 0 < η.im := lt_of_lt_of_le (by positivity : 0 < ξ.im / 2)
    (actual_nearby_im_lower ξ (by linarith [ξ.im_pos]))
  let ηH : ℍ := ⟨η, hηIm⟩
  have hmu : ‖NativeHarmonicBeltrami.coefficient R p q ηH‖ ≤ M := by
    rw [NativeHarmonicBeltrami.norm_coefficient]
    exact hb η hηIm
  have hk := actual_anchor_value_bound ξ z (by linarith [ξ.im_pos] : ‖η - (ξ : ℂ)‖ ≤ ξ.im / 2)
  calc
    _ = ‖NativeHarmonicBeltrami.coefficient R p q ηH‖ *
        ‖cauchySquare ηH (conj (z : ℂ))‖ := by
      rw [show innerInput (NativeHarmonicBeltrami.coefficient R p q) z η =
        NativeHarmonicBeltrami.coefficient R p q ηH * cauchySquare ηH (conj (z : ℂ)) from
          actual_literal_input_value R p q z ηH, norm_mul]
    _ ≤ M * (4 * ‖cauchySquare ξ (conj (z : ℂ))‖) :=
      mul_le_mul hmu hk (norm_nonneg _) hM
    _ = _ := by ring

private theorem actual_annulus_real_area (ξ : ℂ) {s r : ℝ} (hs : 0 ≤ s) (hsr : s ≤ r) :
    volume.real (closedBall ξ r \ closedBall ξ s) = Real.pi * (r ^ 2 - s ^ 2) := by
  have hv (t : ℝ) (ht : 0 ≤ t) :
      volume.real (closedBall ξ t) = Real.pi * t ^ 2 := by
    simp [Measure.real, Complex.volume_closedBall, ENNReal.toReal_mul, ht, mul_comm]
  rw [measureReal_sdiff (closedBall_subset_closedBall hsr) measurableSet_closedBall
      measure_closedBall_lt_top.ne,
    hv r (hs.trans hsr), hv s hs]
  ring

include hp in
theorem actual_invariant_error_bound (M : ℝ) (hM : 0 ≤ M)
    (hb : ∀ a ∈ upperHalf, ‖uniformizedQuadratic R p q a‖ * a.im ^ 2 ≤ M)
    (ξ z : ℍ) {e : ℝ} (he0 : 0 < e) (he16 : e < 1 / 16) :
    ‖(-(1 / (Real.pi : ℂ)) * ∫ η in actualInvariantExterior ξ e,
        innerInput (NativeHarmonicBeltrami.coefficient R p q) z η / (η - ξ) ^ 2) -
      hilbertHSmooth (innerInput (NativeHarmonicBeltrami.coefficient R p q) z) ξ‖ ≤
      4096 * M * e * ‖cauchySquare ξ (conj (z : ℂ))‖ := by
  let f : ℂ → ℂ := innerInput (NativeHarmonicBeltrami.coefficient R p q) z
  let k : ℝ := ‖cauchySquare ξ (conj (z : ℂ))‖
  let rm : ℝ := 2 * e * ξ.im / (1 + e)
  let rp : ℝ := 2 * e * ξ.im / (1 - e)
  let A : Set ℂ := {η : ℂ | rm < ‖η - ξ‖} \ actualInvariantExterior ξ e
  let T : ℂ := -(1 / (Real.pi : ℂ)) * ∫ η in {η : ℂ | rm < ‖η - ξ‖}, f η / (η - ξ) ^ 2
  let H : ℂ := -(1 / (Real.pi : ℂ)) * ∫ η in actualInvariantExterior ξ e, f η / (η - ξ) ^ 2
  have he1 : e < 1 := he16.trans (by norm_num)
  have hplus : 0 < 1 + e := by linarith
  have hminus : 0 < 1 - e := by linarith
  have hrm : 0 < rm := div_pos (by positivity) hplus
  have hrp : 0 < rp := div_pos (by positivity) hminus
  have hrmrp : rm ≤ rp :=
    div_le_div_of_nonneg_left (by positivity) hminus (by linarith)
  have hrpY : rp ≤ ξ.im / 4 := by
    apply (div_le_iff₀ hminus).2
    have heY := mul_le_mul_of_nonneg_right he16.le ξ.im_pos.le
    nlinarith
  have hrmUpper : rm ≤ 2 * e * ξ.im := div_le_self (by positivity) (by linarith)
  have hgeo := actualInvariantExterior_between ξ he0 he1
  have hD : MeasurableSet (actualInvariantExterior ξ e) :=
    measurableSet_lt
      (measurable_const.mul (measurable_id.sub_const (conj (ξ : ℂ))).norm)
      (measurable_id.sub_const (ξ : ℂ)).norm
  have hDsub : actualInvariantExterior ξ e ⊆ {η : ℂ | rm < ‖η - ξ‖} := hgeo.2
  have hAsub : A ⊆ closedBall (ξ : ℂ) rp \ closedBall (ξ : ℂ) rm := by
    intro η hη
    have hηrm : rm < ‖η - (ξ : ℂ)‖ := hη.1
    have hηrp : ‖η - (ξ : ℂ)‖ ≤ rp := by
      by_contra hn
      exact hη.2 (hgeo.1 (lt_of_not_ge hn))
    exact ⟨by simpa only [mem_closedBall, dist_eq_norm] using hηrp,
      by simpa only [mem_closedBall, dist_eq_norm, not_le] using hηrm⟩
  have hAfin : volume A < ⊤ :=
    (measure_mono (hAsub.trans sdiff_subset)).trans_lt measure_closedBall_lt_top
  have hArea : volume.real A ≤ Real.pi * (rp ^ 2 - rm ^ 2) :=
    (measureReal_mono hAsub (measure_ne_top_of_subset sdiff_subset
      measure_closedBall_lt_top.ne)).trans_eq (actual_annulus_real_area (ξ : ℂ) hrm.le hrmrp)
  have hpv := actual_literal_PV R p hp q z ξ
  have _hDint : IntegrableOn (fun η : ℂ => f η / (η - ξ) ^ 2)
      (actualInvariantExterior ξ e) := (hpv.1 rm hrm).mono_set hDsub
  have _hAint : IntegrableOn (fun η : ℂ => f η / (η - ξ) ^ 2) A :=
    (hpv.1 rm hrm).mono_set sdiff_subset
  have hpoint (η : ℂ) (hη : η ∈ A) :
      ‖f η / (η - ξ) ^ 2‖ ≤ (4 * M * k) / rm ^ 2 := by
    have hηrm : rm < ‖η - (ξ : ℂ)‖ := hη.1
    have hηrp : ‖η - (ξ : ℂ)‖ ≤ rp := by
      simpa only [mem_closedBall, dist_eq_norm] using (hAsub hη).1
    have hval := actual_literal_input_ball_bound R p q M hM hb ξ z (hηrp.trans hrpY)
    rw [norm_div, norm_pow]
    calc
      _ ≤ (4 * M * k) / ‖η - ξ‖ ^ 2 := div_le_div_of_nonneg_right hval (sq_nonneg _)
      _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos hrm)
        (pow_le_pow_left₀ hrm.le hηrm.le 2)
  have hnorm : ‖∫ η in A, f η / (η - ξ) ^ 2‖ ≤
      ((4 * M * k) / rm ^ 2) * (Real.pi * (rp ^ 2 - rm ^ 2)) :=
    (norm_setIntegral_le_of_norm_le_const hAfin hpoint).trans
      (mul_le_mul_of_nonneg_left hArea (by positivity))
  have heq : T - H = -(1 / (Real.pi : ℂ)) * ∫ η in A, f η / (η - ξ) ^ 2 := by
    change -(1 / (Real.pi : ℂ)) * _ - -(1 / (Real.pi : ℂ)) * _ = _
    rw [← mul_sub, ← setIntegral_sdiff hD (hpv.1 rm hrm) hDsub]
  have hpi : ‖-(1 / (Real.pi : ℂ))‖ = 1 / Real.pi := by
    rw [norm_neg, norm_div, norm_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos]
  have hshape : ‖H - T‖ ≤ 20 * M * e * k := by
    calc
      _ = (1 / Real.pi) * ‖∫ η in A, f η / (η - ξ) ^ 2‖ := by
        rw [norm_sub_rev, heq, norm_mul, hpi]
      _ ≤ (1 / Real.pi) * (((4 * M * k) / rm ^ 2) *
          (Real.pi * (rp ^ 2 - rm ^ 2))) :=
        mul_le_mul_of_nonneg_left hnorm (by positivity)
      _ = (16 * M * k * e) / (1 - e) ^ 2 := by
        dsimp only [rm, rp]
        field_simp [Real.pi_ne_zero, he0.ne', ξ.im_pos.ne', hplus.ne', hminus.ne']
        ring
      _ ≤ _ := by
        apply (div_le_iff₀ (sq_pos_of_pos hminus)).2
        have hden : (4 : ℝ) / 5 ≤ (1 - e) ^ 2 := by nlinarith [sq_nonneg e]
        have hN : 0 ≤ 20 * M * k * e := by positivity
        nlinarith [mul_le_mul_of_nonneg_left hden hN]
  have hcenter : ‖T - hilbertHSmooth f ξ‖ ≤ 1024 * M * e * k := by
    calc
      _ ≤ 2 * ((256 * M / ξ.im) * k) * rm :=
        actual_centered_radial_error R p hp q M hM hb ξ z hrm (hrmrp.trans hrpY)
      _ ≤ 2 * ((256 * M / ξ.im) * k) * (2 * e * ξ.im) :=
        mul_le_mul_of_nonneg_left hrmUpper (by positivity)
      _ = _ := by dsimp only [k]; field_simp [ξ.im_pos.ne']; ring
  calc
    _ ≤ ‖H - T‖ + ‖T - hilbertHSmooth f ξ‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ 20 * M * e * k + 1024 * M * e * k := add_le_add hshape hcenter
    _ ≤ _ := by nlinarith [mul_nonneg (mul_nonneg hM he0.le) (norm_nonneg
      (cauchySquare (ξ : ℂ) (conj (z : ℂ))))]

/-- The same actual harmonic input has a quantitative comparison between
its invariant positive exclusions and its genuine radial principal value.
The constant is supplied by the original compact-surface quadratic bound. -/
theorem innerInput_ofQuadratic_invariant_truncation_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ξ z : ℍ, ∀ e : ℝ, 0 < e → e < 1 / 16 →
      ‖(-(1 / (Real.pi : ℂ)) *
          ∫ η : ℂ in {η : ℂ | e * ‖η - conj (ξ : ℂ)‖ < ‖η - (ξ : ℂ)‖},
            innerInput (fun w => (NativeHarmonicBeltrami.ofQuadratic R p hp q).val w) z η /
              (η - ξ) ^ 2) -
        hilbertHSmooth (innerInput
          (fun w => (NativeHarmonicBeltrami.ofQuadratic R p hp q).val w) z) ξ‖ ≤
          C * e * ‖cauchySquare ξ (conj (z : ℂ))‖ := by
  obtain ⟨M, hM, hb⟩ := uniformizedQuadratic_weightedBound R p hp q
  refine ⟨4096 * M, by positivity, fun ξ z e he0 he16 => ?_⟩
  have h := actual_invariant_error_bound R p hp q M hM hb ξ z he0 he16
  have hae := actual_input_ae R p hp q z
  have he : (∫ η : ℂ in {η : ℂ | e * ‖η - conj (ξ : ℂ)‖ < ‖η - (ξ : ℂ)‖},
      innerInput (fun w => (NativeHarmonicBeltrami.ofQuadratic R p hp q).val w) z η /
        (η - ξ) ^ 2) =
      ∫ η : ℂ in {η : ℂ | e * ‖η - conj (ξ : ℂ)‖ < ‖η - (ξ : ℂ)‖},
        innerInput (NativeHarmonicBeltrami.coefficient R p q) z η / (η - ξ) ^ 2 := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae hae] with η hη
    rw [hη]
  rw [he, congrFun (hilbertHSmooth_congr_ae hae) (ξ : ℂ)]
  simpa only [actualInvariantExterior, mul_assoc] using h

end LowDimensionalTopology.Geometry.Teichmuller.WeilPetersson.SourceKernel
