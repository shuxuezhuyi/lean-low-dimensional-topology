/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Hyperbolic.Models.Klein.Closed

/-! # Genuine ideal-endpoint closed segments and actual ray closures -/

@[expose] public section
open Set Filter
open scoped UpperHalfPlane OnePoint Topology Complex.UnitDisc
namespace LowDimensionalTopology.Geometry.Hyperbolic
noncomputable section

/-- The actual affine coordinate on a real line in the complex plane. -/
theorem affine_line_projection_identity {a p q x : ℂ} {t : ℝ} (ha : a ≠ 0) (hpq : p ≠ q)
    (hpA : inner ℝ a p = t) (hqA : inner ℝ a q = t) (hxA : inner ℝ a x = t) :
    x = p + (inner ℝ (q - p) (x - p) / ‖q - p‖ ^ 2) • (q - p) := by
  let := Complex.finrank_real_complex_fact
  have hd : q - p ≠ 0 := sub_ne_zero.mpr (Ne.symm hpq)
  have hdx : inner ℝ a (x - p) = 0 := by rw [inner_sub_right,hxA,hpA,sub_self]
  have hdq : inner ℝ a (q - p) = 0 := by rw [inner_sub_right,hqA,hpA,sub_self]
  obtain ⟨r,hr⟩ := Submodule.mem_span_singleton.mp
    (Submodule.mem_span_singleton_of_inner_eq_zero_of_inner_eq_zero ha hd hdx hdq)
  have he : inner ℝ (q - p) (x - p) / ‖q - p‖ ^ 2 = r := by
    rw [← hr,inner_smul_right,real_inner_self_eq_norm_sq]
    exact mul_div_cancel_right₀ r (pow_ne_zero 2 (norm_ne_zero_iff.mpr hd))
  rw [he,hr]
  abel

/-- A closed-disc point on the forward line from an interior point toward a unit
point lies in their genuine Euclidean segment. -/
theorem affine_closedDisc_forward_subset_segment {a p q : ℂ} {t : ℝ}
    (ha : a ≠ 0) (hp : ‖p‖ < 1) (hq : ‖q‖ = 1)
    (hpA : inner ℝ a p = t) (hqA : inner ℝ a q = t) :
    ({w : ℂ | inner ℝ a w = t} ∩ Metric.closedBall (0 : ℂ) 1) ∩
      {w : ℂ | 0 ≤ inner ℝ (q - p) (w - p)} ⊆ segment ℝ p q := by
  have hpq : p ≠ q := by intro he; rw [he,hq] at hp; exact lt_irrefl 1 hp
  let d := q - p
  have hd : d ≠ 0 := sub_ne_zero.mpr (Ne.symm hpq)
  have hdN : 0 < ‖d‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hd)
  have hpN : 0 < 1 - ‖p‖ ^ 2 := by
    nlinarith [mul_pos (sub_pos.mpr hp) (by positivity : 0 < 1 + ‖p‖)]
  have hpd : 2 * inner ℝ p d = 1 - ‖p‖ ^ 2 - ‖d‖ ^ 2 := by
    have he := norm_add_sq_real p d
    have heq : p + d = q := by dsimp only [d]; abel
    rw [heq,hq] at he
    nlinarith
  intro w hw
  let r := inner ℝ d (w - p) / ‖d‖ ^ 2
  have hwr : w = p + r • d := affine_line_projection_identity ha hpq hpA hqA hw.1.1
  have hr : 0 ≤ r := div_nonneg hw.2 hdN.le
  have hwNsq : ‖w‖ ^ 2 ≤ 1 := by
    have he := pow_le_pow_left₀ (norm_nonneg w) (mem_closedBall_zero_iff.mp hw.1.2) 2
    simpa only [one_pow] using he
  have hnorm : ‖w‖ ^ 2 - 1 = (r - 1) * ((1 - ‖p‖ ^ 2) + r * ‖d‖ ^ 2) := by
    rw [hwr,norm_add_sq_real,inner_smul_right,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs]
    rw [show 2 * (r * inner ℝ p d) = r * (2 * inner ℝ p d) by ring,hpd]
    ring
  have hr1 : r ≤ 1 := by
    by_contra! hgt
    have hc : 0 < (1 - ‖p‖ ^ 2) + r * ‖d‖ ^ 2 := by positivity
    have hmul := mul_pos (sub_pos.mpr hgt) hc
    linarith
  rw [segment_eq_image']
  exact ⟨r,⟨hr,hr1⟩,hwr.symm⟩

/-- A genuine continuous injective line chart in the open unit ball, whose forward
half-trace accumulates at an actual unit point, closes to exactly the expected segment. -/
theorem affine_forward_ray_closure_segment {γ : ℝ → ℂ} (hc : Continuous γ)
    (hi : Function.Injective γ) {a : ℂ} {t : ℝ} (ha : a ≠ 0)
    (hline : ∀ r, inner ℝ a (γ r) = t) (hball : ∀ r, ‖γ r‖ < 1)
    (s : ℝ) (p : ℂ) (hp : ‖p‖ = 1) (hpcl : p ∈ closure (γ '' Ici s)) :
    closure (γ '' Ici s) = segment ℝ (γ s) p := by
  let d := γ (s + 1) - γ s
  have hsd : γ s ≠ γ (s + 1) := hi.ne (by linarith)
  have hd : d ≠ 0 := sub_ne_zero.mpr (Ne.symm hsd)
  have hdN : 0 < ‖d‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hd)
  let φ : ℂ → ℝ := fun x => inner ℝ d (x - γ s) / ‖d‖ ^ 2
  have hφc : Continuous φ := (continuous_const.inner (continuous_id.sub continuous_const)).div_const _
  have hparam (x : ℂ) (hx : inner ℝ a x = t) : x = γ s + φ x • d :=
    affine_line_projection_identity ha hsd (hline s) (hline (s + 1)) hx
  have hφi : Function.Injective (φ ∘ γ) := by
    intro u v huv
    apply hi
    rw [hparam (γ u) (hline u),hparam (γ v) (hline v)]
    exact congrArg (fun r : ℝ => γ s + r • d) huv
  have hφs : φ (γ s) = 0 := by simp [φ]
  have hφs1 : φ (γ (s + 1)) = 1 := by
    change inner ℝ d d / ‖d‖ ^ 2 = 1
    rw [real_inner_self_eq_norm_sq,div_self (ne_of_gt hdN)]
  have hmono : StrictMono (φ ∘ γ) := by
    apply (hφc.comp hc).strictMonoOn_of_inj_rigidity hφi (by linarith : s < s + 1)
    apply (hφc.comp hc).continuousOn.strictMonoOn_of_injOn_Icc (by linarith : s ≤ s + 1)
    · change φ (γ s) ≤ φ (γ (s + 1))
      rw [hφs,hφs1]
      norm_num
    · exact hφi.injOn
  have hclosedA : IsClosed {x : ℂ | inner ℝ a x = t} :=
    isClosed_eq (continuous_const.inner continuous_id) continuous_const
  have hsubA : closure (γ '' Ici s) ⊆ {x : ℂ | inner ℝ a x = t} := by
    apply closure_minimal _ hclosedA
    rintro x ⟨r,_,rfl⟩
    exact hline r
  have hsubB : closure (γ '' Ici s) ⊆ Metric.closedBall (0 : ℂ) 1 := by
    apply closure_minimal _ Metric.isClosed_closedBall
    rintro x ⟨r,_,rfl⟩
    exact mem_closedBall_zero_iff.mpr (hball r).le
  have hsubP : closure (γ '' Ici s) ⊆ {x : ℂ | 0 ≤ φ x} := by
    apply closure_minimal _ (isClosed_le continuous_const hφc)
    rintro x ⟨r,hr,rfl⟩
    change 0 ≤ φ (γ r)
    simpa only [Function.comp_apply,hφs] using hmono.monotone hr
  have hφp : 0 < φ p := by
    apply lt_of_le_of_ne (hsubP hpcl)
    intro he
    have hps : p = γ s := by simpa only [← he,zero_smul,add_zero] using hparam p (hsubA hpcl)
    have hn := hball s
    rw [← hps,hp] at hn
    exact lt_irrefl 1 hn
  have hconv : Convex ℝ (closure (γ '' Ici s)) := by
    apply convex_of_preconnected_subset_affine_line
      ((isPreconnected_Ici.image γ hc.continuousOn).closure) ha
    exact fun x hx => hsubA hx
  apply subset_antisymm
  · intro x hx
    apply affine_closedDisc_forward_subset_segment ha (hball s) hp (hline s) (hsubA hpcl)
    refine ⟨⟨hsubA hx,hsubB hx⟩,?_⟩
    have hpx : p - γ s = φ p • d := by
      calc
        p - γ s = (γ s + φ p • d) - γ s := congrArg (fun u => u - γ s) (hparam p (hsubA hpcl))
        _ = φ p • d := by abel
    have hxx : x - γ s = φ x • d := by
      calc
        x - γ s = (γ s + φ x • d) - γ s := congrArg (fun u => u - γ s) (hparam x (hsubA hx))
        _ = φ x • d := by abel
    change 0 ≤ inner ℝ (p - γ s) (x - γ s)
    rw [hpx,hxx,inner_smul_left,inner_smul_right,real_inner_self_eq_norm_sq]
    exact mul_nonneg hφp.le (mul_nonneg (hsubP hx) hdN.le)
  · exact hconv.segment_subset (subset_closure (mem_image_of_mem γ (le_refl s))) hpcl

/-- The same genuine closure statement holds for the opposite chart orientation. -/
theorem affine_backward_ray_closure_segment {γ : ℝ → ℂ} (hc : Continuous γ)
    (hi : Function.Injective γ) {a : ℂ} {t : ℝ} (ha : a ≠ 0)
    (hline : ∀ r, inner ℝ a (γ r) = t) (hball : ∀ r, ‖γ r‖ < 1)
    (s : ℝ) (p : ℂ) (hp : ‖p‖ = 1) (hpcl : p ∈ closure (γ '' Iic s)) :
    closure (γ '' Iic s) = segment ℝ (γ s) p := by
  have he : (fun r : ℝ => γ (-r)) '' Ici (-s) = γ '' Iic s := by
    ext x
    constructor
    · rintro ⟨r,hr,rfl⟩
      refine ⟨-r,?_,rfl⟩
      change -s ≤ r at hr
      change -r ≤ s
      linarith
    · rintro ⟨r,hr,rfl⟩
      refine ⟨-r,?_,?_⟩
      · change r ≤ s at hr
        change -s ≤ -r
        linarith
      · simp only [neg_neg]
  have h := affine_forward_ray_closure_segment (hc.comp continuous_neg)
    (hi.comp neg_injective) ha (fun r => hline (-r)) (fun r => hball (-r)) (-s) p hp
    (he ▸ hpcl)
  change closure ((fun r : ℝ => γ (-r)) '' Ici (-s)) = segment ℝ (γ (- -s)) p at h
  simpa only [he,neg_neg] using h

theorem closedKlein_image_discClosedModelClosure (S : Set 𝔻) :
    closedKleinCoordinate '' closure (discToClosedModel '' S) = closure (kleinCoordinate '' S) := by
  rw [← isClosedEmbedding_closedKleinCoordinate.closure_image_eq,image_image]
  rfl

/-- A source segment with one genuine finite and one genuine ideal endpoint agrees
with the closure of the previously formalized actual native isometric half-line. -/
theorem closedModelDiscHSegment_ray (z : 𝔻) (p : 𝕔𝔻) (hp : ‖(p : ℂ)‖ = 1) :
    closedModelDiscHSegment (discToClosedModel z) p =
      closure (discToClosedModel '' discHRay z (closedDiscToExtended p)) := by
  have hpB : closedDiscToExtended p ∈ extendedDiscIdealBoundary :=
    (coe_mem_extendedDiscIdealBoundary (p : ℂ)).mpr hp
  have hpcl : closedDiscToExtended p ∈ closure
      (extendedDiscPoint '' discHRay z (closedDiscToExtended p)) := by
    have he := discHRay_idealEndpoints z (closedDiscToExtended p) hpB
    have hm : closedDiscToExtended p ∈ discTraceIdealEndpoints
        (discHRay z (closedDiscToExtended p)) := by rw [he]; rfl
    exact hm.1
  have hpR : p ∈ closure (discToClosedModel '' discHRay z (closedDiscToExtended p)) := by
    have hE := discClosedModelClosure_ambient (discHRay z (closedDiscToExtended p))
    change closedDiscToExtended '' closure (discToClosedModel '' discHRay z (closedDiscToExtended p)) =
      closure (extendedDiscPoint '' discHRay z (closedDiscToExtended p)) at hE
    rw [← hE] at hpcl
    obtain ⟨q,hq,he⟩ := hpcl
    exact isEmbedding_closedDiscToExtended.injective he ▸ hq
  have hpK : (p : ℂ) ∈ closure (kleinCoordinate '' discHRay z (closedDiscToExtended p)) := by
    have he : closedKleinCoordinate p = (p : ℂ) :=
      congrArg (fun x : 𝕔𝔻 => (x : ℂ)) (closedPoincareToKlein_ideal_fixed p hp)
    rw [← he,← closedKlein_image_discClosedModelClosure]
    exact mem_image_of_mem closedKleinCoordinate hpR
  obtain ⟨γ,hγ,s,hs,hor,_⟩ := isDiscHLineRay_discHRay z (closedDiscToExtended p) hpB
  let := discHyperbolicMetric
  obtain ⟨L,hL⟩ := hγ.2
  obtain ⟨a,t,ha,hA⟩ := L.exists_klein_linear_equation
  have hc : Continuous (kleinCoordinate ∘ γ) := continuous_kleinCoordinate.comp hγ.1.continuous
  have hi : Function.Injective (kleinCoordinate ∘ γ) := kleinCoordinate_injective.comp hγ.1.injective
  have hline : ∀ r : ℝ, inner ℝ a (kleinCoordinate (γ r)) = t := by
    intro r
    apply (hA _).mp
    rw [← hL]
    exact mem_range_self r
  have hball : ∀ r : ℝ, ‖kleinCoordinate (γ r)‖ < 1 := fun r => (poincareToKlein (γ r)).norm_lt_one
  apply closedKleinCoordinate_injective.image_injective
  rw [closedKlein_image_closedModelDiscHSegment,closedKlein_image_discClosedModelClosure,
    closedKleinCoordinate_disc_inclusion]
  have hpf : closedKleinCoordinate p = (p : ℂ) :=
    congrArg (fun x : 𝕔𝔻 => (x : ℂ)) (closedPoincareToKlein_ideal_fixed p hp)
  rw [hpf]
  rcases hor with hor | hor
  · rw [hor,image_image] at hpK ⊢
    simpa only [Function.comp_apply,hs] using
      (affine_forward_ray_closure_segment hc hi ha hline hball s (p : ℂ) hp hpK).symm
  · rw [hor,image_image] at hpK ⊢
    simpa only [Function.comp_apply,hs] using
      (affine_backward_ray_closure_segment hc hi ha hline hball s (p : ℂ) hp hpK).symm

/-- Actual native h-line closure in the genuine OnePoint H compactification. -/
def HalfPlaneLine.closedCarrier (L : HalfPlaneLine) : Set ClosedHalfPlaneModel :=
  closure (halfPlaneToClosedModel '' L.carrier)

theorem HalfPlaneLine.cayley_image_closedCarrier (L : HalfPlaneLine) :
    closedModelCayleyHomeomorph '' L.closedCarrier = L.toDiscLine.closedCarrier := by
  rw [HalfPlaneLine.closedCarrier,closedModelCayleyHomeomorph.image_closure,image_image,
    DiscLine.closedCarrier,HalfPlaneLine.toDiscLine_carrier,HalfPlaneLine.discCarrier_eq_cayley_image,
    image_image]
  apply congrArg closure
  apply Set.image_congr
  intro u _
  exact closedModelCayley_on_interior u

theorem closedModelCayley_ideal_norm (p : ClosedHalfPlaneModel)
    (hp : p.1 ∈ halfPlaneIdealBoundary) :
    ‖(closedModelCayleyHomeomorph p : ℂ)‖ = 1 := by
  apply (coe_mem_extendedDiscIdealBoundary _).mp
  change closedDiscToExtended (closedModelCayleyHomeomorph p) ∈ extendedDiscIdealBoundary
  rw [closedModelCayley_toExtended]
  exact (idealBoundary_cayley_iff p.1).mp hp

/-- The mixed-endpoint segment also equals the actual ray closure in the genuine
closed H model, including the true infinite ideal point. -/
theorem cayley_pullback_closed_segment_ray (z : ℍ) (p : ClosedHalfPlaneModel)
    (hp : p.1 ∈ halfPlaneIdealBoundary) :
    closedModelCayleyHomeomorph ⁻¹' closedModelDiscHSegment
      (closedModelCayleyHomeomorph (halfPlaneToClosedModel z)) (closedModelCayleyHomeomorph p) =
      closure (halfPlaneToClosedModel '' hRay z p.1) := by
  apply closedModelCayleyHomeomorph.injective.image_injective
  rw [closedModelCayleyHomeomorph.surjective.image_preimage,closedModelCayley_on_interior,
    closedModelDiscHSegment_ray _ _ (closedModelCayley_ideal_norm p hp),
    closedModelCayleyHomeomorph.image_closure]
  have hpB : closedDiscToExtended (closedModelCayleyHomeomorph p) ∈ extendedDiscIdealBoundary := by
    rw [closedModelCayley_toExtended]
    exact (idealBoundary_cayley_iff p.1).mp hp
  rw [discHRay_eq_cayley_image _ _ hpB,closedModelCayley_toExtended,
    extendedCayley.symm_apply_apply,discToHalfPlane_halfPlaneToDisc,image_image,image_image]
  apply congrArg closure
  apply Set.image_congr
  intro u _
  exact (closedModelCayley_on_interior u).symm

/-- Both actual ideal endpoints select exactly the actual complete closed H h-line. -/
theorem cayley_pullback_closed_segment_ideal_endpoints (L : HalfPlaneLine)
    (p q : ClosedHalfPlaneModel) (hp : p.1 ∈ halfPlaneIdealBoundary)
    (hq : q.1 ∈ halfPlaneIdealBoundary) (hpq : p ≠ q)
    (hpL : p ∈ L.closedCarrier) (hqL : q ∈ L.closedCarrier) :
    closedModelCayleyHomeomorph ⁻¹' closedModelDiscHSegment
      (closedModelCayleyHomeomorph p) (closedModelCayleyHomeomorph q) = L.closedCarrier := by
  apply closedModelCayleyHomeomorph.injective.image_injective
  rw [closedModelCayleyHomeomorph.surjective.image_preimage,L.cayley_image_closedCarrier]
  apply closedModelDiscHSegment_ideal_endpoints L.toDiscLine _ _
    (closedModelCayley_ideal_norm p hp) (closedModelCayley_ideal_norm q hq)
    (closedModelCayleyHomeomorph.injective.ne hpq)
  · rw [← L.cayley_image_closedCarrier]
    exact mem_image_of_mem _ hpL
  · rw [← L.cayley_image_closedCarrier]
    exact mem_image_of_mem _ hqL

end
end LowDimensionalTopology.Geometry.Hyperbolic
