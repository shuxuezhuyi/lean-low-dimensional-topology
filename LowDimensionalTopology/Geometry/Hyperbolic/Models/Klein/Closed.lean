/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Hyperbolic.Convexity.HorocyclicRegions

/-!
# Actual closed Klein model and boundary-compatible coordinates
-/

@[expose] public section
open Set Filter
open scoped UpperHalfPlane MatrixGroups OnePoint Topology ComplexConjugate Complex.UnitDisc
namespace LowDimensionalTopology.Geometry.Hyperbolic
noncomputable section

theorem kleinFormula_mem_closedDisc (z : 𝕔𝔻) : ‖kleinFormula z‖ ≤ 1 := by
  rw [kleinFormula_norm]
  apply (div_le_one (by positivity : 0 < 1 + ‖(z : ℂ)‖ ^ 2)).mpr
  nlinarith [sq_nonneg (1 - ‖(z : ℂ)‖)]

def closedPoincareToKlein (z : 𝕔𝔻) : 𝕔𝔻 :=
  Complex.UnitClosedDisc.mk (kleinFormula z) (kleinFormula_mem_closedDisc z)

theorem inverseKleinFormula_mem_closedDisc (z : 𝕔𝔻) : ‖inverseKleinFormula z‖ ≤ 1 := by
  rw [inverseKleinFormula_norm]
  apply (div_le_one (by positivity : 0 < 1 + Real.sqrt (1 - ‖(z : ℂ)‖ ^ 2))).mpr
  linarith [z.norm_le_one,Real.sqrt_nonneg (1 - ‖(z : ℂ)‖ ^ 2)]

def closedKleinToPoincare (z : 𝕔𝔻) : 𝕔𝔻 :=
  Complex.UnitClosedDisc.mk (inverseKleinFormula z) (inverseKleinFormula_mem_closedDisc z)

theorem closed_klein_sqrt_identity (z : 𝕔𝔻) :
    Real.sqrt (1 - ‖kleinFormula z‖ ^ 2) = (1 - ‖(z : ℂ)‖ ^ 2) / (1 + ‖(z : ℂ)‖ ^ 2) := by
  have hpos : 0 ≤ 1 - ‖(z : ℂ)‖ ^ 2 := sub_nonneg.mpr z.sq_norm_lt_one
  have hden : 0 < 1 + ‖(z : ℂ)‖ ^ 2 := by positivity
  have hrad : 0 ≤ 1 - ‖kleinFormula z‖ ^ 2 := by
    nlinarith [kleinFormula_mem_closedDisc z,norm_nonneg (kleinFormula z)]
  apply (sq_eq_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
  rw [Real.sq_sqrt hrad,kleinFormula_norm]
  field_simp
  ring

theorem closedKleinToPoincare_closedPoincareToKlein (z : 𝕔𝔻) :
    closedKleinToPoincare (closedPoincareToKlein z) = z := by
  apply Complex.UnitClosedDisc.coe_injective
  change inverseKleinFormula (kleinFormula z) = (z : ℂ)
  rw [inverseKleinFormula,closed_klein_sqrt_identity]
  have he : 1 / (1 + (1 - ‖(z : ℂ)‖ ^ 2) / (1 + ‖(z : ℂ)‖ ^ 2)) *
      (2 / (1 + ‖(z : ℂ)‖ ^ 2)) = 1 := by
    field_simp
    ring
  rw [kleinFormula,← mul_assoc,← Complex.ofReal_mul,he,Complex.ofReal_one,one_mul]

theorem closedPoincareToKlein_closedKleinToPoincare (z : 𝕔𝔻) :
    closedPoincareToKlein (closedKleinToPoincare z) = z := by
  apply Complex.UnitClosedDisc.coe_injective
  change kleinFormula (inverseKleinFormula z) = (z : ℂ)
  rw [kleinFormula,inverseKleinFormula_norm]
  have hs : Real.sqrt (1 - ‖(z : ℂ)‖ ^ 2) ^ 2 = 1 - ‖(z : ℂ)‖ ^ 2 :=
    Real.sq_sqrt (sub_nonneg.mpr z.sq_norm_lt_one)
  have hden : 1 + Real.sqrt (1 - ‖(z : ℂ)‖ ^ 2) ≠ 0 := by positivity
  have he : 2 / (1 + (‖(z : ℂ)‖ / (1 + Real.sqrt (1 - ‖(z : ℂ)‖ ^ 2))) ^ 2) *
      (1 / (1 + Real.sqrt (1 - ‖(z : ℂ)‖ ^ 2))) = 1 := by
    apply (div_mul_eq_mul_div _ _ _).trans ?_
    apply (div_eq_one_iff_eq (by positivity)).mpr
    field_simp
    nlinarith
  unfold inverseKleinFormula
  rw [← mul_assoc,← Complex.ofReal_mul,he,Complex.ofReal_one,one_mul]

theorem continuous_closedPoincareToKlein : Continuous closedPoincareToKlein := by
  apply Complex.UnitClosedDisc.isEmbedding_coe.continuous_iff.mpr
  change Continuous (fun z : 𝕔𝔻 => kleinFormula z)
  have hn : Continuous (fun z : 𝕔𝔻 => ‖(z : ℂ)‖ ^ 2) :=
    (continuous_norm.comp Complex.UnitClosedDisc.continuous_coe).pow 2
  have hs : Continuous (fun z : 𝕔𝔻 => (2 : ℝ) / (1 + ‖(z : ℂ)‖ ^ 2)) :=
    continuous_const.div (continuous_const.add hn) (fun _ => by positivity)
  exact (Complex.continuous_ofReal.comp hs).mul Complex.UnitClosedDisc.continuous_coe

theorem continuous_closedKleinToPoincare : Continuous closedKleinToPoincare := by
  apply Complex.UnitClosedDisc.isEmbedding_coe.continuous_iff.mpr
  change Continuous (fun z : 𝕔𝔻 => inverseKleinFormula z)
  have hn : Continuous (fun z : 𝕔𝔻 => ‖(z : ℂ)‖ ^ 2) :=
    (continuous_norm.comp Complex.UnitClosedDisc.continuous_coe).pow 2
  have hs : Continuous (fun z : 𝕔𝔻 => (1 : ℝ) / (1 + Real.sqrt (1 - ‖(z : ℂ)‖ ^ 2))) :=
    continuous_const.div (continuous_const.add ((continuous_const.sub hn).sqrt)) (fun _ => by positivity)
  exact (Complex.continuous_ofReal.comp hs).mul Complex.UnitClosedDisc.continuous_coe

/-- Actual Klein coordinates extend continuously to the genuine closed disc and fix its ideal circle. -/
def closedKleinHomeomorph : 𝕔𝔻 ≃ₜ 𝕔𝔻 where
  toFun := closedPoincareToKlein
  invFun := closedKleinToPoincare
  left_inv := closedKleinToPoincare_closedPoincareToKlein
  right_inv := closedPoincareToKlein_closedKleinToPoincare
  continuous_toFun := continuous_closedPoincareToKlein
  continuous_invFun := continuous_closedKleinToPoincare

theorem closedPoincareToKlein_ideal_fixed (z : 𝕔𝔻) (hz : ‖(z : ℂ)‖ = 1) :
    closedPoincareToKlein z = z := by
  apply Complex.UnitClosedDisc.coe_injective
  change kleinFormula z = (z : ℂ)
  norm_num [kleinFormula,hz]

theorem closedPoincareToKlein_disc_inclusion (z : 𝔻) :
    closedPoincareToKlein (discToClosedModel z) = discToClosedModel (poincareToKlein z) := rfl

/-- The actual complex coordinate of the genuine compact closed Klein model. -/
def closedKleinCoordinate (z : 𝕔𝔻) : ℂ := (closedPoincareToKlein z : ℂ)

theorem closedKleinCoordinate_disc_inclusion (z : 𝔻) :
    closedKleinCoordinate (discToClosedModel z) = kleinCoordinate z := rfl

theorem isClosedEmbedding_closedKleinCoordinate : Topology.IsClosedEmbedding closedKleinCoordinate := by
  have he : Topology.IsEmbedding closedKleinCoordinate :=
    Complex.UnitClosedDisc.isEmbedding_coe.comp closedKleinHomeomorph.isEmbedding
  exact he.continuous.isClosedEmbedding he.injective

/-- The closed H model here is the actual OnePoint closure including its genuine infinite ideal point. -/
def closedHalfPlaneKleinHomeomorph : ClosedHalfPlaneModel ≃ₜ 𝕔𝔻 :=
  closedModelCayleyHomeomorph.trans closedKleinHomeomorph

theorem closedKleinCoordinate_injective : Function.Injective closedKleinCoordinate :=
  isClosedEmbedding_closedKleinCoordinate.injective

theorem range_closedKleinCoordinate : range closedKleinCoordinate = Metric.closedBall (0 : ℂ) 1 := by
  ext z
  constructor
  · rintro ⟨w,rfl⟩
    exact mem_closedBall_zero_iff.mpr (closedPoincareToKlein w).norm_le_one
  · intro hz
    let w := Complex.UnitClosedDisc.mk z (mem_closedBall_zero_iff.mp hz)
    refine ⟨closedKleinToPoincare w,?_⟩
    change (closedPoincareToKlein (closedKleinToPoincare w) : ℂ) = z
    rw [closedPoincareToKlein_closedKleinToPoincare]
    rfl

/-- This carrier is the actual closure of the genuine native Euclidean h-line arc. -/
def DiscLine.closedCarrier (L : DiscLine) : Set 𝕔𝔻 := closure (discToClosedModel '' L.carrier)

theorem DiscLine.closedCarrier_ambient (L : DiscLine) :
    closedDiscToExtended '' L.closedCarrier = closure (extendedDiscPoint '' L.carrier) := by
  exact discClosedModelClosure_ambient L.carrier

theorem DiscLine.klein_image_carrier (L : DiscLine) :
    ∃ (a : ℂ) (t : ℝ), a ≠ 0 ∧
      kleinCoordinate '' L.carrier = {w : ℂ | inner ℝ a w = t} ∩ Metric.ball (0 : ℂ) 1 := by
  obtain ⟨a,t,ha,hL⟩ := L.exists_klein_linear_equation
  refine ⟨a,t,ha,?_⟩
  have he : L.carrier = kleinCoordinate ⁻¹' {w : ℂ | inner ℝ a w = t} := by
    ext z
    exact hL z
  rw [he,image_preimage_eq_inter_range,range_kleinCoordinate]

/-- Closing a genuine affine slice through an interior disc point gives exactly its closed chord. -/
theorem closure_affine_slice_unitBall (a : ℂ) (t : ℝ)
    (hne : ({w : ℂ | inner ℝ a w = t} ∩ Metric.ball (0 : ℂ) 1).Nonempty) :
    closure ({w : ℂ | inner ℝ a w = t} ∩ Metric.ball (0 : ℂ) 1) =
      {w : ℂ | inner ℝ a w = t} ∩ Metric.closedBall (0 : ℂ) 1 := by
  let A : Set ℂ := {w | inner ℝ a w = t}
  have hA : Convex ℝ A := convex_hyperplane (innerSL ℝ a).toLinearMap.isLinear t
  have hAc : IsClosed A := isClosed_eq (innerSL ℝ a).continuous continuous_const
  apply subset_antisymm
  · apply closure_minimal
    · exact inter_subset_inter_right _ (Metric.ball_subset_closedBall (x := (0 : ℂ)) (ε := 1))
    · exact hAc.inter Metric.isClosed_closedBall
  · intro x hx
    obtain ⟨y,hyA,hyB⟩ := hne
    have hxcl : x ∈ closure (Metric.ball (0 : ℂ) 1) := by
      rw [closure_ball (0 : ℂ) one_ne_zero]
      exact hx.2
    have hyint : y ∈ interior (Metric.ball (0 : ℂ) 1) := by
      rw [Metric.isOpen_ball.interior_eq]
      exact hyB
    have hb := (convex_ball (0 : ℂ) 1).openSegment_interior_closure_subset_interior hyint hxcl
    have hs : openSegment ℝ y x ⊆ A ∩ Metric.ball (0 : ℂ) 1 := by
      intro u hu
      exact ⟨hA.segment_subset hyA hx.1 (openSegment_subset_segment ℝ y x hu),interior_subset (hb hu)⟩
    exact closure_mono hs (segment_subset_closure_openSegment (right_mem_segment ℝ y x))

/-- The closure is transported by the actual compact-model embedding. -/
theorem DiscLine.closedKlein_image_closedCarrier (L : DiscLine) :
    closedKleinCoordinate '' L.closedCarrier = closure (kleinCoordinate '' L.carrier) := by
  rw [DiscLine.closedCarrier,← isClosedEmbedding_closedKleinCoordinate.closure_image_eq,image_image]
  have he : (fun z : 𝔻 => closedKleinCoordinate (discToClosedModel z)) = kleinCoordinate := by
    funext z
    exact closedKleinCoordinate_disc_inclusion z
  rw [he]

/-- Actual closed native h-line arcs, including their genuine two ideal endpoints, become closed chords. -/
theorem DiscLine.exists_closedKlein_affine_chord (L : DiscLine) :
    ∃ (a : ℂ) (t : ℝ), a ≠ 0 ∧
      closedKleinCoordinate '' L.closedCarrier =
        {w : ℂ | inner ℝ a w = t} ∩ Metric.closedBall (0 : ℂ) 1 := by
  obtain ⟨a,t,ha,hL⟩ := L.klein_image_carrier
  refine ⟨a,t,ha,?_⟩
  rw [L.closedKlein_image_closedCarrier,hL]
  apply closure_affine_slice_unitBall
  obtain ⟨z,w,hz,_,_⟩ := L.toHalfPlane.exists_two_points
  have hzD : halfPlaneToDisc z ∈ L.carrier := by
    apply (L.mem_carrier _).mpr
    rw [discToHalfPlane_halfPlaneToDisc]
    exact hz
  rw [← hL]
  exact ⟨kleinCoordinate (halfPlaneToDisc z),mem_image_of_mem kleinCoordinate hzD⟩

theorem DiscLine.closedCarrier_isPreconnected (L : DiscLine) : IsPreconnected L.closedCarrier := by
  obtain ⟨a,t,_,he⟩ := L.exists_closedKlein_affine_chord
  apply isClosedEmbedding_closedKleinCoordinate.isEmbedding.isInducing.isPreconnected_image.mp
  rw [he]
  exact ((convex_hyperplane (innerSL ℝ a).toLinearMap.isLinear t).inter
    (convex_closedBall (0 : ℂ) 1)).isPreconnected

theorem DiscLine.closedCarrier_isCompact (L : DiscLine) : IsCompact L.closedCarrier :=
  isClosed_closure.isCompact

theorem DiscLine.closedCarrier_mem_iff_ambient (L : DiscLine) (p : 𝕔𝔻) :
    p ∈ L.closedCarrier ↔ closedDiscToExtended p ∈ closure (extendedDiscPoint '' L.carrier) := by
  rw [← L.closedCarrier_ambient]
  constructor
  · exact mem_image_of_mem closedDiscToExtended
  · rintro ⟨q,hq,he⟩
    exact isEmbedding_closedDiscToExtended.injective he ▸ hq

theorem DiscLine.closedCarrier_mem_ideal_iff (L : DiscLine) (p : 𝕔𝔻) (hp : ‖(p : ℂ)‖ = 1) :
    p ∈ L.closedCarrier ↔ closedDiscToExtended p ∈ L.idealEndpoints := by
  rw [L.closedCarrier_mem_iff_ambient]
  have hb : closedDiscToExtended p ∈ extendedDiscIdealBoundary := by
    change ((p : ℂ) : OnePoint ℂ) ∈ extendedDiscIdealBoundary
    exact (coe_mem_extendedDiscIdealBoundary (p : ℂ)).mpr hp
  exact ⟨fun h => ⟨h,hb⟩,fun h => h.1⟩

/-- A preconnected subset of a genuine real affine line in the complex plane is convex. -/
theorem convex_of_preconnected_subset_affine_line {S : Set ℂ} (hS : IsPreconnected S)
    {a : ℂ} {t : ℝ} (ha : a ≠ 0) (hline : ∀ z ∈ S, inner ℝ a z = t) : Convex ℝ S := by
  let := Complex.finrank_real_complex_fact
  apply convex_iff_segment_subset.mpr
  intro p hp q hq
  by_cases hpq : p = q
  · subst q
    simpa only [segment_same, singleton_subset_iff] using hp
  let d := q - p
  have hd : d ≠ 0 := sub_ne_zero.mpr (Ne.symm hpq)
  have hdN : ‖d‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hd)
  let φ : ℂ → ℝ := fun w => inner ℝ d (w - p) / ‖d‖ ^ 2
  have hφc : Continuous φ := (continuous_const.inner (continuous_id.sub continuous_const)).div_const _
  have hparam (w : ℂ) (hw : w ∈ S) : w = p + φ w • d := by
    have hu : inner ℝ a (w - p) = 0 := by
      rw [inner_sub_right,hline w hw,hline p hp,sub_self]
    have hdt : inner ℝ a d = 0 := by
      change inner ℝ a (q - p) = 0
      rw [inner_sub_right,hline q hq,hline p hp,sub_self]
    obtain ⟨r,hr⟩ := Submodule.mem_span_singleton.mp
      (Submodule.mem_span_singleton_of_inner_eq_zero_of_inner_eq_zero ha hd hu hdt)
    have hφ : φ w = r := by
      change inner ℝ d (w - p) / ‖d‖ ^ 2 = r
      rw [← hr,inner_smul_right,real_inner_self_eq_norm_sq]
      exact mul_div_cancel_right₀ r hdN
    rw [hφ,hr]
    abel
  have hφp : φ p = 0 := by simp [φ]
  have hφq : φ q = 1 := by
    change inner ℝ d d / ‖d‖ ^ 2 = 1
    rw [real_inner_self_eq_norm_sq,div_self hdN]
  have hI : Icc (0 : ℝ) 1 ⊆ φ '' S := (hS.image φ hφc.continuousOn).ordConnected.out
    (hφp ▸ mem_image_of_mem φ hp) (hφq ▸ mem_image_of_mem φ hq)
  rw [segment_eq_image']
  rintro w ⟨r,hr,rfl⟩
  obtain ⟨u,hu,hur⟩ := hI hr
  have he : u = p + r • (q - p) := by simpa only [hur] using hparam u hu
  change p + r • (q - p) ∈ S
  rw [← he]
  exact hu

/-- The intrinsic closed arc between two points is the intersection of all connected
subarcs of the actual closed native h-line containing them. -/
def DiscLine.closedArcHull (L : DiscLine) (p q : 𝕔𝔻) : Set 𝕔𝔻 :=
  {x | ∀ T : Set 𝕔𝔻, IsPreconnected T → T ⊆ L.closedCarrier → p ∈ T → q ∈ T → x ∈ T}

/-- The intrinsic arc, defined on the actual circle/diameter closure, has the expected
Euclidean chord segment in the genuine compact Klein model. -/
theorem DiscLine.closedKlein_image_closedArcHull (L : DiscLine) (p q : 𝕔𝔻)
    (hp : p ∈ L.closedCarrier) (hq : q ∈ L.closedCarrier) :
    closedKleinCoordinate '' L.closedArcHull p q =
      segment ℝ (closedKleinCoordinate p) (closedKleinCoordinate q) := by
  obtain ⟨a,t,ha,hL⟩ := L.exists_closedKlein_affine_chord
  let C := closedKleinCoordinate
  let J := segment ℝ (C p) (C q)
  have hC : Function.Injective C := closedKleinCoordinate_injective
  have hpC : C p ∈ {w : ℂ | inner ℝ a w = t} ∩ Metric.closedBall (0 : ℂ) 1 :=
    hL ▸ mem_image_of_mem C hp
  have hqC : C q ∈ {w : ℂ | inner ℝ a w = t} ∩ Metric.closedBall (0 : ℂ) 1 :=
    hL ▸ mem_image_of_mem C hq
  have hJ : J ⊆ C '' L.closedCarrier := by
    rw [hL]
    exact ((convex_hyperplane (innerSL ℝ a).toLinearMap.isLinear t).inter
      (convex_closedBall (0 : ℂ) 1)).segment_subset hpC hqC
  have him : C '' (C ⁻¹' J) = J := image_preimage_eq_of_subset (hJ.trans (image_subset_range C _))
  have hTconn : IsPreconnected (C ⁻¹' J) := by
    apply isClosedEmbedding_closedKleinCoordinate.isEmbedding.isInducing.isPreconnected_image.mp
    rw [him]
    exact (convex_segment (C p) (C q)).isPreconnected
  have hTsub : C ⁻¹' J ⊆ L.closedCarrier := by
    intro x hx
    obtain ⟨y,hy,he⟩ := hJ hx
    exact hC he ▸ hy
  apply subset_antisymm
  · rintro w ⟨x,hx,rfl⟩
    exact hx _ hTconn hTsub (left_mem_segment ℝ (C p) (C q)) (right_mem_segment ℝ (C p) (C q))
  · intro w hw
    obtain ⟨x,hx,hxw⟩ := hJ hw
    refine ⟨x,?_,hxw⟩
    intro T hTc hTL hpT hqT
    have hconv : Convex ℝ (C '' T) := by
      apply convex_of_preconnected_subset_affine_line
        (hTc.image C isClosedEmbedding_closedKleinCoordinate.continuous.continuousOn) ha
      rintro u ⟨v,hv,rfl⟩
      exact ((hL ▸ mem_image_of_mem C (hTL hv)) : C v ∈
        {w : ℂ | inner ℝ a w = t} ∩ Metric.closedBall (0 : ℂ) 1).1
    obtain ⟨y,hy,he⟩ := hconv.segment_subset (mem_image_of_mem C hpT) (mem_image_of_mem C hqT) hw
    exact hC (he.trans hxw.symm) ▸ hy

theorem DiscLine.isClosed_carrier (L : DiscLine) : IsClosed L.carrier := by
  obtain ⟨a,t,_,hL⟩ := L.exists_klein_linear_equation
  have he : L.carrier = {z : 𝔻 | inner ℝ a (kleinCoordinate z) = t} := by
    ext z
    exact hL z
  rw [he]
  exact isClosed_eq (continuous_const.inner continuous_kleinCoordinate) continuous_const

theorem DiscLine.closedCarrier_mem_interior_iff (L : DiscLine) (z : 𝔻) :
    discToClosedModel z ∈ L.closedCarrier ↔ z ∈ L.carrier := by
  change z ∈ discToClosedModel ⁻¹' closure (discToClosedModel '' L.carrier) ↔ z ∈ L.carrier
  rw [← isEmbedding_discToClosedModel.closure_eq_preimage_closure_image L.carrier,
    L.isClosed_carrier.closure_eq]

theorem closedDisc_interior_or_ideal (p : 𝕔𝔻) :
    (∃ z : 𝔻, discToClosedModel z = p) ∨ ‖(p : ℂ)‖ = 1 := by
  by_cases hp : ‖(p : ℂ)‖ < 1
  · left
    refine ⟨Complex.UnitDisc.mk (p : ℂ) hp,?_⟩
    exact Complex.UnitClosedDisc.coe_injective rfl
  · exact Or.inr (le_antisymm p.norm_le_one (not_lt.mp hp))

theorem DiscLine.idealEndpoints_eq_pair_of_closedCarrier (L : DiscLine) (p q : 𝕔𝔻)
    (hp : ‖(p : ℂ)‖ = 1) (hq : ‖(q : ℂ)‖ = 1) (hpq : p ≠ q)
    (hpL : p ∈ L.closedCarrier) (hqL : q ∈ L.closedCarrier) :
    L.idealEndpoints = {closedDiscToExtended p,closedDiscToExtended q} := by
  have hpa := (L.closedCarrier_mem_ideal_iff p hp).mp hpL
  have hqa := (L.closedCarrier_mem_ideal_iff q hq).mp hqL
  have hab := isEmbedding_closedDiscToExtended.injective.ne hpq
  obtain ⟨a,b,_,_,_,he⟩ := L.exists_idealEndpoints_pair
  rw [he] at hpa hqa ⊢
  simp only [mem_insert_iff,mem_singleton_iff] at hpa hqa
  rcases hpa with hpa | hpa <;> rcases hqa with hqa | hqa
  · exact (hab (hpa.trans hqa.symm)).elim
  · rw [hpa,hqa]
  · rw [hpa,hqa,pair_comm]
  · exact (hab (hpa.trans hqa.symm)).elim

/-- Every two distinct genuine closed-model points, including any combination of ideal
endpoints, lie on one and only one actual Euclidean disc h-line closure. -/
theorem existsUnique_discLine_closedCarrier (p q : 𝕔𝔻) (hpq : p ≠ q) :
    ∃! L : DiscLine, p ∈ L.closedCarrier ∧ q ∈ L.closedCarrier := by
  rcases closedDisc_interior_or_ideal p with ⟨z,rfl⟩ | hp
  · rcases closedDisc_interior_or_ideal q with ⟨w,rfl⟩ | hq
    · have hzw : z ≠ w := fun h => hpq (congrArg discToClosedModel h)
      obtain ⟨L,⟨hz,hw⟩,huniq⟩ := existsUnique_discLine_through z w hzw
      refine ⟨L,⟨(L.closedCarrier_mem_interior_iff z).mpr hz,
        (L.closedCarrier_mem_interior_iff w).mpr hw⟩,?_⟩
      intro M hM
      exact huniq M ⟨(M.closedCarrier_mem_interior_iff z).mp hM.1,
        (M.closedCarrier_mem_interior_iff w).mp hM.2⟩
    · have hqB : closedDiscToExtended q ∈ extendedDiscIdealBoundary :=
        (coe_mem_extendedDiscIdealBoundary (q : ℂ)).mpr hq
      obtain ⟨L,⟨hz,hqa⟩,huniq⟩ :=
        existsUnique_discLine_through_point_and_idealEndpoint z (closedDiscToExtended q) hqB
      refine ⟨L,⟨(L.closedCarrier_mem_interior_iff z).mpr hz,
        (L.closedCarrier_mem_ideal_iff q hq).mpr hqa⟩,?_⟩
      intro M hM
      exact huniq M ⟨(M.closedCarrier_mem_interior_iff z).mp hM.1,
        (M.closedCarrier_mem_ideal_iff q hq).mp hM.2⟩
  · rcases closedDisc_interior_or_ideal q with ⟨w,rfl⟩ | hq
    · have hpB : closedDiscToExtended p ∈ extendedDiscIdealBoundary :=
        (coe_mem_extendedDiscIdealBoundary (p : ℂ)).mpr hp
      obtain ⟨L,⟨hw,hpa⟩,huniq⟩ :=
        existsUnique_discLine_through_point_and_idealEndpoint w (closedDiscToExtended p) hpB
      refine ⟨L,⟨(L.closedCarrier_mem_ideal_iff p hp).mpr hpa,
        (L.closedCarrier_mem_interior_iff w).mpr hw⟩,?_⟩
      intro M hM
      exact huniq M ⟨(M.closedCarrier_mem_interior_iff w).mp hM.2,
        (M.closedCarrier_mem_ideal_iff p hp).mp hM.1⟩
    · have hpB : closedDiscToExtended p ∈ extendedDiscIdealBoundary :=
        (coe_mem_extendedDiscIdealBoundary (p : ℂ)).mpr hp
      have hqB : closedDiscToExtended q ∈ extendedDiscIdealBoundary :=
        (coe_mem_extendedDiscIdealBoundary (q : ℂ)).mpr hq
      obtain ⟨L,hL,huniq⟩ := existsUnique_discLine_of_idealEndpoints
        (closedDiscToExtended p) (closedDiscToExtended q) hpB hqB
        (isEmbedding_closedDiscToExtended.injective.ne hpq)
      have hpL : closedDiscToExtended p ∈ L.idealEndpoints := by rw [hL]; simp only [mem_insert_iff, true_or]
      have hqL : closedDiscToExtended q ∈ L.idealEndpoints := by rw [hL]; simp only [mem_insert_iff, mem_singleton_iff, or_true]
      refine ⟨L,⟨(L.closedCarrier_mem_ideal_iff p hp).mpr hpL,
        (L.closedCarrier_mem_ideal_iff q hq).mpr hqL⟩,?_⟩
      intro M hM
      exact huniq M (M.idealEndpoints_eq_pair_of_closedCarrier p q hp hq hpq hM.1 hM.2)

/-- Genuine compactified hyperbolic segment: the intrinsic arc in the unique actual
circle/diameter closure, with the singleton convention for coincident endpoints. -/
def closedModelDiscHSegment (p q : 𝕔𝔻) : Set 𝕔𝔻 := by
  classical
  exact if p = q then {p} else {x | ∃ L : DiscLine,
    p ∈ L.closedCarrier ∧ q ∈ L.closedCarrier ∧ x ∈ L.closedArcHull p q}

theorem closedModelDiscHSegment_self (p : 𝕔𝔻) : closedModelDiscHSegment p p = {p} := by
  simp [closedModelDiscHSegment]

theorem closedModelDiscHSegment_eq_arcHull (L : DiscLine) (p q : 𝕔𝔻) (hpq : p ≠ q)
    (hp : p ∈ L.closedCarrier) (hq : q ∈ L.closedCarrier) :
    closedModelDiscHSegment p q = L.closedArcHull p q := by
  obtain ⟨M,hM,huniq⟩ := existsUnique_discLine_closedCarrier p q hpq
  have hLM : L = M := huniq L ⟨hp,hq⟩
  simp only [closedModelDiscHSegment,ite_eq_right hpq]
  ext x
  constructor
  · rintro ⟨N,hpN,hqN,hx⟩
    have hNL : N = L := (huniq N ⟨hpN,hqN⟩).trans hLM.symm
    exact hNL ▸ hx
  · intro hx
    exact ⟨L,hp,hq,hx⟩

/-- Compactification and actual hyperbolic arcs agree with the ordinary Euclidean
segments of their actual Klein coordinates, even at both ideal endpoints. -/
theorem closedKlein_image_closedModelDiscHSegment (p q : 𝕔𝔻) :
    closedKleinCoordinate '' closedModelDiscHSegment p q =
      segment ℝ (closedKleinCoordinate p) (closedKleinCoordinate q) := by
  by_cases hpq : p = q
  · subst q
    rw [closedModelDiscHSegment_self,image_singleton,segment_same]
  · obtain ⟨L,⟨hp,hq⟩,_⟩ := existsUnique_discLine_closedCarrier p q hpq
    rw [closedModelDiscHSegment_eq_arcHull L p q hpq hp hq]
    exact L.closedKlein_image_closedArcHull p q hp hq

/-- The compactified definition restricts to the already formalized actual finite h-segment. -/
theorem closedModelDiscHSegment_interior (z w : 𝔻) :
    closedModelDiscHSegment (discToClosedModel z) (discToClosedModel w) =
      discToClosedModel '' closedDiscHSegment z w := by
  apply closedKleinCoordinate_injective.image_injective
  rw [closedKlein_image_closedModelDiscHSegment,image_image]
  change segment ℝ (kleinCoordinate z) (kleinCoordinate w) =
    kleinCoordinate '' closedDiscHSegment z w
  exact (klein_image_closedDiscHSegment z w).symm

/-- In a real affine line, every closed-disc point lies between any two distinct unit-circle
points on that line. This supplies the two-ideal-endpoint case without a boundary convention. -/
theorem affine_closedDisc_subset_segment_unit_endpoints {a p q : ℂ} {t : ℝ}
    (ha : a ≠ 0) (hpq : p ≠ q) (hp : ‖p‖ = 1) (hq : ‖q‖ = 1)
    (hpA : inner ℝ a p = t) (hqA : inner ℝ a q = t) :
    {w : ℂ | inner ℝ a w = t} ∩ Metric.closedBall (0 : ℂ) 1 ⊆ segment ℝ p q := by
  let := Complex.finrank_real_complex_fact
  let d := q - p
  have hd : d ≠ 0 := sub_ne_zero.mpr (Ne.symm hpq)
  have hdN : 0 < ‖d‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hd)
  have hdt : inner ℝ a d = 0 := by
    change inner ℝ a (q - p) = 0
    rw [inner_sub_right,hqA,hpA,sub_self]
  have hpd : 2 * inner ℝ p d = -‖d‖ ^ 2 := by
    have he := norm_add_sq_real p d
    have heq : p + d = q := by dsimp only [d]; abel
    rw [heq,hp,hq] at he
    nlinarith
  intro w hw
  have hwa : inner ℝ a (w - p) = 0 := by
    rw [inner_sub_right,hw.1,hpA,sub_self]
  obtain ⟨r,hr⟩ := Submodule.mem_span_singleton.mp
    (Submodule.mem_span_singleton_of_inner_eq_zero_of_inner_eq_zero ha hd hwa hdt)
  have hwr : w = p + r • d := by rw [hr]; abel
  have hnorm : ‖w‖ ^ 2 = 1 + r * (r - 1) * ‖d‖ ^ 2 := by
    rw [hwr,norm_add_sq_real,hp,inner_smul_right,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs]
    rw [show 2 * (r * inner ℝ p d) = r * (2 * inner ℝ p d) by ring,hpd]
    ring
  have hwN : ‖w‖ ≤ 1 := mem_closedBall_zero_iff.mp hw.2
  have hwNsq : ‖w‖ ^ 2 ≤ 1 := by
    have he := pow_le_pow_left₀ (norm_nonneg w) hwN 2
    simpa only [one_pow] using he
  have hprod : r * (r - 1) ≤ 0 := by
    apply nonpos_of_mul_nonpos_left (b := ‖d‖ ^ 2) _ hdN
    nlinarith only [hnorm,hwNsq]
  have hrI : r ∈ Icc (0 : ℝ) 1 := by
    constructor <;> nlinarith [sq_nonneg r,sq_nonneg (r - 1)]
  rw [segment_eq_image']
  exact ⟨r,hrI,hwr.symm⟩

/-- The segment between two distinct actual ideal endpoints is exactly the whole actual
closed geodesic, including both ideal endpoints. -/
theorem closedModelDiscHSegment_ideal_endpoints (L : DiscLine) (p q : 𝕔𝔻)
    (hp : ‖(p : ℂ)‖ = 1) (hq : ‖(q : ℂ)‖ = 1) (hpq : p ≠ q)
    (hpL : p ∈ L.closedCarrier) (hqL : q ∈ L.closedCarrier) :
    closedModelDiscHSegment p q = L.closedCarrier := by
  apply closedKleinCoordinate_injective.image_injective
  rw [closedKlein_image_closedModelDiscHSegment]
  obtain ⟨a,t,ha,hL⟩ := L.exists_closedKlein_affine_chord
  rw [hL]
  have hpf : closedKleinCoordinate p = (p : ℂ) :=
    congrArg (fun z : 𝕔𝔻 => (z : ℂ)) (closedPoincareToKlein_ideal_fixed p hp)
  have hqf : closedKleinCoordinate q = (q : ℂ) :=
    congrArg (fun z : 𝕔𝔻 => (z : ℂ)) (closedPoincareToKlein_ideal_fixed q hq)
  have hpA : inner ℝ a (closedKleinCoordinate p) = t :=
    ((hL ▸ mem_image_of_mem closedKleinCoordinate hpL) :
      closedKleinCoordinate p ∈ {w : ℂ | inner ℝ a w = t} ∩ Metric.closedBall (0 : ℂ) 1).1
  have hqA : inner ℝ a (closedKleinCoordinate q) = t :=
    ((hL ▸ mem_image_of_mem closedKleinCoordinate hqL) :
      closedKleinCoordinate q ∈ {w : ℂ | inner ℝ a w = t} ∩ Metric.closedBall (0 : ℂ) 1).1
  apply subset_antisymm
  · exact ((convex_hyperplane (innerSL ℝ a).toLinearMap.isLinear t).inter
      (convex_closedBall (0 : ℂ) 1)).segment_subset
        ⟨hpA,mem_closedBall_zero_iff.mpr (closedPoincareToKlein p).norm_le_one⟩
        ⟨hqA,mem_closedBall_zero_iff.mpr (closedPoincareToKlein q).norm_le_one⟩
  · exact affine_closedDisc_subset_segment_unit_endpoints ha
      (closedKleinCoordinate_injective.ne hpq) (hpf ▸ hp) (hqf ▸ hq) hpA hqA

/-- Convexity in the genuine compactification uses its actual finite or ideal-endpoint
hyperbolic arcs, rather than taking Euclidean-coordinate convexity as the definition. -/
def ClosedDiscHConvex (S : Set 𝕔𝔻) : Prop :=
  ∀ p ∈ S, ∀ q ∈ S, closedModelDiscHSegment p q ⊆ S

theorem closedDiscHConvex_iff_klein_convex (S : Set 𝕔𝔻) :
    ClosedDiscHConvex S ↔ Convex ℝ (closedKleinCoordinate '' S) := by
  rw [convex_iff_segment_subset]
  constructor
  · intro hS p hp q hq
    obtain ⟨x,hx,rfl⟩ := hp
    obtain ⟨y,hy,rfl⟩ := hq
    rw [← closedKlein_image_closedModelDiscHSegment]
    exact image_mono (hS x hx y hy)
  · intro hS p hp q hq x hx
    have hK : closedKleinCoordinate x ∈ closedKleinCoordinate '' S :=
      hS (mem_image_of_mem _ hp) (mem_image_of_mem _ hq)
        (closedKlein_image_closedModelDiscHSegment p q ▸ mem_image_of_mem _ hx)
    obtain ⟨y,hy,he⟩ := hK
    exact closedKleinCoordinate_injective he ▸ hy

/-- Local convexity in the genuine compactified model uses its relative topology
and actual finite/ideal hyperbolic segments. -/
def IsLocallyClosedDiscHConvex (S : Set 𝕔𝔻) : Prop :=
  ∀ p ∈ S, ∃ U : Set 𝕔𝔻, IsOpen U ∧ p ∈ U ∧ ClosedDiscHConvex (S ∩ U)

/-- The local-convexity transfer works even at the ideal circle: relative open
neighborhoods are restrictions of actual ambient Euclidean open neighborhoods. -/
theorem locallyClosedDiscHConvex_iff_klein_local (S : Set 𝕔𝔻) :
    IsLocallyClosedDiscHConvex S ↔
      ∀ w ∈ closedKleinCoordinate '' S, ∃ V : Set ℂ,
        IsOpen V ∧ w ∈ V ∧ Convex ℝ ((closedKleinCoordinate '' S) ∩ V) := by
  constructor
  · intro hS w hw
    obtain ⟨p,hp,rfl⟩ := hw
    obtain ⟨U,hU,hpU,hconv⟩ := hS p hp
    obtain ⟨V,hV,hVU⟩ :=
      isClosedEmbedding_closedKleinCoordinate.isEmbedding.isInducing.isOpen_iff.mp hU
    refine ⟨V,hV,?_,?_⟩
    · change p ∈ closedKleinCoordinate ⁻¹' V
      rw [hVU]
      exact hpU
    · have hc := (closedDiscHConvex_iff_klein_convex (S ∩ U)).mp hconv
      rw [← hVU,image_inter_preimage] at hc
      exact hc
  · intro hS p hp
    obtain ⟨V,hV,hpV,hconv⟩ := hS _ (mem_image_of_mem closedKleinCoordinate hp)
    refine ⟨closedKleinCoordinate ⁻¹' V,
      hV.preimage isClosedEmbedding_closedKleinCoordinate.continuous,hpV,?_⟩
    apply (closedDiscHConvex_iff_klein_convex _).mpr
    rw [image_inter_preimage]
    exact hconv

theorem isClosed_closedKlein_image_iff (S : Set 𝕔𝔻) :
    IsClosed (closedKleinCoordinate '' S) ↔ IsClosed S :=
  isClosedEmbedding_closedKleinCoordinate.isClosed_iff_image_isClosed.symm

theorem isPreconnected_closedKlein_image_iff (S : Set 𝕔𝔻) :
    IsPreconnected (closedKleinCoordinate '' S) ↔ IsPreconnected S :=
  isClosedEmbedding_closedKleinCoordinate.isEmbedding.isInducing.isPreconnected_image

end
end LowDimensionalTopology.Geometry.Hyperbolic
