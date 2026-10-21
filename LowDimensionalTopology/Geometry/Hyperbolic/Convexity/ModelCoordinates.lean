/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Hyperbolic.Models.Disk.IsometryCoefficients
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Analysis.Convex.PathConnected
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-!
# Genuine hyperbolic convexity and Klein coordinates
-/

@[expose] public section
open Set Filter
open scoped UpperHalfPlane MatrixGroups OnePoint Topology ComplexConjugate Complex.UnitDisc
namespace LowDimensionalTopology.Geometry.Hyperbolic
noncomputable section

/-- The actual radial Poincaré-to-Klein coordinate formula. -/
def kleinFormula (z : ℂ) : ℂ := ((2 / (1 + ‖z‖ ^ 2) : ℝ) : ℂ) * z

/-- The actual inverse radial formula. -/
def inverseKleinFormula (z : ℂ) : ℂ :=
  ((1 / (1 + Real.sqrt (1 - ‖z‖ ^ 2)) : ℝ) : ℂ) * z

theorem kleinFormula_norm (z : ℂ) : ‖kleinFormula z‖ = 2 * ‖z‖ / (1 + ‖z‖ ^ 2) := by
  rw [kleinFormula,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (by positivity)]
  ring

theorem kleinFormula_mem_disc (z : 𝔻) : ‖kleinFormula z‖ < 1 := by
  rw [kleinFormula_norm]
  apply (div_lt_one (by positivity : 0 < 1 + ‖(z : ℂ)‖ ^ 2)).mpr
  nlinarith [sq_pos_of_pos (sub_pos.mpr z.norm_lt_one)]

def poincareToKlein (z : 𝔻) : 𝔻 := Complex.UnitDisc.mk (kleinFormula z) (kleinFormula_mem_disc z)

theorem inverseKleinFormula_norm (z : ℂ) :
    ‖inverseKleinFormula z‖ = ‖z‖ / (1 + Real.sqrt (1 - ‖z‖ ^ 2)) := by
  rw [inverseKleinFormula,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (by positivity)]
  ring

theorem inverseKleinFormula_mem_disc (z : 𝔻) : ‖inverseKleinFormula z‖ < 1 := by
  rw [inverseKleinFormula_norm]
  apply (div_lt_one (by positivity : 0 < 1 + Real.sqrt (1 - ‖(z : ℂ)‖ ^ 2))).mpr
  linarith [z.norm_lt_one,Real.sqrt_nonneg (1 - ‖(z : ℂ)‖ ^ 2)]

def kleinToPoincare (z : 𝔻) : 𝔻 :=
  Complex.UnitDisc.mk (inverseKleinFormula z) (inverseKleinFormula_mem_disc z)

theorem klein_sqrt_identity (z : 𝔻) :
    Real.sqrt (1 - ‖kleinFormula z‖ ^ 2) = (1 - ‖(z : ℂ)‖ ^ 2) / (1 + ‖(z : ℂ)‖ ^ 2) := by
  have hpos : 0 < 1 - ‖(z : ℂ)‖ ^ 2 := sub_pos.mpr z.sq_norm_lt_one
  have hden : 0 < 1 + ‖(z : ℂ)‖ ^ 2 := by positivity
  have hrad : 0 ≤ 1 - ‖kleinFormula z‖ ^ 2 := by
    nlinarith [kleinFormula_mem_disc z,norm_nonneg (kleinFormula z)]
  apply (sq_eq_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
  rw [Real.sq_sqrt hrad,kleinFormula_norm]
  field_simp
  ring

theorem kleinToPoincare_poincareToKlein (z : 𝔻) : kleinToPoincare (poincareToKlein z) = z := by
  apply Complex.UnitDisc.coe_injective
  change inverseKleinFormula (kleinFormula z) = (z : ℂ)
  rw [inverseKleinFormula,klein_sqrt_identity]
  have he : 1 / (1 + (1 - ‖(z : ℂ)‖ ^ 2) / (1 + ‖(z : ℂ)‖ ^ 2)) *
      (2 / (1 + ‖(z : ℂ)‖ ^ 2)) = 1 := by
    field_simp
    ring
  rw [kleinFormula,← mul_assoc,← Complex.ofReal_mul,he,Complex.ofReal_one,one_mul]

theorem poincareToKlein_kleinToPoincare (z : 𝔻) : poincareToKlein (kleinToPoincare z) = z := by
  apply Complex.UnitDisc.coe_injective
  change kleinFormula (inverseKleinFormula z) = (z : ℂ)
  rw [kleinFormula,inverseKleinFormula_norm]
  have hs : Real.sqrt (1 - ‖(z : ℂ)‖ ^ 2) ^ 2 = 1 - ‖(z : ℂ)‖ ^ 2 :=
    Real.sq_sqrt (sub_nonneg.mpr z.sq_norm_lt_one.le)
  have hden : 1 + Real.sqrt (1 - ‖(z : ℂ)‖ ^ 2) ≠ 0 := by positivity
  have he : 2 / (1 + (‖(z : ℂ)‖ / (1 + Real.sqrt (1 - ‖(z : ℂ)‖ ^ 2))) ^ 2) *
      (1 / (1 + Real.sqrt (1 - ‖(z : ℂ)‖ ^ 2))) = 1 := by
    apply (div_mul_eq_mul_div _ _ _).trans ?_
    apply (div_eq_one_iff_eq (by positivity)).mpr
    field_simp
    nlinarith
  unfold inverseKleinFormula
  rw [← mul_assoc,← Complex.ofReal_mul,he,Complex.ofReal_one,one_mul]

theorem continuous_poincareToKlein : Continuous poincareToKlein := by
  apply Complex.UnitDisc.isEmbedding_coe.continuous_iff.mpr
  change Continuous (fun z : 𝔻 => kleinFormula z)
  have hn : Continuous (fun z : 𝔻 => ‖(z : ℂ)‖ ^ 2) :=
    (continuous_norm.comp Complex.UnitDisc.continuous_coe).pow 2
  have hs : Continuous (fun z : 𝔻 => (2 : ℝ) / (1 + ‖(z : ℂ)‖ ^ 2)) :=
    continuous_const.div (continuous_const.add hn) (fun _ => by positivity)
  exact (Complex.continuous_ofReal.comp hs).mul Complex.UnitDisc.continuous_coe

theorem continuous_kleinToPoincare : Continuous kleinToPoincare := by
  apply Complex.UnitDisc.isEmbedding_coe.continuous_iff.mpr
  change Continuous (fun z : 𝔻 => inverseKleinFormula z)
  have hn : Continuous (fun z : 𝔻 => ‖(z : ℂ)‖ ^ 2) :=
    (continuous_norm.comp Complex.UnitDisc.continuous_coe).pow 2
  have hs : Continuous (fun z : 𝔻 => (1 : ℝ) / (1 + Real.sqrt (1 - ‖(z : ℂ)‖ ^ 2))) :=
    continuous_const.div (continuous_const.add ((continuous_const.sub hn).sqrt)) (fun _ => by positivity)
  exact (Complex.continuous_ofReal.comp hs).mul Complex.UnitDisc.continuous_coe

/-- The genuine radial homeomorphism between the Poincaré and Klein discs. -/
def kleinHomeomorph : 𝔻 ≃ₜ 𝔻 where
  toFun := poincareToKlein
  invFun := kleinToPoincare
  left_inv := kleinToPoincare_poincareToKlein
  right_inv := poincareToKlein_kleinToPoincare
  continuous_toFun := continuous_poincareToKlein
  continuous_invFun := continuous_kleinToPoincare

theorem kleinFormula_inner (z a : ℂ) :
    inner ℝ (kleinFormula z) a = (2 / (1 + ‖z‖ ^ 2)) * inner ℝ z a := by
  rw [kleinFormula,← Complex.real_smul,real_inner_smul_left]

theorem klein_circle_iff (z : 𝔻) (c : ℂ) (r : ℝ) (hr : 0 < r)
    (hcr : ‖c‖ ^ 2 = r ^ 2 + 1) :
    ‖(z : ℂ) - c‖ = r ↔ inner ℝ (kleinFormula z) c = 1 := by
  rw [kleinFormula_inner,div_mul_eq_mul_div]
  have hden : 1 + ‖(z : ℂ)‖ ^ 2 ≠ 0 := by positivity
  rw [div_eq_one_iff_eq hden]
  have he := norm_sub_sq_real (z : ℂ) c
  constructor
  · intro hz
    rw [hz,hcr] at he
    nlinarith
  · intro hz
    rw [hcr] at he
    nlinarith [norm_nonneg ((z : ℂ) - c)]

theorem klein_diameter_iff (z : 𝔻) (a : ℂ) :
    inner ℝ (z : ℂ) a = 0 ↔ inner ℝ (kleinFormula z) a = 0 := by
  rw [kleinFormula_inner]
  have hs : (2 : ℝ) / (1 + ‖(z : ℂ)‖ ^ 2) ≠ 0 := by positivity
  rw [mul_eq_zero]
  simp only [hs,false_or]

/-- Every native disc h-line becomes a genuine real affine line in Klein coordinates. -/
theorem DiscLine.exists_klein_affine_equation (L : DiscLine) :
    ∃ (a : ℂ) (t : ℝ), a ≠ 0 ∧ ∀ z : 𝔻,
      z ∈ L.carrier ↔ inner ℝ (poincareToKlein z : ℂ) a = t := by
  rcases (isDiscHLine_iff_euclidean L.carrier).mp ⟨L,rfl⟩ with
    ⟨c,r,hr,hcr,hL⟩ | ⟨a,ha,hL⟩
  · have hc : c ≠ 0 := by
      intro h
      rw [h,norm_zero] at hcr
      nlinarith
    refine ⟨c,1,hc,fun z => ?_⟩
    rw [hL]
    exact klein_circle_iff z c r hr hcr
  · refine ⟨a,0,ha,fun z => ?_⟩
    rw [hL]
    exact klein_diameter_iff z a

/-- A continuous injective curve contained in one real affine line traces precisely the
Euclidean segment between the images of two ordered parameter endpoints. -/
theorem line_curve_image_segment {γ : ℝ → ℂ} (hγ : Continuous γ) (hi : Function.Injective γ)
    {a : ℂ} {b : ℝ} (ha : a ≠ 0) (he : ∀ t : ℝ, inner ℝ (γ t) a = b)
    {s t : ℝ} (hst : s < t) : γ '' Icc s t = segment ℝ (γ s) (γ t) := by
  let := Complex.finrank_real_complex_fact
  let d := γ t - γ s
  have hd : d ≠ 0 := sub_ne_zero.mpr (hi.ne hst.ne')
  have hdN : ‖d‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hd)
  let φ : ℝ → ℝ := fun u => inner ℝ d (γ u - γ s) / ‖d‖ ^ 2
  have hparam (u : ℝ) : γ u = γ s + φ u • d := by
    have hu : inner ℝ a (γ u - γ s) = 0 := by
      rw [← real_inner_comm a (γ u - γ s),inner_sub_left,he u,he s,sub_self]
    have hdt : inner ℝ a d = 0 := by
      change inner ℝ a (γ t - γ s) = 0
      rw [← real_inner_comm a (γ t - γ s),inner_sub_left,he t,he s,sub_self]
    obtain ⟨r,hr⟩ := Submodule.mem_span_singleton.mp
      (Submodule.mem_span_singleton_of_inner_eq_zero_of_inner_eq_zero ha hd hu hdt)
    have hφ : φ u = r := by
      change inner ℝ d (γ u - γ s) / ‖d‖ ^ 2 = r
      rw [← hr,inner_smul_right,real_inner_self_eq_norm_sq]
      exact mul_div_cancel_right₀ r hdN
    rw [hφ,hr]
    abel
  have hφc : Continuous φ := (continuous_const.inner (hγ.sub continuous_const)).div_const _
  have hφi : Function.Injective φ := by
    intro u v huv
    apply hi
    rw [hparam u,hparam v,huv]
  have hφs : φ s = 0 := by simp [φ]
  have hφt : φ t = 1 := by
    dsimp [φ]
    change inner ℝ d d / ‖d‖ ^ 2 = 1
    rw [real_inner_self_eq_norm_sq,div_self hdN]
  have hm := hφc.continuousOn.strictMonoOn_of_injOn_Icc hst.le
    (by rw [hφs,hφt]; norm_num) hφi.injOn
  have him : φ '' Icc s t = Icc (0 : ℝ) 1 := by
    have h := hφc.continuousOn.image_Icc_of_monotoneOn hst.le hm.monotoneOn
    simpa only [hφs,hφt] using h
  calc
    γ '' Icc s t = (fun r : ℝ => γ s + r • d) '' (φ '' Icc s t) := by
      rw [image_image]
      apply Set.image_congr
      intro u _
      exact hparam u
    _ = segment ℝ (γ s) (γ t) := by rw [him,segment_eq_image']

theorem closedHSegment_self (z : ℍ) : closedHSegment z z = {z} := by
  ext u
  constructor
  · intro hu
    have he := dist_triangle_eq_of_mem_closedHSegment hu
    rw [dist_self] at he
    have hdist : dist u z = 0 := by nlinarith [dist_nonneg (x := z) (y := u),dist_nonneg (x := u) (y := z)]
    exact dist_eq_zero.mp hdist
  · intro hu
    have huz : u = z := hu
    subst u
    let L := HalfPlaneLine.vertical z.re
    obtain ⟨γ,hγ,hrange⟩ := L.exists_isometric_param
    have hz : z ∈ L.carrier := rfl
    obtain ⟨r,hr⟩ : z ∈ range γ := hrange.symm ▸ hz
    refine ⟨γ,⟨hγ,?_⟩,r,r,le_refl r,hr,hr,r,⟨le_refl r,le_refl r⟩,hr⟩
    rw [hrange]
    exact L.isHLine

theorem closedDiscHSegment_self (z : 𝔻) : closedDiscHSegment z z = {z} := by
  rw [closedDiscHSegment_eq_cayley_image,closedHSegment_self,image_singleton,
    halfPlaneToDisc_discToHalfPlane]

/-- The actual Klein coordinate as a complex point. -/
def kleinCoordinate (z : 𝔻) : ℂ := (poincareToKlein z : ℂ)

theorem continuous_kleinCoordinate : Continuous kleinCoordinate :=
  Complex.UnitDisc.continuous_coe.comp continuous_poincareToKlein

theorem kleinCoordinate_injective : Function.Injective kleinCoordinate :=
  Complex.UnitDisc.coe_injective.comp kleinHomeomorph.injective

/-- The actual component-defined/geodesic segment maps to the actual Euclidean segment. -/
theorem klein_image_closedDiscHSegment (z w : 𝔻) :
    kleinCoordinate '' closedDiscHSegment z w = segment ℝ (kleinCoordinate z) (kleinCoordinate w) := by
  by_cases hzw : z = w
  · subst w
    rw [closedDiscHSegment_self,image_singleton,segment_same]
  obtain ⟨L,⟨hz,hw⟩,_⟩ := existsUnique_discLine_through z w hzw
  obtain ⟨δ,s,t,hδ,hst,hs,ht,hrange⟩ := L.exists_ordered_param hzw hz hw
  obtain ⟨a,b,ha,he⟩ := L.exists_klein_affine_equation
  let γ : ℝ → ℂ := kleinCoordinate ∘ halfPlaneToDisc ∘ δ
  have hγ : Continuous γ := continuous_kleinCoordinate.comp
    (cayleyHomeomorph.continuous.comp hδ.1.continuous)
  have hγi : Function.Injective γ := kleinCoordinate_injective.comp
    (cayleyHomeomorph.injective.comp hδ.1.injective)
  have hline (u : ℝ) : inner ℝ (γ u) a = b := by
    apply (he _).mp
    rw [← hrange]
    exact mem_range_self u
  have him := line_curve_image_segment hγ hγi ha hline hst
  have hs' : γ s = kleinCoordinate z := congrArg kleinCoordinate hs
  have ht' : γ t = kleinCoordinate w := congrArg kleinCoordinate ht
  rw [hs',ht'] at him
  rw [← hs,← ht,closedDiscHSegment_eq_image_Icc hδ hst,image_image]
  simpa only [γ,Function.comp_def,hs,ht] using him

/-- The source hyperbolic convexity definition in H uses the genuine closed h-segment. -/
def HConvex (S : Set ℍ) : Prop := ∀ z ∈ S, ∀ w ∈ S, closedHSegment z w ⊆ S

/-- The same source definition on native disc h-segments. -/
def DiscHConvex (S : Set 𝔻) : Prop := ∀ z ∈ S, ∀ w ∈ S, closedDiscHSegment z w ⊆ S

/-- Klein coordinates identify the source native disc convexity with actual Euclidean convexity. -/
theorem discHConvex_iff_klein_convex (S : Set 𝔻) :
    DiscHConvex S ↔ Convex ℝ (kleinCoordinate '' S) := by
  rw [convex_iff_segment_subset]
  constructor
  · intro h z hz w hw
    obtain ⟨Z,hZ,rfl⟩ := hz
    obtain ⟨W,hW,rfl⟩ := hw
    rw [← klein_image_closedDiscHSegment]
    exact image_mono (h Z hZ W hW)
  · intro h z hz w hw u hu
    have him : kleinCoordinate u ∈ segment ℝ (kleinCoordinate z) (kleinCoordinate w) := by
      rw [← klein_image_closedDiscHSegment]
      exact mem_image_of_mem kleinCoordinate hu
    obtain ⟨v,hv,he⟩ := h (mem_image_of_mem kleinCoordinate hz) (mem_image_of_mem kleinCoordinate hw) him
    exact kleinCoordinate_injective he ▸ hv

/-- Actual Cayley transport preserves the full source segment-convexity definition. -/
theorem hConvex_iff_cayley_discHConvex (S : Set ℍ) :
    HConvex S ↔ DiscHConvex (halfPlaneToDisc '' S) := by
  constructor
  · intro h z hz w hw u hu
    obtain ⟨Z,hZ,rfl⟩ := hz
    obtain ⟨W,hW,rfl⟩ := hw
    rw [closedDiscHSegment_eq_cayley_image,discToHalfPlane_halfPlaneToDisc,
      discToHalfPlane_halfPlaneToDisc] at hu
    obtain ⟨U,hU,rfl⟩ := hu
    exact mem_image_of_mem halfPlaneToDisc (h Z hZ W hW hU)
  · intro h z hz w hw u hu
    have hU := h (halfPlaneToDisc z) (mem_image_of_mem halfPlaneToDisc hz)
      (halfPlaneToDisc w) (mem_image_of_mem halfPlaneToDisc hw)
    have huD : halfPlaneToDisc u ∈ closedDiscHSegment (halfPlaneToDisc z) (halfPlaneToDisc w) := by
      rw [closedDiscHSegment_eq_cayley_image,discToHalfPlane_halfPlaneToDisc,
        discToHalfPlane_halfPlaneToDisc]
      exact mem_image_of_mem halfPlaneToDisc hu
    obtain ⟨v,hv,he⟩ := hU huD
    have hvu : v = u := cayleyHomeomorph.injective he
    exact hvu ▸ hv

theorem isEmbedding_kleinCoordinate : Topology.IsEmbedding kleinCoordinate :=
  Complex.UnitDisc.isEmbedding_coe.comp kleinHomeomorph.isEmbedding

theorem range_kleinCoordinate : range kleinCoordinate = Metric.ball (0 : ℂ) 1 := by
  ext z
  constructor
  · rintro ⟨u,rfl⟩
    exact mem_ball_zero_iff.mpr (poincareToKlein u).norm_lt_one
  · intro hz
    let w := Complex.UnitDisc.mk z (mem_ball_zero_iff.mp hz)
    refine ⟨kleinToPoincare w,?_⟩
    change (poincareToKlein (kleinToPoincare w) : ℂ) = z
    rw [poincareToKlein_kleinToPoincare]
    rfl

theorem isOpenEmbedding_kleinCoordinate : Topology.IsOpenEmbedding kleinCoordinate :=
  ⟨isEmbedding_kleinCoordinate,by rw [range_kleinCoordinate]; exact Metric.isOpen_ball⟩

theorem klein_image_closure (S : Set 𝔻) :
    kleinCoordinate '' closure S = closure (kleinCoordinate '' S) ∩ Metric.ball (0 : ℂ) 1 := by
  rw [isEmbedding_kleinCoordinate.closure_eq_preimage_closure_image S,
    image_preimage_eq_inter_range,range_kleinCoordinate]

theorem klein_image_interior (S : Set 𝔻) :
    kleinCoordinate '' interior S = interior (kleinCoordinate '' S) ∩ Metric.ball (0 : ℂ) 1 := by
  have he : interior S = kleinCoordinate ⁻¹' interior (kleinCoordinate '' S) := by
    rw [isOpenEmbedding_kleinCoordinate.isOpenMap.preimage_interior_eq_interior_preimage
      continuous_kleinCoordinate,preimage_image_eq _ kleinCoordinate_injective]
  rw [he,image_preimage_eq_inter_range,range_kleinCoordinate]

/-- The actual original-topology closure of a disc h-convex set remains h-convex. -/
theorem DiscHConvex.closure {S : Set 𝔻} (hS : DiscHConvex S) : DiscHConvex (closure S) := by
  apply (discHConvex_iff_klein_convex _).mpr
  rw [klein_image_closure]
  exact ((discHConvex_iff_klein_convex _).mp hS).closure.inter (convex_ball (0 : ℂ) 1)

theorem DiscHConvex.interior {S : Set 𝔻} (hS : DiscHConvex S) : DiscHConvex (interior S) := by
  apply (discHConvex_iff_klein_convex _).mpr
  rw [klein_image_interior]
  exact ((discHConvex_iff_klein_convex _).mp hS).interior.inter (convex_ball (0 : ℂ) 1)

theorem HConvex.closure {S : Set ℍ} (hS : HConvex S) : HConvex (closure S) := by
  apply (hConvex_iff_cayley_discHConvex _).mpr
  have he : halfPlaneToDisc '' _root_.closure S = _root_.closure (halfPlaneToDisc '' S) :=
    cayleyHomeomorph.image_closure S
  rw [he]
  exact _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscHConvex.closure ((hConvex_iff_cayley_discHConvex _).mp hS)

theorem HConvex.interior {S : Set ℍ} (hS : HConvex S) : HConvex (interior S) := by
  apply (hConvex_iff_cayley_discHConvex _).mpr
  have he : halfPlaneToDisc '' _root_.interior S = _root_.interior (halfPlaneToDisc '' S) :=
    cayleyHomeomorph.image_interior S
  rw [he]
  exact _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscHConvex.interior ((hConvex_iff_cayley_discHConvex _).mp
    hS)

theorem HConvex.iInter {ι : Sort*} {S : ι → Set ℍ} (hS : ∀ i, HConvex (S i)) :
    HConvex (⋂ i,S i) := by
  intro z hz w hw u hu
  exact mem_iInter.mpr (fun i => hS i z (mem_iInter.mp hz i) w (mem_iInter.mp hw i) hu)

theorem DiscHConvex.iInter {ι : Sort*} {S : ι → Set 𝔻} (hS : ∀ i, DiscHConvex (S i)) :
    DiscHConvex (⋂ i,S i) := by
  intro z hz w hw u hu
  exact mem_iInter.mpr (fun i => hS i z (mem_iInter.mp hz i) w (mem_iInter.mp hw i) hu)

theorem HConvex.directed_iUnion {ι : Sort*} {S : ι → Set ℍ} (hd : Directed (· ⊆ ·) S)
    (hS : ∀ i, HConvex (S i)) : HConvex (⋃ i,S i) := by
  intro z hz w hw u hu
  obtain ⟨i,hi⟩ := mem_iUnion.mp hz
  obtain ⟨j,hj⟩ := mem_iUnion.mp hw
  obtain ⟨k,hik,hjk⟩ := hd i j
  exact mem_iUnion.mpr ⟨k,hS k z (hik hi) w (hjk hj) hu⟩

theorem DiscHConvex.directed_iUnion {ι : Sort*} {S : ι → Set 𝔻} (hd : Directed (· ⊆ ·) S)
    (hS : ∀ i, DiscHConvex (S i)) : DiscHConvex (⋃ i,S i) := by
  intro z hz w hw u hu
  obtain ⟨i,hi⟩ := mem_iUnion.mp hz
  obtain ⟨j,hj⟩ := mem_iUnion.mp hw
  obtain ⟨k,hik,hjk⟩ := hd i j
  exact mem_iUnion.mpr ⟨k,hS k z (hik hi) w (hjk hj) hu⟩

/-- Convexity is invariant under genuine H isometries. -/
theorem HConvex.isometry_image {S : Set ℍ} (hS : HConvex S) {f : ℍ → ℍ} (hf : Isometry f) :
    HConvex (f '' S) := by
  intro z hz w hw u hu
  obtain ⟨Z,hZ,rfl⟩ := hz
  obtain ⟨W,hW,rfl⟩ := hw
  by_cases hZW : Z = W
  · subst W
    rw [closedHSegment_self] at hu
    have hue : u = f Z := hu
    exact hue.symm ▸ mem_image_of_mem f hZ
  · rw [← _root_.LowDimensionalTopology.Geometry.Hyperbolic.Isometry.image_closedHSegment hf hZW] at hu
    obtain ⟨U,hU,rfl⟩ := hu
    exact mem_image_of_mem f (hS Z hZ W hW hU)

/-- Convexity is invariant under genuine native-disc isometries. -/
theorem DiscHConvex.isometry_image {S : Set 𝔻} (hS : DiscHConvex S) {f : 𝔻 → 𝔻} :
    letI := discHyperbolicMetric; Isometry f → DiscHConvex (f '' S) := by
  let := discHyperbolicMetric
  intro hf z hz w hw u hu
  obtain ⟨Z,hZ,rfl⟩ := hz
  obtain ⟨W,hW,rfl⟩ := hw
  by_cases hZW : Z = W
  · subst W
    rw [closedDiscHSegment_self] at hu
    have hue : u = f Z := hu
    exact hue.symm ▸ mem_image_of_mem f hZ
  · rw [← disc_isometry_image_closedHSegment hf hZW] at hu
    obtain ⟨U,hU,rfl⟩ := hu
    exact mem_image_of_mem f (hS Z hZ W hW hU)

theorem closedHSegment_param_Icc {γ : ℝ → ℍ} (hγ : IsHGeodesicParam γ)
    {s t : ℝ} (hst : s ≤ t) : closedHSegment (γ s) (γ t) = γ '' Icc s t := by
  rcases lt_or_eq_of_le hst with h | h
  · exact closedHSegment_eq_image_Icc hγ h
  · subst t
    rw [closedHSegment_self,Icc_self,image_singleton]

/-- On any genuine h-line chart, source convex subsets are exactly real intervals. -/
theorem hConvex_iff_ordConnected_parameter {γ : ℝ → ℍ} (hγ : IsHGeodesicParam γ)
    {S : Set ℍ} (hS : S ⊆ range γ) : HConvex S ↔ OrdConnected (γ ⁻¹' S) := by
  rw [ordConnected_iff]
  constructor
  · intro h s hs t ht hst r hr
    apply h (γ s) hs (γ t) ht
    rw [closedHSegment_param_Icc hγ hst]
    exact mem_image_of_mem γ hr
  · intro h z hz w hw u hu
    obtain ⟨s,rfl⟩ := hS hz
    obtain ⟨t,rfl⟩ := hS hw
    rcases le_total s t with hst | hts
    · rw [closedHSegment_param_Icc hγ hst] at hu
      obtain ⟨r,hr,rfl⟩ := hu
      exact h s hz t hw hst hr
    · by_cases he : s = t
      · subst t
        rw [closedHSegment_self] at hu
        have hue : u = γ s := hu
        exact hue.symm ▸ hz
      · rw [closedHSegment_comm (hγ.1.injective.ne he),closedHSegment_param_Icc hγ hts] at hu
        obtain ⟨r,hr,rfl⟩ := hu
        exact h t hw s hz hts hr

theorem hConvex_iff_convex_parameter {γ : ℝ → ℍ} (hγ : IsHGeodesicParam γ)
    {S : Set ℍ} (hS : S ⊆ range γ) : HConvex S ↔ Convex ℝ (γ ⁻¹' S) := by
  rw [hConvex_iff_ordConnected_parameter hγ hS,convex_iff_ordConnected]

/-- Complete genuine H lines are convex, as a special case of the exact interval criterion. -/
theorem HalfPlaneLine.hConvex (L : HalfPlaneLine) : HConvex L.carrier := by
  obtain ⟨γ,hiso,hrange⟩ := L.exists_isometric_param
  have hγ : IsHGeodesicParam γ := ⟨hiso,hrange ▸ L.isHLine⟩
  apply (hConvex_iff_ordConnected_parameter hγ (by rw [hrange])).mpr
  have he : γ ⁻¹' L.carrier = univ := by rw [← hrange]; exact preimage_range γ
  rw [he]
  exact ordConnected_univ

theorem DiscLine.hConvex (L : DiscLine) : DiscHConvex L.carrier := by
  rw [L.carrier_eq_cayley_image_halfPlane]
  exact (hConvex_iff_cayley_discHConvex _).mp L.toHalfPlane.hConvex

/-- Source convexity implies connectedness, including the empty-set convention. -/
theorem DiscHConvex.isPreconnected {S : Set 𝔻} (hS : DiscHConvex S) : IsPreconnected S :=
  isEmbedding_kleinCoordinate.isInducing.isPreconnected_image.mp
    (((discHConvex_iff_klein_convex _).mp hS).isPreconnected)

theorem HConvex.isPreconnected {S : Set ℍ} (hS : HConvex S) : IsPreconnected S :=
  cayleyHomeomorph.isEmbedding.isInducing.isPreconnected_image.mp
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscHConvex.isPreconnected ((hConvex_iff_cayley_discHConvex _).mp
      hS))

/-- The interval characterization also holds in arbitrary genuine native disc line charts. -/
theorem discHConvex_iff_ordConnected_parameter {γ : ℝ → 𝔻} (hγ : IsNativeDiscGeodesicParam γ)
    {S : Set 𝔻} (hS : S ⊆ range γ) : DiscHConvex S ↔ OrdConnected (γ ⁻¹' S) := by
  have hδ := hγ.toHalfPlane
  have hsub : discToHalfPlane '' S ⊆ range (discToHalfPlane ∘ γ) := by
    rintro _ ⟨z,hz,rfl⟩
    obtain ⟨t,ht⟩ := hS hz
    exact ⟨t,congrArg discToHalfPlane ht⟩
  have hc : HConvex (discToHalfPlane '' S) ↔ DiscHConvex S := by
    rw [hConvex_iff_cayley_discHConvex,cayley_image_inverse_image]
  have hp : (discToHalfPlane ∘ γ) ⁻¹' (discToHalfPlane '' S) = γ ⁻¹' S := by
    ext u
    constructor
    · rintro ⟨z,hz,he⟩
      change γ u ∈ S
      exact discToHalfPlane_injective he ▸ hz
    · intro hu
      exact ⟨γ u,hu,rfl⟩
  rw [← hc,hConvex_iff_ordConnected_parameter hδ hsub,hp]

theorem discHConvex_iff_convex_parameter {γ : ℝ → 𝔻} (hγ : IsNativeDiscGeodesicParam γ)
    {S : Set 𝔻} (hS : S ⊆ range γ) : DiscHConvex S ↔ Convex ℝ (γ ⁻¹' S) := by
  rw [discHConvex_iff_ordConnected_parameter hγ hS,convex_iff_ordConnected]

end
end LowDimensionalTopology.Geometry.Hyperbolic
