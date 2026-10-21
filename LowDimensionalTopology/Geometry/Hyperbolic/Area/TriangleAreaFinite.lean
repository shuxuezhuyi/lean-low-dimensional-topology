/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Hyperbolic.Area.TriangleAreaAngles
public import LowDimensionalTopology.Geometry.Hyperbolic.Triangle.TriangleSideNormals
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.TriangleInequality
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
@[expose] public section
open Set MeasureTheory InnerProductGeometry
open scoped UpperHalfPlane Complex.UnitDisc Topology OnePoint MatrixGroups
namespace LowDimensionalTopology.Geometry.Hyperbolic
open LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
noncomputable section

/-- Actual affine change between two genuine Klein triangle charts. -/
theorem ClosedDiscTriangle.coordinate_change (T U : ClosedDiscTriangle) (x : 𝕔𝔻) :
    U.coordinate x = U.coordinate T.a +
      (T.coordinate x).1 • (U.coordinate T.b - U.coordinate T.a) +
      (T.coordinate x).2 • (U.coordinate T.c - U.coordinate T.a) := by
  change U.coordinateLinear (closedKleinCoordinate x - closedKleinCoordinate U.a) =
    U.coordinateLinear (closedKleinCoordinate T.a - closedKleinCoordinate U.a) +
      (T.coordinate x).1 • (U.coordinateLinear (closedKleinCoordinate T.b - closedKleinCoordinate U.a) -
        U.coordinateLinear (closedKleinCoordinate T.a - closedKleinCoordinate U.a)) +
      (T.coordinate x).2 • (U.coordinateLinear (closedKleinCoordinate T.c - closedKleinCoordinate U.a) -
        U.coordinateLinear (closedKleinCoordinate T.a - closedKleinCoordinate U.a))
  rw [T.klein_reconstruction x]
  simp only [map_add,map_sub,map_smul]
  module

/-- The original finite triangle occupies the lower affine subtriangle of an actual ideal extension. -/
theorem ClosedDiscTriangle.coordinate_split_lower (T U : ClosedDiscTriangle)
    (ha : T.a = U.a) (hb : T.b = U.b) (t : ℝ) (hc : U.coordinate T.c = (0,t)) (x : 𝕔𝔻) :
    U.coordinate x = ((T.coordinate x).1,t * (T.coordinate x).2) := by
  have he := T.coordinate_change U x
  rw [ha,hb,U.coordinate_a,U.coordinate_b,hc] at he
  simpa [mul_comm] using he

/-- Coordinates of the complementary actual upper triangle. -/
theorem ClosedDiscTriangle.coordinate_split_upper (U V : ClosedDiscTriangle)
    (hb : V.b = U.b) (hc : V.c = U.c) (t : ℝ) (ha : U.coordinate V.a = (0,t)) (x : 𝕔𝔻) :
    U.coordinate x = ((V.coordinate x).1,
      t - t * (V.coordinate x).1 + (1-t) * (V.coordinate x).2) := by
  have he := V.coordinate_change U x
  rw [hb,hc,U.coordinate_b,U.coordinate_c,ha] at he
  simpa [sub_eq_add_neg,mul_add,mul_comm,mul_left_comm,add_comm,add_left_comm,add_assoc] using he

/-- Exact whole-interior inequality for the lower genuine subtriangle. -/
theorem ClosedDiscTriangle.halfPlaneInterior_split_lower (T U : ClosedDiscTriangle)
    (ha : T.a = U.a) (hb : T.b = U.b) (t : ℝ) (ht : 0 < t)
    (hc : U.coordinate T.c = (0,t)) (x : ℍ) :
    x ∈ T.halfPlaneInterior ↔ 0 < (U.halfPlaneCoordinate x).1 ∧
      0 < (U.halfPlaneCoordinate x).2 ∧
      t * (U.halfPlaneCoordinate x).1 + (U.halfPlaneCoordinate x).2 < t := by
  have he := T.coordinate_split_lower U ha hb t hc (discToClosedModel (halfPlaneToDisc x))
  change U.halfPlaneCoordinate x = ((T.halfPlaneCoordinate x).1,t * (T.halfPlaneCoordinate x).2) at he
  rw [he,T.mem_halfPlaneInterior_iff]
  constructor
  · rintro ⟨hx,hy,hz⟩
    refine ⟨hx,mul_pos ht hy,?_⟩
    nlinarith only [mul_lt_mul_of_pos_left hz ht]
  · rintro ⟨hx,hy,hz⟩
    refine ⟨hx,(mul_pos_iff_of_pos_left ht).mp hy,?_⟩
    apply (mul_lt_mul_iff_right₀ ht).mp
    nlinarith only [hz]

/-- Exact whole-interior inequality for the complementary genuine subtriangle. -/
theorem ClosedDiscTriangle.halfPlaneInterior_split_upper (U V : ClosedDiscTriangle)
    (hb : V.b = U.b) (hc : V.c = U.c) (t : ℝ) (ht : t < 1)
    (ha : U.coordinate V.a = (0,t)) (x : ℍ) :
    x ∈ V.halfPlaneInterior ↔ 0 < (U.halfPlaneCoordinate x).1 ∧
      (U.halfPlaneCoordinate x).1 + (U.halfPlaneCoordinate x).2 < 1 ∧
      t < t * (U.halfPlaneCoordinate x).1 + (U.halfPlaneCoordinate x).2 := by
  have he := U.coordinate_split_upper V hb hc t ha (discToClosedModel (halfPlaneToDisc x))
  change U.halfPlaneCoordinate x = ((V.halfPlaneCoordinate x).1,
    t - t * (V.halfPlaneCoordinate x).1 + (1-t) * (V.halfPlaneCoordinate x).2) at he
  rw [he,V.mem_halfPlaneInterior_iff]
  constructor
  · rintro ⟨hx,hy,hz⟩
    refine ⟨hx,?_,?_⟩
    · nlinarith only [mul_pos (sub_pos.mpr ht) (sub_pos.mpr hz)]
    · nlinarith only [mul_pos (sub_pos.mpr ht) hy]
  · rintro ⟨hx,hz,hy⟩
    refine ⟨hx,?_,?_⟩
    · nlinarith only [hy,ht]
    · nlinarith only [hz,ht]

/-- The dividing straight affine level is exactly the genuine opposing h-line. -/
theorem ClosedDiscTriangle.split_level_eq_sideLine (T U : ClosedDiscTriangle)
    (ha : T.a = U.a) (hb : T.b = U.b) (t : ℝ) (ht : 0 < t)
    (hc : U.coordinate T.c = (0,t)) :
    {x : ℍ | t * (U.halfPlaneCoordinate x).1 + (U.halfPlaneCoordinate x).2 = t} =
      T.sideLineA.toHalfPlane.carrier := by
  ext x
  have he := T.coordinate_split_lower U ha hb t hc (discToClosedModel (halfPlaneToDisc x))
  change U.halfPlaneCoordinate x = ((T.halfPlaneCoordinate x).1,t * (T.halfPlaneCoordinate x).2) at he
  rw [mem_ofPred,he,← T.halfPlaneCoordinate_opposite_line x]
  constructor <;> intro h <;> nlinarith only [h,ht]

/-- A native vertical h-line has zero genuine density area. -/
theorem halfPlane_vertical_volume_zero : volume (HalfPlaneLine.vertical 0).carrier = 0 := by
  have hker : Complex.reCLM.ker ≠ ⊤ := by
    intro he
    have h : (1 : ℂ) ∈ Complex.reCLM.ker := by rw [he]; trivial
    simp at h
  have hzero : (volume : Measure ℂ) (Complex.reCLM.ker : Set ℂ) = 0 :=
    Measure.addHaar_submodule volume Complex.reCLM.ker hker
  have hnull : (volume : Measure ℂ) (((↑) : ℍ → ℂ) '' (HalfPlaneLine.vertical 0).carrier) = 0 := by
    apply measure_mono_null _ hzero
    rintro _ ⟨z,hz,rfl⟩
    exact hz
  rw [UpperHalfPlane.volume_eq_lintegral,Measure.restrict_eq_zero.mpr hnull]
  exact lintegral_zero_measure _

/-- Every actual h-line is null for the genuine hyperbolic density measure. -/
theorem HalfPlaneLine.volume_zero (L : HalfPlaneLine) : volume L.carrier = 0 := by
  obtain ⟨g,_,hL⟩ := L.exists_normalizer
  have him : (g • · : ℍ → ℍ) '' L.carrier = (HalfPlaneLine.vertical 0).carrier := by
    rw [hL]
    change (g • · : ℍ → ℍ) '' ((g • · : ℍ → ℍ) ⁻¹' (HalfPlaneLine.vertical 0).carrier) = (HalfPlaneLine.vertical
      0).carrier
    apply image_preimage_eq_of_subset
    intro z _
    exact ⟨g⁻¹ • z,by simp⟩
  have he := measure_smul (volume : Measure ℍ) g L.carrier
  change volume ((g • · : ℍ → ℍ) '' L.carrier) = volume L.carrier at he
  rw [him,halfPlane_vertical_volume_zero] at he
  exact he.symm

/-- Every actual finite ray reaches an ideal vertex in the genuine closed model. -/
theorem discRayThrough_exists_closed_ideal_extension (a c : 𝔻) (hac : a ≠ c) :
    ∃ w : 𝕔𝔻, ‖(w : ℂ)‖ = 1 ∧
      discToClosedModel c ∈ closedModelDiscHSegment (discToClosedModel a) w := by
  let R := discRayThrough a c hac
  obtain ⟨w,hw,hwe⟩ := R.idealEndpoint_mem
  have hwn : ‖w‖ = 1 := by simpa only [Metric.mem_sphere,dist_zero_right] using hw
  let p : 𝕔𝔻 := ⟨w,by simpa only [Submonoid.mem_unitClosedBall] using hwn.le⟩
  have hpE : closedDiscToExtended p = R.idealEndpoint := hwe
  refine ⟨p,hwn,?_⟩
  rw [closedModelDiscHSegment_ray a p hwn]
  apply subset_closure
  refine ⟨c,?_,rfl⟩
  rw [hpE,discHRay_eq_of_isDiscHLineRay R.isRay]
  exact discRayThrough_mem a c hac

/-- The genuine larger triangle obtained by extending the first-to-third side. -/
def ClosedDiscTriangle.idealExtension (T : ClosedDiscTriangle) (w : 𝕔𝔻)
    (hc : T.c ∈ closedModelDiscHSegment T.a w) : ClosedDiscTriangle where
  a := T.a
  b := T.b
  c := w
  noncollinear := by
    rintro ⟨L,ha,hb,hw⟩
    exact T.noncollinear ⟨L,ha,hb,L.closedCarrier_hConvex T.a ha w hw hc⟩

/-- The genuine complementary triangle above the old third vertex. -/
def ClosedDiscTriangle.idealComplement (T : ClosedDiscTriangle) (w : 𝕔𝔻)
    (hc : T.c ∈ closedModelDiscHSegment T.a w) (hcw : T.c ≠ w) : ClosedDiscTriangle where
  a := T.c
  b := T.b
  c := w
  noncollinear := by
    rintro ⟨L,hcL,hbL,hwL⟩
    let U := T.idealExtension w hc
    have hcU : T.c ∈ U.sideLineB.closedCarrier :=
      U.sideLineB.closedCarrier_hConvex T.a U.a_mem_sideLineB w U.c_mem_sideLineB hc
    have hLU : L = U.sideLineB := L.eq_of_two_closed_points U.sideLineB hcw hcL hwL hcU U.c_mem_sideLineB
    have haL : T.a ∈ L.closedCarrier := hLU.symm ▸ U.a_mem_sideLineB
    exact T.noncollinear ⟨L,haL,hbL,hcL⟩

/-- The old third vertex lies strictly between the extended vertices in the true affine chart. -/
theorem ClosedDiscTriangle.idealExtension_coordinate (T : ClosedDiscTriangle) (w : 𝕔𝔻)
    (hc : T.c ∈ closedModelDiscHSegment T.a w) (hcw : T.c ≠ w) :
    ∃ t : ℝ, 0 < t ∧ t < 1 ∧ (T.idealExtension w hc).coordinate T.c = (0,t) := by
  let U := T.idealExtension w hc
  have hcs : T.c ∈ U.sideB := by
    change T.c ∈ closedModelDiscHSegment w T.a
    rwa [closedModelDiscHSegment_comm]
  obtain ⟨ht0,ht1,hx⟩ := (U.mem_sideB_iff_coordinate T.c).mp hcs
  have hinj : Function.Injective U.coordinate := U.coordinateHomeomorph.injective.comp closedKleinCoordinate_injective
  have htne0 : (U.coordinate T.c).2 ≠ 0 := by
    intro he
    have hp : U.coordinate T.c = U.coordinate U.a := by rw [U.coordinate_a]; exact Prod.ext hx he
    exact T.c_ne_a (hinj hp)
  have htne1 : (U.coordinate T.c).2 ≠ 1 := by
    intro he
    have hp : U.coordinate T.c = U.coordinate U.c := by rw [U.coordinate_c]; exact Prod.ext hx he
    exact hcw (hinj hp)
  exact ⟨(U.coordinate T.c).2,lt_of_le_of_ne ht0 (Ne.symm htne0),
    lt_of_le_of_ne ht1 htne1,Prod.ext hx rfl⟩

/-- The affine cut partitions the genuine open triangle away from its dividing line. -/
theorem triangle_area_split_inequalities (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1)
    (x y : ℝ) (hcut : t*x+y ≠ t) :
    (0 < x ∧ 0 < y ∧ x+y < 1) ↔
      (0 < x ∧ 0 < y ∧ t*x+y < t) ∨
      (0 < x ∧ x+y < 1 ∧ t < t*x+y) := by
  constructor
  · rintro ⟨hx,hy,hs⟩
    rcases lt_or_gt_of_ne hcut with h | h
    · exact Or.inl ⟨hx,hy,h⟩
    · exact Or.inr ⟨hx,hs,h⟩
  · rintro (⟨hx,hy,hl⟩ | ⟨hx,hs,hu⟩)
    · refine ⟨hx,hy,?_⟩
      nlinarith only [hl,ht0,mul_pos (sub_pos.mpr ht1) hy]
    · refine ⟨hx,?_,hs⟩
      have hpos : 0 < (1-t)*y := by nlinarith only [hu,mul_lt_mul_of_pos_left hs ht0]
      exact (mul_pos_iff_of_pos_left (sub_pos.mpr ht1)).mp hpos

/-- Additivity for the actual weighted areas of a genuine finite triangle and its ideal complement. -/
theorem ClosedDiscTriangle.idealExtension_area_add (T : ClosedDiscTriangle) (w : 𝕔𝔻)
    (hc : T.c ∈ closedModelDiscHSegment T.a w) (hcw : T.c ≠ w) :
    volume (T.idealExtension w hc).halfPlaneInterior = volume T.halfPlaneInterior +
      volume (T.idealComplement w hc hcw).halfPlaneInterior := by
  let U := T.idealExtension w hc
  let V := T.idealComplement w hc hcw
  obtain ⟨t,ht0,ht1,htc⟩ := T.idealExtension_coordinate w hc hcw
  have hLow := T.halfPlaneInterior_split_lower U rfl rfl t ht0 htc
  have hHigh := U.halfPlaneInterior_split_upper V rfl rfl t ht1 htc
  have hlevel := T.split_level_eq_sideLine U rfl rfl t ht0 htc
  have hae : U.halfPlaneInterior =ᵐ[volume] T.halfPlaneInterior ∪ V.halfPlaneInterior := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp T.sideLineA.toHalfPlane.volume_zero] with x hx
    have hne : t * (U.halfPlaneCoordinate x).1 + (U.halfPlaneCoordinate x).2 ≠ t := by
      intro he
      apply hx
      rw [← hlevel]
      exact he
    apply propext
    rw [mem_union,hLow x,hHigh x,U.mem_halfPlaneInterior_iff]
    exact triangle_area_split_inequalities t ht0 ht1 _ _ hne
  have hd : Disjoint T.halfPlaneInterior V.halfPlaneInterior := by
    apply disjoint_left.mpr
    intro x hx hy
    have hl := (hLow x).mp hx
    have hu := (hHigh x).mp hy
    exact (not_lt_of_gt hl.2.2) hu.2.2
  rw [measure_congr hae,measure_union hd]
  exact V.interior_isOpen.measurableSet.preimage continuous_halfPlaneToDisc.measurable

/-- Cyclic chart coordinates are the actual affine barycentric coordinates. -/
theorem ClosedDiscTriangle.cycle_coordinate (T : ClosedDiscTriangle) (x : 𝕔𝔻) :
    T.cycle.coordinate x = ((T.coordinate x).2,1-(T.coordinate x).1-(T.coordinate x).2) := by
  have he := T.cycle.coordinate_change T x
  change T.coordinate x = T.coordinate T.b + (T.cycle.coordinate x).1 •
    (T.coordinate T.c - T.coordinate T.b) + (T.cycle.coordinate x).2 •
      (T.coordinate T.a - T.coordinate T.b) at he
  rw [T.coordinate_a,T.coordinate_b,T.coordinate_c] at he
  have h₁ := congrArg Prod.fst he
  have h₂ := congrArg Prod.snd he
  simp [Prod.smul_mk] at h₁ h₂
  apply Prod.ext <;> dsimp <;> linarith only [h₁,h₂]

/-- Actual finite target vertices determine their corner ray. -/
theorem ClosedDiscTriangle.cornerAB_eq_through_finite (T : ClosedDiscTriangle) (a b : 𝔻)
    (ha : T.a = discToClosedModel a) (hb : T.b = discToClosedModel b) (hab : a ≠ b) :
    T.cornerRayABAtA a ha = discRayThrough a b hab := by
  apply (discRayThrough_eq hab _ ?_).symm
  apply T.cornerAtA_sideC_finite_subset a ha
  change discToClosedModel b ∈ T.sideC
  rw [← hb,T.mem_sideC_iff_coordinate,T.coordinate_b]
  norm_num

theorem ClosedDiscTriangle.cornerAC_eq_through_finite (T : ClosedDiscTriangle) (a c : 𝔻)
    (ha : T.a = discToClosedModel a) (hc : T.c = discToClosedModel c) (hac : a ≠ c) :
    T.cornerRayACAtA a ha = discRayThrough a c hac := by
  apply (discRayThrough_eq hac _ ?_).symm
  apply T.cornerAtA_sideB_finite_subset a ha
  change discToClosedModel c ∈ T.sideB
  rw [← hc,T.mem_sideB_iff_coordinate,T.coordinate_c]
  norm_num

/-- Angle addition for genuine rays with the middle ray in the actual proper corner. -/
theorem hInteriorAngleMeasure_add_of_mem_proper {z q : ℍ} (R Q S : HRayAt z)
    (hne : R.supportLine ≠ S.supportLine) (hq : q ∈ properHAngleInterior R S)
    (hqQ : q ∈ Q.val) (hqz : q ≠ z) :
    hInteriorAngleMeasure R S = hInteriorAngleMeasure R Q + hInteriorAngleMeasure Q S := by
  obtain ⟨a,b,ha,hb,he⟩ := hAngle_direction_positive_combination R S hne hq
  rw [hInteriorAngleMeasure_eq_direction R S R.directionPoint_mem.1 R.directionPoint_mem.2
      S.directionPoint_mem.1 S.directionPoint_mem.2,
    hInteriorAngleMeasure_eq_direction R Q R.directionPoint_mem.1 R.directionPoint_mem.2 hqQ hqz,
    hInteriorAngleMeasure_eq_direction Q S hqQ hqz S.directionPoint_mem.1 S.directionPoint_mem.2]
  apply angle_eq_angle_add_add_angle_add_of_mem_span (hyperbolicDirection_ne_zero hqz.symm)
  rw [Submodule.mem_span_pair]
  exact ⟨⟨a,ha.le⟩,⟨b,hb.le⟩,he.symm⟩

/-- Distinct actual rays on the same h-line have opposite forward tangent vectors. -/
theorem HRayAt.tangentVector_neg_of_ne_same_support {z : ℍ} (R S : HRayAt z)
    (hL : R.supportLine = S.supportLine) (hne : R ≠ S) : S.tangentVector = -R.tangentVector := by
  have hl (x : ℍ) : R.longitudinal x = S.longitudinal x := by simp only [HRayAt.longitudinal,hL]
  have hcond : (R.longitudinal z < R.longitudinal R.directionPoint) ≠
      (S.longitudinal z < S.longitudinal S.directionPoint) := by
    intro he
    apply hne
    apply Subtype.ext
    ext x
    by_cases hx : x ∈ R.supportLine.carrier
    · have hxS : x ∈ S.supportLine.carrier := hL ▸ hx
      rw [R.mem_iff_longitudinal hx,S.mem_iff_longitudinal hxS]
      simp only [he]
      simp only [hl]
    · have hxS : x ∉ S.supportLine.carrier := hL ▸ hx
      exact iff_of_false (fun h => hx (R.subset_support h)) (fun h => hxS (S.subset_support h))
  by_cases hR : R.longitudinal z < R.longitudinal R.directionPoint
  · have hS : ¬ S.longitudinal z < S.longitudinal S.directionPoint := by
      intro h
      exact hcond (propext ⟨fun _ => h,fun _ => hR⟩)
    have hsR : R.tangentSign = 1 := ite_eq_left hR
    have hsS : S.tangentSign = -1 := ite_eq_right hS
    simp only [HRayAt.tangentVector,hsR,hsS,hL,one_smul,neg_one_smul]
  · have hS : S.longitudinal z < S.longitudinal S.directionPoint := by
      by_contra h
      exact hcond (propext ⟨fun hr => (hR hr).elim,fun hs => (h hs).elim⟩)
    have hsR : R.tangentSign = -1 := ite_eq_right hR
    have hsS : S.tangentSign = 1 := ite_eq_left hS
    simp only [HRayAt.tangentVector,hsR,hsS,hL,one_smul,neg_one_smul,neg_neg]

/-- Equality of actual native rays is determined by their true compactified endpoint. -/
theorem DiscRayAt.eq_of_idealEndpoint_eq {z : 𝔻} (R S : DiscRayAt z)
    (he : R.idealEndpoint = S.idealEndpoint) : R = S := by
  apply (discRayHalfPlaneEquiv z).injective
  apply HRayAt.idealEndpoint_injective
  change R.toHalfPlane.idealEndpoint = S.toHalfPlane.idealEndpoint
  rw [R.toHalfPlane_idealEndpoint,S.toHalfPlane_idealEndpoint,he]

/-- Every actual point of a ray belongs to its genuine closed finite-to-ideal segment. -/
theorem DiscRayAt.point_mem_closedSegment_endpoint {z : 𝔻} (R : DiscRayAt z)
    (w : 𝕔𝔻) (hw : ‖(w : ℂ)‖ = 1) (hE : R.idealEndpoint = closedDiscToExtended w)
    {p : 𝔻} (hp : p ∈ R.val) : discToClosedModel p ∈ closedModelDiscHSegment (discToClosedModel z) w := by
  rw [closedModelDiscHSegment_ray z w hw]
  apply subset_closure
  refine ⟨p,?_,rfl⟩
  rw [← hE,discHRay_eq_of_isDiscHLineRay R.isRay]
  exact hp

/-- Extending the first-to-third side leaves the actual first angle unchanged. -/
theorem ClosedDiscTriangle.idealExtension_alpha (T : ClosedDiscTriangle) (w : 𝕔𝔻)
    (hcS : T.c ∈ closedModelDiscHSegment T.a w) (a b c : 𝔻)
    (ha : T.a = discToClosedModel a) (hb : T.b = discToClosedModel b)
    (hc : T.c = discToClosedModel c) : (T.idealExtension w hcS).alpha = T.alpha := by
  let U := T.idealExtension w hcS
  have haU : U.a = discToClosedModel a := ha
  have hbU : U.b = discToClosedModel b := hb
  have hab : a ≠ b := by intro he; exact T.a_ne_b (ha.trans ((congrArg discToClosedModel he).trans hb.symm))
  have hac : a ≠ c := by intro he; exact T.c_ne_a (hc.trans ((congrArg discToClosedModel he.symm).trans ha.symm))
  have hR : U.cornerRayACAtA a haU = discRayThrough a c hac := by
    apply (discRayThrough_eq hac _ ?_).symm
    apply U.cornerAtA_sideB_finite_subset a haU
    change discToClosedModel c ∈ closedModelDiscHSegment w T.a
    rw [← hc,closedModelDiscHSegment_comm]
    exact hcS
  change U.alpha = T.alpha
  rw [U.alpha_of_finite a haU,T.alpha_of_finite a ha,
    U.cornerAB_eq_through_finite a b haU hbU hab,T.cornerAB_eq_through_finite a b ha hb hab,
    T.cornerAC_eq_through_finite a c ha hc hac,hR]

/-- At the shared finite second vertex, the genuine extended angle splits into the two actual angles. -/
theorem ClosedDiscTriangle.idealExtension_beta_add (T : ClosedDiscTriangle) (w : 𝕔𝔻)
    (hw : ‖(w : ℂ)‖ = 1) (hcS : T.c ∈ closedModelDiscHSegment T.a w) (hcw : T.c ≠ w)
    (a b c : 𝔻) (ha : T.a = discToClosedModel a) (hb : T.b = discToClosedModel b)
    (hc : T.c = discToClosedModel c) :
    (T.idealExtension w hcS).beta = T.beta + (T.idealComplement w hcS hcw).beta := by
  let U := T.idealExtension w hcS
  let V := T.idealComplement w hcS hcw
  let A := U.cycle
  let B := T.cycle
  let C := V.cycle
  have hbA : A.a = discToClosedModel b := hb
  have hbB : B.a = discToClosedModel b := hb
  have hbC : C.a = discToClosedModel b := hb
  have haA : A.c = discToClosedModel a := ha
  have haB : B.c = discToClosedModel a := ha
  have hcB : B.b = discToClosedModel c := hc
  have hcC : C.c = discToClosedModel c := hc
  have hba : b ≠ a := by intro he; exact T.a_ne_b (ha.trans ((congrArg discToClosedModel he.symm).trans hb.symm))
  have hbc : b ≠ c := by intro he; exact T.b_ne_c (hb.trans ((congrArg discToClosedModel he).trans hc.symm))
  let R := A.cornerRayABAtA b hbA
  let S := A.cornerRayACAtA b hbA
  let Q := B.cornerRayABAtA b hbB
  have hR : C.cornerRayABAtA b hbC = R := by
    apply DiscRayAt.eq_of_idealEndpoint_eq
    rw [C.cornerRayABAtA_idealEndpoint b hbC hw,A.cornerRayABAtA_idealEndpoint b hbA hw]
    rfl
  have hS : B.cornerRayACAtA b hbB = S := by
    change B.cornerRayACAtA b hbB = A.cornerRayACAtA b hbA
    rw [B.cornerAC_eq_through_finite b a hbB haB hba,A.cornerAC_eq_through_finite b a hbA haA hba]
  have hQ : C.cornerRayACAtA b hbC = Q := by
    change C.cornerRayACAtA b hbC = B.cornerRayABAtA b hbB
    rw [C.cornerAC_eq_through_finite b c hbC hcC hbc,B.cornerAB_eq_through_finite b c hbB hcB hbc]
  obtain ⟨t,ht0,ht1,htc⟩ := T.idealExtension_coordinate w hcS hcw
  have hcoord : A.halfPlaneCoordinate (discToHalfPlane c) = (t,1-t) := by
    have he := U.cycle_coordinate T.c
    rw [htc] at he
    change A.coordinate T.c = _ at he
    simpa only [hc,ClosedDiscTriangle.halfPlaneCoordinate,ClosedDiscTriangle.discCoordinate,
      halfPlaneToDisc_discToHalfPlane,Prod.fst,Prod.snd,sub_zero] using he
  have hcorner : discToHalfPlane c ∈ properHAngleInterior R.toHalfPlane S.toHalfPlane := by
    rw [A.cornerRayABAtA_toHalfPlane,A.cornerRayACAtA_toHalfPlane]
    apply ((A.finiteHalfPlaneCornerAtDiscA b hbA).mem_interior_iff _).mpr
    rw [hcoord]
    exact ⟨ht0,sub_pos.mpr ht1⟩
  have hproper : R.toHalfPlane.supportLine ≠ S.toHalfPlane.supportLine := by
    intro he
    exact A.cornerAtA_proper b hbA ((R.support_eq_iff S).mpr he)
  have hqQ : discToHalfPlane c ∈ Q.toHalfPlane.val := by
    refine ⟨c,?_,rfl⟩
    change c ∈ (B.cornerRayABAtA b hbB).val
    rw [B.cornerAB_eq_through_finite b c hbB hcB hbc]
    exact discRayThrough_mem b c hbc
  have hqb : discToHalfPlane c ≠ discToHalfPlane b := cayleyHomeomorph.symm.injective.ne hbc.symm
  have he := hInteriorAngleMeasure_add_of_mem_proper R.toHalfPlane Q.toHalfPlane S.toHalfPlane
    hproper hcorner hqQ hqb
  have hβU : U.beta = hInteriorAngleMeasure R.toHalfPlane S.toHalfPlane := by
    change A.alpha = _
    rw [A.alpha_of_finite b hbA,discInteriorAngleMeasure_eq_halfPlane]
  have hβT : T.beta = hInteriorAngleMeasure Q.toHalfPlane S.toHalfPlane := by
    change B.alpha = _
    rw [B.alpha_of_finite b hbB,discInteriorAngleMeasure_eq_halfPlane,hS]
  have hβV : V.beta = hInteriorAngleMeasure R.toHalfPlane Q.toHalfPlane := by
    change C.alpha = _
    rw [C.alpha_of_finite b hbC,discInteriorAngleMeasure_eq_halfPlane,hR,hQ]
  change U.beta = T.beta + V.beta
  rw [hβU,hβT,hβV]
  exact he.trans (add_comm _ _)

/-- The complementary angle at the old third vertex is the actual supplement. -/
theorem ClosedDiscTriangle.idealComplement_alpha (T : ClosedDiscTriangle) (w : 𝕔𝔻)
    (hw : ‖(w : ℂ)‖ = 1) (hcS : T.c ∈ closedModelDiscHSegment T.a w) (hcw : T.c ≠ w)
    (a b c : 𝔻) (ha : T.a = discToClosedModel a) (hb : T.b = discToClosedModel b)
    (hc : T.c = discToClosedModel c) :
    (T.idealComplement w hcS hcw).alpha = Real.pi - T.gamma := by
  let U := T.idealExtension w hcS
  let V := T.idealComplement w hcS hcw
  let A := T.cycle.cycle
  have hcA : A.a = discToClosedModel c := hc
  have hcV : V.a = discToClosedModel c := hc
  have haA : A.b = discToClosedModel a := ha
  have hbA : A.c = discToClosedModel b := hb
  have hbV : V.b = discToClosedModel b := hb
  have hca : c ≠ a := by intro he; exact T.c_ne_a (hc.trans ((congrArg discToClosedModel he).trans ha.symm))
  have hcb : c ≠ b := by intro he; exact T.b_ne_c (hb.trans ((congrArg discToClosedModel he.symm).trans hc.symm))
  let R := A.cornerRayABAtA c hcA
  let Q := A.cornerRayACAtA c hcA
  let S := V.cornerRayACAtA c hcV
  have hQ : V.cornerRayABAtA c hcV = Q := by
    change V.cornerRayABAtA c hcV = A.cornerRayACAtA c hcA
    rw [V.cornerAB_eq_through_finite c b hcV hbV hcb,A.cornerAC_eq_through_finite c b hcA hbA hcb]
  have hcU : T.c ∈ U.sideLineB.closedCarrier :=
    U.sideLineB.closedCarrier_hConvex T.a U.a_mem_sideLineB w U.c_mem_sideLineB hcS
  have hR : R.supportLine = U.sideLineB := by
    rw [A.cornerRayABAtA_support]
    apply DiscLine.eq_of_two_closed_points _ _ T.c_ne_a
      A.a_mem_sideLineC A.b_mem_sideLineC hcU U.a_mem_sideLineB
  have hS : S.supportLine = U.sideLineB := by
    rw [V.cornerRayACAtA_support]
    apply DiscLine.eq_of_two_closed_points _ _ hcw
      V.a_mem_sideLineB V.c_mem_sideLineB hcU U.c_mem_sideLineB
  have hne : R ≠ S := by
    intro he
    have haR : a ∈ R.val := by
      change a ∈ (A.cornerRayABAtA c hcA).val
      rw [A.cornerAB_eq_through_finite c a hcA haA hca]
      exact discRayThrough_mem c a hca
    have haS : a ∈ S.val := he ▸ haR
    have hEnd : S.idealEndpoint = closedDiscToExtended w := V.cornerRayACAtA_idealEndpoint c hcV hw
    have hseg : T.a ∈ closedModelDiscHSegment T.c w := by
      have h := S.point_mem_closedSegment_endpoint w hw hEnd haS
      rwa [← ha,← hc] at h
    obtain ⟨t,ht0,_,htc⟩ := T.idealExtension_coordinate w hcS hcw
    rw [U.mem_closedSegment_iff_coordinate,htc] at hseg
    change U.coordinate U.a ∈ segment ℝ (0,t) (U.coordinate U.c) at hseg
    rw [U.coordinate_a,U.coordinate_c] at hseg
    have hp : segment ℝ ((0,t) : ℝ × ℝ) (0,1) ⊆ {p : ℝ × ℝ | 0 < p.2} :=
      (convex_halfSpace_gt (LinearMap.snd ℝ ℝ ℝ).isLinear (0 : ℝ)).segment_subset ht0 zero_lt_one
    exact (lt_irrefl (0 : ℝ)) (hp hseg)
  have hLH : R.toHalfPlane.supportLine = S.toHalfPlane.supportLine := (R.support_eq_iff S).mp (hR.trans hS.symm)
  have hneH : R.toHalfPlane ≠ S.toHalfPlane := fun he => hne ((discRayHalfPlaneEquiv c).injective he)
  have ht := R.toHalfPlane.tangentVector_neg_of_ne_same_support S.toHalfPlane hLH hneH
  have hγ : T.gamma = hInteriorAngleMeasure R.toHalfPlane Q.toHalfPlane := by
    change A.alpha = _
    rw [A.alpha_of_finite c hcA,discInteriorAngleMeasure_eq_halfPlane]
  have hα : V.alpha = hInteriorAngleMeasure Q.toHalfPlane S.toHalfPlane := by
    rw [V.alpha_of_finite c hcV,discInteriorAngleMeasure_eq_halfPlane,hQ]
  change V.alpha = _
  rw [hα,hγ,hInteriorAngleMeasure,hInteriorAngleMeasure,ht,angle_neg_right,angle_comm]

/-- Subtracting the genuine complementary area proves the area theorem for all finite vertices. -/
theorem ClosedDiscTriangle.halfPlane_area_eq_angle_defect_of_finite (T : ClosedDiscTriangle)
    (ha : ‖(T.a : ℂ)‖ < 1) (hb : ‖(T.b : ℂ)‖ < 1) (hc : ‖(T.c : ℂ)‖ < 1) :
    volume T.halfPlaneInterior = ENNReal.ofReal (Real.pi - T.alpha - T.beta - T.gamma) := by
  let a := closedDiscFinitePoint T.a ha
  let b := closedDiscFinitePoint T.b hb
  let c := closedDiscFinitePoint T.c hc
  have haD : T.a = discToClosedModel a := (closedDiscFinitePoint_spec T.a ha).symm
  have hbD : T.b = discToClosedModel b := (closedDiscFinitePoint_spec T.b hb).symm
  have hcD : T.c = discToClosedModel c := (closedDiscFinitePoint_spec T.c hc).symm
  have hac : a ≠ c := by
    intro he
    exact T.c_ne_a (hcD.trans ((congrArg discToClosedModel he.symm).trans haD.symm))
  obtain ⟨w,hw,hcS⟩ := discRayThrough_exists_closed_ideal_extension a c hac
  rw [← haD,← hcD] at hcS
  have hcw : T.c ≠ w := by intro he; rw [he,hw] at hc; exact (lt_irrefl (1 : ℝ)) hc
  let U := T.idealExtension w hcS
  let V := T.idealComplement w hcS hcw
  have hU : volume U.halfPlaneInterior = ENNReal.ofReal (Real.pi - U.alpha - U.beta - U.gamma) :=
    U.halfPlane_area_eq_angle_defect_of_ideal hw
  have hV : volume V.halfPlaneInterior = ENNReal.ofReal (Real.pi - V.alpha - V.beta - V.gamma) :=
    V.halfPlane_area_eq_angle_defect_of_ideal hw
  have harea : volume U.halfPlaneInterior = volume T.halfPlaneInterior + volume V.halfPlaneInterior :=
    T.idealExtension_area_add w hcS hcw
  have hTle : volume T.halfPlaneInterior ≤ volume U.halfPlaneInterior := by
    rw [harea]
    exact le_self_add
  have hTtop : volume T.halfPlaneInterior ≠ ⊤ := ne_top_of_le_ne_top (hU ▸ ENNReal.ofReal_ne_top) hTle
  have hVtop : volume V.halfPlaneInterior ≠ ⊤ := hV ▸ ENNReal.ofReal_ne_top
  have hα := T.idealExtension_alpha w hcS a b c haD hbD hcD
  have hβ := T.idealExtension_beta_add w hw hcS hcw a b c haD hbD hcD
  have hγ := T.idealComplement_alpha w hw hcS hcw a b c haD hbD hcD
  have hγU : U.gamma = 0 := U.gamma_of_ideal hw
  have hγV : V.gamma = 0 := V.gamma_of_ideal hw
  have hUnonneg : 0 ≤ Real.pi - U.alpha - U.beta - U.gamma := by linarith only [U.angle_sum_lt_pi]
  have hVnonneg : 0 ≤ Real.pi - V.alpha - V.beta - V.gamma := by linarith only [V.angle_sum_lt_pi]
  have hTnonneg : 0 ≤ Real.pi - T.alpha - T.beta - T.gamma := by linarith only [T.angle_sum_lt_pi]
  have he := congrArg ENNReal.toReal harea
  rw [ENNReal.toReal_add hTtop hVtop,hU,hV,ENNReal.toReal_ofReal hUnonneg,
    ENNReal.toReal_ofReal hVnonneg] at he
  apply (ENNReal.toReal_eq_toReal_iff' hTtop ENNReal.ofReal_ne_top).mp
  rw [ENNReal.toReal_ofReal hTnonneg]
  change U.alpha = T.alpha at hα
  change U.beta = T.beta + V.beta at hβ
  change V.alpha = Real.pi - T.gamma at hγ
  linarith only [he,hα,hβ,hγ,hγU,hγV]

/-- The genuine density area of every finite-or-ideal native triangle is its angle defect. -/
theorem ClosedDiscTriangle.area_eq_angle_defect (T : ClosedDiscTriangle) :
    discHyperbolicArea T.interior = ENNReal.ofReal (Real.pi - T.alpha - T.beta - T.gamma) := by
  by_cases ha : ‖(T.a : ℂ)‖ < 1
  · by_cases hb : ‖(T.b : ℂ)‖ < 1
    · by_cases hc : ‖(T.c : ℂ)‖ < 1
      · rw [T.area_eq_halfPlane_volume]
        exact T.halfPlane_area_eq_angle_defect_of_finite ha hb hc
      · exact T.area_eq_angle_defect_of_exists_ideal (Or.inr (Or.inr (le_antisymm T.c.norm_le_one (not_lt.mp hc))))
    · exact T.area_eq_angle_defect_of_exists_ideal (Or.inr (Or.inl (le_antisymm T.b.norm_le_one (not_lt.mp hb))))
  · exact T.area_eq_angle_defect_of_exists_ideal (Or.inl (le_antisymm T.a.norm_le_one (not_lt.mp ha)))

/-- In the genuine closed half-plane model, including all ideal vertices. -/
theorem ClosedHTriangle.area_eq_angle_defect (T : ClosedHTriangle) :
    volume T.interior = ENNReal.ofReal (Real.pi - T.alpha - T.beta - T.gamma) := by
  have he := T.toDiscTriangle.area_eq_angle_defect
  rw [T.toDiscTriangle.area_eq_halfPlane_volume] at he
  exact he

/-- The area theorem for the original all-finite native disc triangles. -/
theorem DiscTriangle.area_eq_angle_defect (T : DiscTriangle) :
    discHyperbolicArea T.interior = ENNReal.ofReal (Real.pi - T.alpha - T.beta - T.gamma) := by
  have he := T.toClosedDiscTriangle.area_eq_angle_defect
  rw [T.interior_toClosedDiscTriangle,T.closed_angles.1,T.closed_angles.2.1,T.closed_angles.2.2] at he
  exact he

/-- The area theorem for the original all-finite upper-half-plane triangles. -/
theorem HTriangle.area_eq_angle_defect (T : HTriangle) :
    volume T.interior = ENNReal.ofReal (Real.pi - T.alpha - T.beta - T.gamma) := by
  have he := T.toClosedHTriangle.area_eq_angle_defect
  rw [T.interior_toClosedHTriangle,T.closed_angles.1,T.closed_angles.2.1,T.closed_angles.2.2] at he
  exact he

/-- The real area is exactly the positive angle defect, with no truncation ambiguity. -/
theorem ClosedDiscTriangle.area_toReal_eq_angle_defect (T : ClosedDiscTriangle) :
    (discHyperbolicArea T.interior).toReal = Real.pi - T.alpha - T.beta - T.gamma := by
  rw [T.area_eq_angle_defect,ENNReal.toReal_ofReal]
  linarith only [T.angle_sum_lt_pi]

/-- In particular every actual finite-or-ideal hyperbolic triangle has finite positive area. -/
theorem ClosedDiscTriangle.area_pos_lt_top (T : ClosedDiscTriangle) :
    0 < discHyperbolicArea T.interior ∧ discHyperbolicArea T.interior < ⊤ := by
  rw [T.area_eq_angle_defect]
  exact ⟨ENNReal.ofReal_pos.mpr (by linarith only [T.angle_sum_lt_pi]),ENNReal.ofReal_lt_top⟩

/-- Membership in the genuine closed triangle is exactly the non-strict affine triangle condition. -/
theorem ClosedDiscTriangle.mem_closedCarrier_iff_coordinate (T : ClosedDiscTriangle) (x : 𝕔𝔻) :
    x ∈ T.closedCarrier ↔ 0 ≤ (T.coordinate x).1 ∧ 0 ≤ (T.coordinate x).2 ∧
      (T.coordinate x).1 + (T.coordinate x).2 ≤ 1 := by
  change x ∈ T.closedCarrier ↔ T.coordinate x ∈ standardClosedTriangle
  rw [← T.coordinate_image_closedCarrier]
  exact (T.coordinateHomeomorph.injective.comp closedKleinCoordinate_injective).mem_set_image.symm

/-- Including the actual three finite side traces does not change the density area. -/
theorem ClosedDiscTriangle.halfPlane_closedCarrier_area_eq_interior (T : ClosedDiscTriangle) :
    volume {z : ℍ | discToClosedModel (halfPlaneToDisc z) ∈ T.closedCarrier} = volume T.halfPlaneInterior := by
  have hnull : volume (T.sideLineA.toHalfPlane.carrier ∪
      T.sideLineB.toHalfPlane.carrier ∪ T.sideLineC.toHalfPlane.carrier) = 0 :=
    measure_union_null (measure_union_null T.sideLineA.toHalfPlane.volume_zero T.sideLineB.toHalfPlane.volume_zero)
      T.sideLineC.toHalfPlane.volume_zero
  apply measure_congr
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp hnull] with z hz
  have hA : z ∉ T.sideLineA.toHalfPlane.carrier := fun h => hz (Or.inl (Or.inl h))
  have hB : z ∉ T.sideLineB.toHalfPlane.carrier := fun h => hz (Or.inl (Or.inr h))
  have hC : z ∉ T.sideLineC.toHalfPlane.carrier := fun h => hz (Or.inr h)
  have hn1 : (T.halfPlaneCoordinate z).1 ≠ 0 := fun he => hB ((T.halfPlaneCoordinate_second_line z).mp he)
  have hn2 : (T.halfPlaneCoordinate z).2 ≠ 0 := fun he => hC ((T.halfPlaneCoordinate_first_line z).mp he)
  have hn3 : (T.halfPlaneCoordinate z).1 + (T.halfPlaneCoordinate z).2 ≠ 1 :=
    fun he => hA ((T.halfPlaneCoordinate_opposite_line z).mp he)
  apply propext
  rw [T.mem_closedCarrier_iff_coordinate,T.mem_halfPlaneInterior_iff]
  change (0 ≤ (T.halfPlaneCoordinate z).1 ∧ 0 ≤ (T.halfPlaneCoordinate z).2 ∧
    (T.halfPlaneCoordinate z).1 + (T.halfPlaneCoordinate z).2 ≤ 1) ↔ _
  constructor
  · rintro ⟨h1,h2,h3⟩
    exact ⟨lt_of_le_of_ne h1 (Ne.symm hn1),lt_of_le_of_ne h2 (Ne.symm hn2),lt_of_le_of_ne h3 hn3⟩
  · rintro ⟨h1,h2,h3⟩
    exact ⟨h1.le,h2.le,h3.le⟩

/-- The genuine finite part of the closed native triangle is measurable. -/
theorem ClosedDiscTriangle.closedCarrier_finite_measurable (T : ClosedDiscTriangle) :
    MeasurableSet {z : 𝔻 | discToClosedModel z ∈ T.closedCarrier} := by
  have hcoord : Continuous T.discCoordinate := by
    have he : T.discCoordinate = fun z : 𝔻 => T.ambientCoordinateHomeomorph (z : ℂ) := by
      funext z
      exact (T.ambientCoordinateHomeomorph_disc z).symm
    rw [he]
    exact T.ambientCoordinateHomeomorph.continuous.comp Complex.UnitDisc.continuous_coe
  have hEq : {z : 𝔻 | discToClosedModel z ∈ T.closedCarrier} = T.discCoordinate ⁻¹' standardClosedTriangle := by
    ext z
    exact T.mem_closedCarrier_iff_coordinate (discToClosedModel z)
  rw [hEq]
  exact standardClosedTriangle_isClosed.measurableSet.preimage hcoord.measurable

/-- also for the whole genuine closed native region, with its actual sides included. -/
theorem ClosedDiscTriangle.closedCarrier_area_eq_angle_defect (T : ClosedDiscTriangle) :
    discHyperbolicArea {z : 𝔻 | discToClosedModel z ∈ T.closedCarrier} =
      ENNReal.ofReal (Real.pi - T.alpha - T.beta - T.gamma) := by
  rw [discHyperbolicArea_eq_halfPlane_volume _ T.closedCarrier_finite_measurable]
  have he : discToHalfPlane '' {z : 𝔻 | discToClosedModel z ∈ T.closedCarrier} =
      {z : ℍ | discToClosedModel (halfPlaneToDisc z) ∈ T.closedCarrier} := by
    ext z
    constructor
    · rintro ⟨x,hx,rfl⟩
      change discToClosedModel (halfPlaneToDisc (discToHalfPlane x)) ∈ T.closedCarrier
      rwa [halfPlaneToDisc_discToHalfPlane]
    · intro hz
      exact ⟨halfPlaneToDisc z,hz,discToHalfPlane_halfPlaneToDisc z⟩
  rw [he,T.halfPlane_closedCarrier_area_eq_interior,← T.area_eq_halfPlane_volume,T.area_eq_angle_defect]

end
end LowDimensionalTopology.Geometry.Hyperbolic
