/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Euclidean.InnerProduct.Gram
public import LowDimensionalTopology.Geometry.Hyperbolic.Geodesic.SideNormalGeometry
public import LowDimensionalTopology.Geometry.Hyperbolic.ModelMaps.PoincareKlein.Ambient
public import LowDimensionalTopology.Geometry.Euclidean.InnerProduct.ComplexAffine
public import LowDimensionalTopology.Geometry.Hyperbolic.Triangle.TriangleIncenter
public import LowDimensionalTopology.Geometry.Hyperbolic.Triangle.IdealTriangleData
@[expose] public section
open Set InnerProductGeometry
open scoped UpperHalfPlane Complex.UnitDisc
namespace LowDimensionalTopology.Geometry.Hyperbolic
noncomputable section


/-- The finite-model normalized side normal remains nonzero, including vertical lines. -/
theorem HalfPlaneLine.incenterNormal_ne_zero (L : HalfPlaneLine) : L.incenterNormal ≠ 0 := by
  cases L with
  | vertical a =>
    intro h
    have he := congrArg Complex.im h
    norm_num [HalfPlaneLine.incenterNormal] at he
  | circle c r hr =>
    intro h
    have hre := congrArg Complex.re h
    have him := congrArg Complex.im h
    simp only [HalfPlaneLine.incenterNormal,Complex.zero_re,Complex.zero_im] at hre him
    have hc : c = 0 := (div_eq_zero_iff.mp him).resolve_right hr.ne'
    rw [hc] at hre
    have hz : (1 : ℝ) + r ^ 2 = 0 := by
      exact (div_eq_zero_iff.mp (by simpa using hre)).resolve_right (by positivity)
    nlinarith

def DiscLine.incenterNormal (L : DiscLine) : ℂ := L.toHalfPlane.incenterNormal

def DiscLine.incenterOffset (L : DiscLine) : ℝ := L.toHalfPlane.incenterOffset

theorem DiscLine.incenter_affine_eq_zero_iff (L : DiscLine) (z : 𝔻) :
    inner ℝ L.incenterNormal (kleinCoordinate z) = L.incenterOffset ↔ z ∈ L.carrier := by
  rw [L.mem_carrier]
  have he := L.toHalfPlane.incenter_affine_eq_zero_iff (discToHalfPlane z)
  unfold hKleinAffine at he
  rw [sub_eq_zero] at he
  simpa only [DiscLine.incenterNormal,DiscLine.incenterOffset,halfPlaneKleinCoordinate,
    halfPlaneToDisc_discToHalfPlane] using he

/-- The normalized affine equation is exact also at the genuine ideal endpoints. -/
theorem DiscLine.incenter_closed_affine_eq_zero_iff (L : DiscLine) (z : 𝕔𝔻) :
    inner ℝ L.incenterNormal (closedKleinCoordinate z) = L.incenterOffset ↔ z ∈ L.closedCarrier := by
  obtain ⟨n,t,hn,hL⟩ := L.closedKlein_affine_equation
  obtain ⟨a,b,ha,hb,hab⟩ := L.toHalfPlane.exists_two_points
  let u := halfPlaneToDisc a
  let v := halfPlaneToDisc b
  have hu : u ∈ L.carrier := (L.mem_carrier _).mpr (by simpa only [u,discToHalfPlane_halfPlaneToDisc] using ha)
  have hv : v ∈ L.carrier := (L.mem_carrier _).mpr (by simpa only [v,discToHalfPlane_halfPlaneToDisc] using hb)
  have huClosed : discToClosedModel u ∈ L.closedCarrier := subset_closure (mem_image_of_mem _ hu)
  have hvClosed : discToClosedModel v ∈ L.closedCarrier := subset_closure (mem_image_of_mem _ hv)
  have huv : kleinCoordinate u ≠ kleinCoordinate v := by
    intro he
    exact hab ((show Function.Injective halfPlaneToDisc from cayleyHomeomorph.injective)
      (kleinCoordinate_injective he))
  have hnu := (L.incenter_affine_eq_zero_iff u).mpr hu
  have hnv := (L.incenter_affine_eq_zero_iff v).mpr hv
  have hmu := (hL (discToClosedModel u)).mp huClosed
  have hmv := (hL (discToClosedModel v)).mp hvClosed
  rw [closedKleinCoordinate_disc_inclusion] at hmu hmv
  exact (_root_.LowDimensionalTopology.Geometry.Euclidean.complex_affine_equations_iff_of_two_points
    L.toHalfPlane.incenterNormal_ne_zero hn huv
    hnu hnv hmu hmv).trans (hL z).symm

/-- The normalized genuine line equation evaluated in the closed Klein chart. -/
def closedDiscKleinAffine (n : ℂ) (t : ℝ) (p : 𝕔𝔻) : ℝ := inner ℝ n (closedKleinCoordinate p) - t

theorem ClosedDiscTriangle.kleinAffine_reconstruction (T : ClosedDiscTriangle) (n : ℂ) (t : ℝ) (p : 𝕔𝔻) :
    closedDiscKleinAffine n t p = (1 - (T.coordinate p).1 - (T.coordinate p).2) * closedDiscKleinAffine n t T.a +
      (T.coordinate p).1 * closedDiscKleinAffine n t T.b + (T.coordinate p).2 * closedDiscKleinAffine n t T.c := by
  unfold closedDiscKleinAffine
  rw [T.klein_reconstruction p]
  simp only [inner_add_right,inner_smul_right,inner_sub_right]
  ring

theorem ClosedDiscTriangle.exists_equal_absolute_side_equations (T : ClosedDiscTriangle)
    (nA nB nC : ℂ) (tA tB tC : ℝ)
    (hA : ∀ p : 𝕔𝔻, p ∈ T.sideLineA.closedCarrier ↔ closedDiscKleinAffine nA tA p = 0)
    (hB : ∀ p : 𝕔𝔻, p ∈ T.sideLineB.closedCarrier ↔ closedDiscKleinAffine nB tB p = 0)
    (hC : ∀ p : 𝕔𝔻, p ∈ T.sideLineC.closedCarrier ↔ closedDiscKleinAffine nC tC p = 0) :
    ∃ z ∈ T.interior, |closedDiscKleinAffine nA tA (discToClosedModel
      z)| = |closedDiscKleinAffine nB tB (discToClosedModel z)| ∧
      |closedDiscKleinAffine nB tB (discToClosedModel z)| = |closedDiscKleinAffine nC tC (discToClosedModel z)| := by
  have hbA : T.b ∈ T.sideLineA.closedCarrier := (existsUnique_discLine_closedCarrier T.b T.c
    T.b_ne_c).exists.choose_spec.1
  have hcA : T.c ∈ T.sideLineA.closedCarrier := (existsUnique_discLine_closedCarrier T.b T.c
    T.b_ne_c).exists.choose_spec.2
  have haC : T.a ∈ T.sideLineC.closedCarrier := (existsUnique_discLine_closedCarrier T.a T.b
    T.a_ne_b).exists.choose_spec.1
  have hbC : T.b ∈ T.sideLineC.closedCarrier := (existsUnique_discLine_closedCarrier T.a T.b
    T.a_ne_b).exists.choose_spec.2
  let u := |closedDiscKleinAffine nA tA T.a|
  let v := |closedDiscKleinAffine nB tB T.b|
  let w := |closedDiscKleinAffine nC tC T.c|
  have hu : 0 < u := abs_pos.mpr (fun h => T.noncollinear ⟨T.sideLineA,(hA _).mpr h,hbA,hcA⟩)
  have hv : 0 < v := abs_pos.mpr (fun h => T.b_not_mem_sideLineB ((hB _).mpr h))
  have hw : 0 < w := abs_pos.mpr (fun h => T.noncollinear ⟨T.sideLineC,haC,hbC,(hC _).mpr h⟩)
  let D := u * v + u * w + v * w
  have hD : 0 < D := by dsimp [D]; positivity
  let x := u * w / D
  let y := u * v / D
  have hxy : (x,y) ∈ standardOpenTriangle := by
    refine ⟨div_pos (mul_pos hu hw) hD, div_pos (mul_pos hu hv) hD, ?_⟩
    change u * w / D + u * v / D < 1
    rw [← add_div, div_lt_one hD]
    dsimp [D]
    nlinarith [mul_pos hv hw]
  obtain ⟨z, hz, hcoord⟩ : (x,y) ∈ T.discCoordinate '' T.interior := by
    rw [T.discCoordinate_image_interior]
    exact hxy
  have hAzB : closedDiscKleinAffine nA tA T.b = 0 := (hA _).mp hbA
  have hAzC : closedDiscKleinAffine nA tA T.c = 0 :=
    (hA _).mp hcA
  have hBzA : closedDiscKleinAffine nB tB T.a = 0 :=
    (hB _).mp T.a_mem_sideLineB
  have hBzC : closedDiscKleinAffine nB tB T.c = 0 := (hB _).mp T.c_mem_sideLineB
  have hCzA : closedDiscKleinAffine nC tC T.a = 0 := (hC _).mp haC
  have hCzB : closedDiscKleinAffine nC tC T.b = 0 :=
    (hC _).mp hbC
  have heA : closedDiscKleinAffine nA tA (discToClosedModel z) = (v * w / D) * closedDiscKleinAffine nA tA T.a := by
    rw [T.kleinAffine_reconstruction, show T.coordinate (discToClosedModel z) = (x,y) from hcoord, hAzB, hAzC]
    dsimp only [x,y]
    have he : 1 - u * w / D - u * v / D = v * w / D := by
      field_simp
      dsimp [D]
      ring
    rw [he]
    ring
  have heB : closedDiscKleinAffine nB tB (discToClosedModel z) = x * closedDiscKleinAffine nB tB T.b := by
    rw [T.kleinAffine_reconstruction, show T.coordinate (discToClosedModel z) = (x,y) from hcoord, hBzA, hBzC]
    ring
  have heC : closedDiscKleinAffine nC tC (discToClosedModel z) = y * closedDiscKleinAffine nC tC T.c := by
    rw [T.kleinAffine_reconstruction, show T.coordinate (discToClosedModel z) = (x,y) from hcoord, hCzA, hCzB]
    ring
  have heAx : |closedDiscKleinAffine nA tA (discToClosedModel z)| = u * v * w / D := by
    rw [heA, abs_mul, abs_of_pos (div_pos (mul_pos hv hw) hD)]
    change v * w / D * u = _
    ring
  have heBx : |closedDiscKleinAffine nB tB (discToClosedModel z)| = u * v * w / D := by
    rw [heB, abs_mul, abs_of_pos (div_pos (mul_pos hu hw) hD)]
    change u * w / D * v = _
    ring
  have heCx : |closedDiscKleinAffine nC tC (discToClosedModel z)| = u * v * w / D := by
    rw [heC, abs_mul, abs_of_pos (div_pos (mul_pos hu hv) hD)]
    change u * v / D * w = _
    ring
  exact ⟨z,hz,heAx.trans heBx.symm,heBx.trans heCx.symm⟩

theorem DiscLine.sinh_pointDist_closed_incenter_affine (L : DiscLine) (z : 𝔻) :
    Real.sinh (L.pointDist z) =
      |closedDiscKleinAffine L.incenterNormal L.incenterOffset (discToClosedModel z)| *
        halfPlaneKleinHeight (discToHalfPlane z) := by
  rw [L.pointDist_eq_halfPlane,L.toHalfPlane.sinh_pointDist_incenter_affine]
  simp only [hKleinAffine,closedDiscKleinAffine,DiscLine.incenterNormal,DiscLine.incenterOffset,
    closedKleinCoordinate_disc_inclusion,halfPlaneKleinCoordinate,halfPlaneToDisc_discToHalfPlane]

theorem DiscLine.closed_incenter_affine_zero_iff (L : DiscLine) (p : 𝕔𝔻) :
    closedDiscKleinAffine L.incenterNormal L.incenterOffset p = 0 ↔ p ∈ L.closedCarrier := by
  unfold closedDiscKleinAffine
  rw [sub_eq_zero]
  exact L.incenter_closed_affine_eq_zero_iff p

/-- A genuine internal point equidistant from all three sides, with arbitrary finite or ideal vertices. -/
theorem ClosedDiscTriangle.exists_equidistant_side_point (T : ClosedDiscTriangle) :
    ∃ z ∈ T.interior, T.sideLineA.pointDist z = T.sideLineB.pointDist z ∧
      T.sideLineB.pointDist z = T.sideLineC.pointDist z := by
  obtain ⟨z,hz,hab,hbc⟩ := T.exists_equal_absolute_side_equations
    T.sideLineA.incenterNormal T.sideLineB.incenterNormal T.sideLineC.incenterNormal
    T.sideLineA.incenterOffset T.sideLineB.incenterOffset T.sideLineC.incenterOffset
    (fun p => (T.sideLineA.closed_incenter_affine_zero_iff p).symm)
    (fun p => (T.sideLineB.closed_incenter_affine_zero_iff p).symm)
    (fun p => (T.sideLineC.closed_incenter_affine_zero_iff p).symm)
  refine ⟨z,hz,?_,?_⟩
  · apply Real.sinh_injective
    rw [DiscLine.sinh_pointDist_closed_incenter_affine,DiscLine.sinh_pointDist_closed_incenter_affine,hab]
  · apply Real.sinh_injective
    rw [DiscLine.sinh_pointDist_closed_incenter_affine,DiscLine.sinh_pointDist_closed_incenter_affine,hbc]

def ClosedDiscTriangle.incenter (T : ClosedDiscTriangle) : 𝔻 := T.exists_equidistant_side_point.choose

theorem ClosedDiscTriangle.incenter_mem_interior (T : ClosedDiscTriangle) : T.incenter ∈ T.interior :=
  T.exists_equidistant_side_point.choose_spec.1

theorem ClosedDiscTriangle.incenter_equidistant (T : ClosedDiscTriangle) :
    T.sideLineA.pointDist T.incenter = T.sideLineB.pointDist T.incenter ∧
      T.sideLineB.pointDist T.incenter = T.sideLineC.pointDist T.incenter :=
  T.exists_equidistant_side_point.choose_spec.2

/-- Transport uses the native half-plane density path distance, retaining ideal vertices. -/
def ClosedHTriangle.incenter (T : ClosedHTriangle) : ℍ := discToHalfPlane T.toDiscTriangle.incenter

theorem ClosedHTriangle.incenter_mem_interior (T : ClosedHTriangle) : T.incenter ∈ T.interior := by
  change halfPlaneToDisc (discToHalfPlane T.toDiscTriangle.incenter) ∈ T.toDiscTriangle.interior
  rw [halfPlaneToDisc_discToHalfPlane]
  exact T.toDiscTriangle.incenter_mem_interior

theorem HTriangle.hyperbolicDirection_positive_combination (T : HTriangle) {z : ℍ}
    (hp : 0 < (T.coordinate z).1 ∧ 0 < (T.coordinate z).2) :
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ hyperbolicDirection T.a z =
      a • hyperbolicDirection T.a T.b + b • hyperbolicDirection T.a T.c := by
  have hDq := hKleinDenominator_pos z
  have hDb := hKleinDenominator_pos T.b
  have hDc := hKleinDenominator_pos T.c
  refine ⟨(T.coordinate z).1 * hKleinDenominator z / hKleinDenominator T.b,
    (T.coordinate z).2 * hKleinDenominator z / hKleinDenominator T.c,
    div_pos (mul_pos hp.1 hDq) hDb,div_pos (mul_pos hp.2 hDq) hDc,?_⟩
  have he := congrArg (fun v : ℂ => hKleinDenominator z • v) (T.normalizedDirection_reconstruction z)
  simp only [hNormalizedDirection,smul_add,smul_smul,mul_inv_cancel₀ hDq.ne',one_smul] at he
  simpa only [div_eq_mul_inv,mul_comm,mul_left_comm] using he

theorem HTriangle.equidistant_bisects_angleA_of_corner (T : HTriangle) {z : ℍ} (hz : z ∈ T.angleInteriorA)
    (heq : T.sideLineB.pointDist z = T.sideLineC.pointDist z) :
    angle (hyperbolicDirection T.a T.b) (hyperbolicDirection T.a z) =
      angle (hyperbolicDirection T.a z) (hyperbolicDirection T.a T.c) := by
  have hzBC := T.angleInteriorA_eq_halfPlanes ▸ hz
  have hx := mem_image_of_mem T.coordinate hzBC.1
  have hy := mem_image_of_mem T.coordinate hzBC.2
  rw [T.coordinate_image_halfPlaneB] at hx
  rw [T.coordinate_image_halfPlaneC] at hy
  have hp : 0 < (T.coordinate z).1 ∧ 0 < (T.coordinate z).2 := ⟨hx.2,hy.2⟩
  have hza : T.a ≠ z := by
    intro he
    rw [← he,T.coordinate_a] at hp
    exact lt_irrefl 0 hp.1
  have hsC := T.rayAB.sinh_pointDist_direction T.b_mem_rayAB T.a_ne_b.symm z hza.symm
  have hsB := T.rayAC.sinh_pointDist_direction T.c_mem_rayAC T.c_ne_a z hza.symm
  rw [T.support_AC_eq] at hsB
  change Real.sinh (T.sideLineC.pointDist z) = _ at hsC
  have hs : Real.sin (angle (hyperbolicDirection T.a T.b) (hyperbolicDirection T.a z)) =
      Real.sin (angle (hyperbolicDirection T.a T.c) (hyperbolicDirection T.a z)) := by
    apply mul_right_cancel₀ (ne_of_gt (Real.sinh_pos_iff.mpr (dist_pos.mpr hza)))
    exact hsC.symm.trans ((congrArg Real.sinh heq.symm).trans hsB)
  obtain ⟨a,b,ha,hb,he⟩ := T.hyperbolicDirection_positive_combination hp
  have hc : complexCross (hyperbolicDirection T.a T.b) (hyperbolicDirection T.a T.c) ≠ 0 := by
    have hspos := Real.sin_pos_of_pos_of_lt_pi T.angles_mem_Ioo.1.1 T.angles_mem_Ioo.1.2
    have hangle := hInteriorAngleMeasure_eq_direction T.rayAB T.rayAC
      T.b_mem_rayAB T.a_ne_b.symm T.c_mem_rayAC T.c_ne_a
    change T.alpha = _ at hangle
    rw [hangle,complex_sin_angle_cross (hyperbolicDirection_ne_zero T.a_ne_b)
      (hyperbolicDirection_ne_zero T.c_ne_a.symm)] at hspos
    intro hzero
    rw [hzero,abs_zero,zero_div] at hspos
    exact lt_irrefl 0 hspos
  exact complex_angle_bisector_of_positive_combination
    (hyperbolicDirection_ne_zero T.a_ne_b) (hyperbolicDirection_ne_zero T.c_ne_a.symm)
    (hyperbolicDirection_ne_zero hza) ⟨ha,hb⟩ hc he hs

/-- Actual equidistance inside a proper ray angle gives the actual internal angle bisection. -/
theorem hAngle_equidistant_bisects {z q : ℍ} (R S : HRayAt z)
    (hne : R.supportLine ≠ S.supportLine) (hzq : z ≠ q)
    (hq : q ∈ properHAngleInterior R S)
    (heq : R.supportLine.pointDist q = S.supportLine.pointDist q) :
    hInteriorAngleMeasure R (hRayThrough z q hzq) =
      hInteriorAngleMeasure (hRayThrough z q hzq) S := by
  have hRn : R.directionPoint ≠ z := R.directionPoint_mem.2
  have hSn : S.directionPoint ≠ z := S.directionPoint_mem.2
  let T : HTriangle :=
    { a := z, b := R.directionPoint, c := S.directionPoint
      noncollinear := by
        rintro ⟨L,hz,hR,hS⟩
        have hLR : L = R.supportLine := L.eq_of_two_points R.supportLine
          hRn.symm hz hR R.start_mem_support (R.subset_support R.directionPoint_mem.1)
        have hLS : L = S.supportLine := L.eq_of_two_points S.supportLine
          hSn.symm hz hS S.start_mem_support (S.subset_support S.directionPoint_mem.1)
        exact hne (hLR.symm.trans hLS) }
  have hR : T.rayAB = R := hRayThrough_eq hRn.symm R R.directionPoint_mem.1
  have hS : T.rayAC = S := hRayThrough_eq hSn.symm S S.directionPoint_mem.1
  have hqi : q ∈ T.angleInteriorA := by
    change q ∈ properHAngleInterior T.rayAB T.rayAC
    rwa [hR,hS]
  have heqd : T.sideLineB.pointDist q = T.sideLineC.pointDist q := by
    rw [← T.support_AC_eq]
    change T.rayAC.supportLine.pointDist q = T.rayAB.supportLine.pointDist q
    rw [hR,hS]
    exact heq.symm
  have hb := T.equidistant_bisects_angleA_of_corner hqi heqd
  rw [hInteriorAngleMeasure_eq_direction R (hRayThrough z q hzq)
      R.directionPoint_mem.1 R.directionPoint_mem.2 (hRayThrough_mem z q hzq) hzq.symm,
    hInteriorAngleMeasure_eq_direction (hRayThrough z q hzq) S
      (hRayThrough_mem z q hzq) hzq.symm S.directionPoint_mem.1 S.directionPoint_mem.2]
  exact hb

theorem ClosedDiscTriangle.incenter_interior_coordinates (T : ClosedDiscTriangle) {q : 𝔻}
    (hq : q ∈ T.interior) : 0 < (T.discCoordinate q).1 ∧ 0 < (T.discCoordinate q).2 ∧
      (T.discCoordinate q).1 + (T.discCoordinate q).2 < 1 := by
  have h := mem_image_of_mem T.discCoordinate hq
  rw [T.discCoordinate_image_interior] at h
  exact h

theorem ClosedDiscTriangle.finite_vertex_ne_of_mem_interior (T : ClosedDiscTriangle) (a q : 𝔻)
    (ha : T.a = discToClosedModel a) (hq : q ∈ T.interior) : a ≠ q := by
  have h0 : T.discCoordinate a = (0,0) := by
    change T.coordinate (discToClosedModel a) = _
    rw [← ha,T.coordinate_a]
  have hp := T.incenter_interior_coordinates hq
  intro he
  rw [← he,h0] at hp
  exact lt_irrefl 0 hp.1

/-- At a finite vertex of a possibly ideal triangle, equal actual side distances bisect its true ray angle. -/
theorem ClosedDiscTriangle.equidistant_bisects_finite_angleA (T : ClosedDiscTriangle) (a q : 𝔻)
    (ha : T.a = discToClosedModel a) (hq : q ∈ T.interior)
    (heq : T.sideLineB.pointDist q = T.sideLineC.pointDist q) :
    discInteriorAngleMeasure (T.cornerRayABAtA a ha)
        (discRayThrough a q (T.finite_vertex_ne_of_mem_interior a q ha hq)) =
      discInteriorAngleMeasure (discRayThrough a q (T.finite_vertex_ne_of_mem_interior a q ha hq))
        (T.cornerRayACAtA a ha) := by
  let C := T.finiteHalfPlaneCornerAtDiscA a ha
  have hqH : discToHalfPlane q ∈ T.halfPlaneInterior := by
    change halfPlaneToDisc (discToHalfPlane q) ∈ T.interior
    rwa [halfPlaneToDisc_discToHalfPlane]
  have hp := (T.mem_halfPlaneInterior_iff _).mp hqH
  have hqi : discToHalfPlane q ∈ properHAngleInterior C.rayAB C.rayAC :=
    (C.mem_interior_iff _).mpr ⟨hp.1,hp.2.1⟩
  have hd : C.rayAB.supportLine.pointDist (discToHalfPlane q) =
      C.rayAC.supportLine.pointDist (discToHalfPlane q) := by
    rw [C.supportAB,C.supportAC,← T.sideLineC.pointDist_eq_halfPlane,← T.sideLineB.pointDist_eq_halfPlane]
    exact heq.symm
  have hn : discToHalfPlane a ≠ discToHalfPlane q :=
    discToHalfPlane_injective.ne (T.finite_vertex_ne_of_mem_interior a q ha hq)
  have hb := hAngle_equidistant_bisects C.rayAB C.rayAC C.proper hn hqi hd
  rw [discInteriorAngleMeasure_eq_halfPlane,discInteriorAngleMeasure_eq_halfPlane,
    T.cornerRayABAtA_toHalfPlane,T.cornerRayACAtA_toHalfPlane,discRayThrough_toHalfPlane]
  exact hb

theorem ClosedDiscTriangle.incenter_bisects_finite_angleA (T : ClosedDiscTriangle) (a : 𝔻)
    (ha : T.a = discToClosedModel a) :
    discInteriorAngleMeasure (T.cornerRayABAtA a ha)
        (discRayThrough a T.incenter (T.finite_vertex_ne_of_mem_interior a T.incenter ha T.incenter_mem_interior)) =
      discInteriorAngleMeasure (discRayThrough a T.incenter
        (T.finite_vertex_ne_of_mem_interior a T.incenter ha T.incenter_mem_interior))
        (T.cornerRayACAtA a ha) :=
  T.equidistant_bisects_finite_angleA a T.incenter ha T.incenter_mem_interior T.incenter_equidistant.2

/-- The internal equidistant locus is one nontrivial affine line in the closed Klein chart. -/
theorem ClosedDiscTriangle.exists_internal_bisector_affine (T : ClosedDiscTriangle) :
    ∃ n : ℂ, ∃ t : ℝ, n ≠ 0 ∧ closedDiscKleinAffine n t T.a = 0 ∧
      ∀ z ∈ T.interior, T.sideLineB.pointDist z = T.sideLineC.pointDist z ↔
        closedDiscKleinAffine n t (discToClosedModel z) = 0 := by
  let FB := closedDiscKleinAffine T.sideLineB.incenterNormal T.sideLineB.incenterOffset
  let FC := closedDiscKleinAffine T.sideLineC.incenterNormal T.sideLineC.incenterOffset
  let v := FB T.b
  let w := FC T.c
  have hv : v ≠ 0 := fun h => T.b_not_mem_sideLineB ((T.sideLineB.closed_incenter_affine_zero_iff _).mp h)
  have hw : w ≠ 0 := fun h => T.c_not_mem_sideLineC ((T.sideLineC.closed_incenter_affine_zero_iff _).mp h)
  have hBa : FB T.a = 0 := (T.sideLineB.closed_incenter_affine_zero_iff _).mpr T.a_mem_sideLineB
  have hBc : FB T.c = 0 := (T.sideLineB.closed_incenter_affine_zero_iff _).mpr T.c_mem_sideLineB
  have hCa : FC T.a = 0 := (T.sideLineC.closed_incenter_affine_zero_iff _).mpr T.a_mem_sideLineC
  have hCb : FC T.b = 0 := (T.sideLineC.closed_incenter_affine_zero_iff _).mpr T.b_mem_sideLineC
  have hBp (p : 𝕔𝔻) : FB p = (T.coordinate p).1 * v := by
    change closedDiscKleinAffine _ _ p = _
    rw [T.kleinAffine_reconstruction]
    change (1 - (T.coordinate p).1 - (T.coordinate p).2) * FB T.a +
      (T.coordinate p).1 * FB T.b + (T.coordinate p).2 * FB T.c = _
    rw [hBa,hBc]
    ring
  have hCp (p : 𝕔𝔻) : FC p = (T.coordinate p).2 * w := by
    change closedDiscKleinAffine _ _ p = _
    rw [T.kleinAffine_reconstruction]
    change (1 - (T.coordinate p).1 - (T.coordinate p).2) * FC T.a +
      (T.coordinate p).1 * FC T.b + (T.coordinate p).2 * FC T.c = _
    rw [hCa,hCb]
    ring
  let n : ℂ := (|v| / v) • T.sideLineB.incenterNormal - (|w| / w) • T.sideLineC.incenterNormal
  let t : ℝ := (|v| / v) * T.sideLineB.incenterOffset - (|w| / w) * T.sideLineC.incenterOffset
  have heval (p : 𝕔𝔻) : closedDiscKleinAffine n t p =
      (T.coordinate p).1 * |v| - (T.coordinate p).2 * |w| := by
    have he : closedDiscKleinAffine n t p = (|v| / v) * FB p - (|w| / w) * FC p := by
      simp only [closedDiscKleinAffine,n,t,FB,FC,inner_sub_left,real_inner_smul_left]
      ring
    rw [he,hBp,hCp]
    field_simp
  have ha : closedDiscKleinAffine n t T.a = 0 := by rw [heval,T.coordinate_a]; ring
  have hb : closedDiscKleinAffine n t T.b = |v| := by rw [heval,T.coordinate_b]; ring
  have hn : n ≠ 0 := by
    intro h
    simp only [closedDiscKleinAffine,h,inner_zero_left,zero_sub] at ha hb
    have hp := abs_pos.mpr hv
    linarith
  refine ⟨n,t,hn,ha,?_⟩
  intro z hz
  have hp := T.incenter_interior_coordinates hz
  have hBabs : |FB (discToClosedModel z)| = (T.discCoordinate z).1 * |v| := by
    rw [hBp,abs_mul]
    change |(T.discCoordinate z).1| * |v| = _
    rw [abs_of_pos hp.1]
  have hCabs : |FC (discToClosedModel z)| = (T.discCoordinate z).2 * |w| := by
    rw [hCp,abs_mul]
    change |(T.discCoordinate z).2| * |w| = _
    rw [abs_of_pos hp.2.1]
  have hEq : T.sideLineB.pointDist z = T.sideLineC.pointDist z ↔
      |FB (discToClosedModel z)| = |FC (discToClosedModel z)| := by
    rw [← Real.sinh_inj,DiscLine.sinh_pointDist_closed_incenter_affine,
      DiscLine.sinh_pointDist_closed_incenter_affine]
    constructor
    · exact mul_right_cancel₀ (halfPlaneKleinHeight_pos (discToHalfPlane z)).ne'
    · intro h
      exact congrArg (fun x : ℝ => x * halfPlaneKleinHeight (discToHalfPlane z)) h
  rw [hEq,hBabs,hCabs,heval]
  change _ ↔ (T.discCoordinate z).1 * |v| - (T.discCoordinate z).2 * |w| = 0
  exact sub_eq_zero.symm

/-- A canonical internal bisector is a genuine geodesic through the actual finite/ideal vertex,
with exactly the equal-side-distance locus inside the triangle. -/
def IsClosedTriangleInternalBisectorAtA (T : ClosedDiscTriangle) (L : DiscLine) : Prop :=
  T.a ∈ L.closedCarrier ∧ ∀ z ∈ T.interior,
    z ∈ L.carrier ↔ T.sideLineB.pointDist z = T.sideLineC.pointDist z

theorem ClosedDiscTriangle.closed_vertex_ne_of_mem_interior (T : ClosedDiscTriangle) {q : 𝔻}
    (hq : q ∈ T.interior) : T.a ≠ discToClosedModel q := by
  have hp := T.incenter_interior_coordinates hq
  intro he
  have hc := congrArg T.coordinate he
  rw [T.coordinate_a] at hc
  have hh : (0 : ℝ) = (T.discCoordinate q).1 := congrArg Prod.fst hc
  linarith

/-- The actual equidistant geodesic exists for an arbitrary finite or ideal vertex. -/
theorem ClosedDiscTriangle.internal_bisector_through_point (T : ClosedDiscTriangle) (q : 𝔻)
    (hq : q ∈ T.interior) (heq : T.sideLineB.pointDist q = T.sideLineC.pointDist q) :
    ∃ L : DiscLine, IsClosedTriangleInternalBisectorAtA T L ∧ q ∈ L.carrier := by
  obtain ⟨n,t,hn,hna,hbis⟩ := T.exists_internal_bisector_affine
  have hnq := (hbis q hq).mp heq
  have hneq := T.closed_vertex_ne_of_mem_interior hq
  obtain ⟨L,⟨hLa,hLq⟩,_⟩ := existsUnique_discLine_closedCarrier T.a (discToClosedModel q) hneq
  obtain ⟨m,s,hm,hL⟩ := L.closedKlein_affine_equation
  have hiff (p : 𝕔𝔻) : closedDiscKleinAffine n t p = 0 ↔ p ∈ L.closedCarrier := by
    unfold closedDiscKleinAffine
    rw [sub_eq_zero]
    exact (_root_.LowDimensionalTopology.Geometry.Euclidean.complex_affine_equations_iff_of_two_points hn hm
      (closedKleinCoordinate_injective.ne hneq) (sub_eq_zero.mp hna) (sub_eq_zero.mp hnq)
      ((hL T.a).mp hLa) ((hL (discToClosedModel q)).mp hLq)).trans (hL p).symm
  refine ⟨L,⟨hLa,?_⟩,(L.closedCarrier_mem_interior_iff q).mp hLq⟩
  intro z hz
  exact (L.closedCarrier_mem_interior_iff z).symm.trans ((hiff _).symm.trans (hbis z hz).symm)

/-- Every canonical bisector through a finite corner is its actual measured angle bisector. -/
theorem IsClosedTriangleInternalBisectorAtA.bisects_finite_angle {T : ClosedDiscTriangle} {L : DiscLine}
    (hL : IsClosedTriangleInternalBisectorAtA T L) (a q : 𝔻) (ha : T.a = discToClosedModel a)
    (hq : q ∈ T.interior) (hqL : q ∈ L.carrier) :
    discInteriorAngleMeasure (T.cornerRayABAtA a ha)
        (discRayThrough a q (T.finite_vertex_ne_of_mem_interior a q ha hq)) =
      discInteriorAngleMeasure (discRayThrough a q (T.finite_vertex_ne_of_mem_interior a q ha hq))
        (T.cornerRayACAtA a ha) :=
  T.equidistant_bisects_finite_angleA a q ha hq ((hL.2 q hq).mp hqL)

theorem ClosedDiscTriangle.incenter_cycle_closedCarrier (T : ClosedDiscTriangle) :
    T.cycle.closedCarrier = T.closedCarrier := by
  have he : ({T.cycle.a,T.cycle.b,T.cycle.c} : Set 𝕔𝔻) = {T.a,T.b,T.c} := by
    ext p
    simp only [ClosedDiscTriangle.cycle,mem_insert_iff,mem_singleton_iff]
    tauto
  unfold ClosedDiscTriangle.closedCarrier
  rw [he]

theorem ClosedDiscTriangle.incenter_cycle_interior (T : ClosedDiscTriangle) :
    T.cycle.interior = T.interior := by
  unfold ClosedDiscTriangle.interior ClosedDiscTriangle.complexInterior ClosedDiscTriangle.complexClosedCarrier
  rw [T.incenter_cycle_closedCarrier]

/--
three actual canonical bisector geodesics pass through one genuine internal point,
including triangles with ideal vertices. Their finite-corner measured-angle interpretation is proved above.
-/
theorem ClosedDiscTriangle.exists_common_internal_angle_bisectors (T : ClosedDiscTriangle) :
    ∃ q ∈ T.interior, ∃ A B C : DiscLine,
      IsClosedTriangleInternalBisectorAtA T A ∧ IsClosedTriangleInternalBisectorAtA T.cycle B ∧
        IsClosedTriangleInternalBisectorAtA T.cycle.cycle C ∧
        q ∈ A.carrier ∧ q ∈ B.carrier ∧ q ∈ C.carrier := by
  obtain ⟨A,hA,hqA⟩ := T.internal_bisector_through_point T.incenter T.incenter_mem_interior
    T.incenter_equidistant.2
  have hqB : T.incenter ∈ T.cycle.interior := by
    rw [T.incenter_cycle_interior]
    exact T.incenter_mem_interior
  have hqC : T.incenter ∈ T.cycle.cycle.interior := by
    rw [T.cycle.incenter_cycle_interior,T.incenter_cycle_interior]
    exact T.incenter_mem_interior
  have heqB : T.cycle.sideLineB.pointDist T.incenter = T.cycle.sideLineC.pointDist T.incenter := by
    change T.sideLineC.pointDist T.incenter = T.sideLineA.pointDist T.incenter
    exact (T.incenter_equidistant.1.trans T.incenter_equidistant.2).symm
  have heqC : T.cycle.cycle.sideLineB.pointDist T.incenter = T.cycle.cycle.sideLineC.pointDist T.incenter := by
    change T.sideLineA.pointDist T.incenter = T.sideLineB.pointDist T.incenter
    exact T.incenter_equidistant.1
  obtain ⟨B,hB,hqB⟩ := T.cycle.internal_bisector_through_point T.incenter hqB heqB
  obtain ⟨C,hC,hqC⟩ := T.cycle.cycle.internal_bisector_through_point T.incenter hqC heqC
  exact ⟨T.incenter,T.incenter_mem_interior,A,B,C,hA,hB,hC,hqA,hqB,hqC⟩

end
end LowDimensionalTopology.Geometry.Hyperbolic
