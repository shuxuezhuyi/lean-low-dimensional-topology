/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Hyperbolic.Metric.LineCrossRatios

/-!
# Actual equal-distance loci of line pairs
-/
@[expose] public section
open Set
open scoped UpperHalfPlane MatrixGroups Complex.UnitDisc OnePoint
namespace LowDimensionalTopology.Geometry.Hyperbolic
open LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
noncomputable section

def HalfPlaneLine.bisectorSet (L M : HalfPlaneLine) : Set ℍ := {z | L.pointDist z=M.pointDist z}

def DiscLine.bisectorSet (L M : DiscLine) : Set 𝔻 := {z | L.pointDist z=M.pointDist z}

theorem HalfPlaneLine.mem_bisector_iff_sinh (L M : HalfPlaneLine) (z : ℍ) :
    z ∈ L.bisectorSet M ↔ Real.sinh (L.pointDist z)=Real.sinh (M.pointDist z) := by
  change L.pointDist z=M.pointDist z ↔ _
  exact Real.sinh_inj.symm

theorem common_factor_div_eq_iff (A B x y k : ℝ) (hk : k≠0) :
    A/(k*x)=B/(k*y) ↔ A/x=B/y := by
  rw [mul_comm k x,mul_comm k y,← div_div,← div_div,div_left_inj' hk]

theorem abs_sub_eq_abs_sub_iff_midpoint (a b x : ℝ) (hab : a≠b) :
    |x-a|=|x-b| ↔ x=(a+b)/2 := by
  rw [← sq_eq_sq₀ (abs_nonneg _) (abs_nonneg _),sq_abs,sq_abs]
  constructor
  · intro h
    have hm : (a-b)*(2*x-a-b)=0 := by nlinarith
    have hh := (mul_eq_zero.mp hm).resolve_left (sub_ne_zero.mpr hab)
    linarith
  · intro h
    rw [h]
    ring

theorem vertical_bisectorSet (a b : ℝ) (hab : a≠b) :
    (HalfPlaneLine.vertical a).bisectorSet (HalfPlaneLine.vertical b)=
      (HalfPlaneLine.vertical ((a+b)/2)).carrier := by
  ext z
  rw [HalfPlaneLine.mem_bisector_iff_sinh,verticalLine_pointDist_sinh,verticalLine_pointDist_sinh,
    div_left_inj' z.im_ne_zero,abs_sub_eq_abs_sub_iff_midpoint a b z.re hab]
  rfl

theorem abs_radius_ratio_eq_iff (Q s t : ℝ) (hQ : 0≤Q) (hs : 0<s) (ht : 0<t) (hst : s≠t) :
    |Q-s^2|/s=|Q-t^2|/t ↔ Q=s*t := by
  rw [div_eq_div_iff hs.ne' ht.ne']
  constructor
  · intro he
    have he2 := congrArg (fun x : ℝ => x^2) he
    rw [mul_pow,mul_pow,sq_abs,sq_abs] at he2
    have hf : (t^2-s^2)*(Q^2-s^2*t^2)=0 := by nlinarith only [he2]
    have hne : t^2-s^2≠0 := by intro hh; apply hst; nlinarith
    have hqs := (mul_eq_zero.mp hf).resolve_left hne
    nlinarith [mul_pos hs ht]
  · intro he
    rw [he,show s*t-s^2=s*(t-s) by ring,show s*t-t^2=t*(s-t) by ring,
      abs_mul,abs_mul,abs_of_pos hs,abs_of_pos ht,abs_sub_comm t s]
    ring

def concentricBisectorLine (s t : ℝ) (hs : 0<s) (ht : 0<t) : HalfPlaneLine :=
  .circle 0 (Real.sqrt (s*t)) (Real.sqrt_pos.mpr (mul_pos hs ht))

theorem concentric_bisectorSet (s t : ℝ) (hs : 0<s) (ht : 0<t) (hst : s≠t) :
    (HalfPlaneLine.circle 0 s hs).bisectorSet (HalfPlaneLine.circle 0 t ht)=
      (concentricBisectorLine s t hs ht).carrier := by
  ext z
  rw [HalfPlaneLine.mem_bisector_iff_sinh,circleLine_pointDist_sinh,circleLine_pointDist_sinh]
  simp only [Complex.ofReal_zero,sub_zero]
  rw [common_factor_div_eq_iff _ _ _ _ (2*z.im) (by positivity),
    abs_radius_ratio_eq_iff _ s t (sq_nonneg _) hs ht hst]
  change ‖(z : ℂ)‖^2=s*t ↔ ‖(z : ℂ)-(0 : ℂ)‖=Real.sqrt (s*t)
  rw [sub_zero,← sq_eq_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _),Real.sq_sqrt (mul_pos hs ht).le]

def axisCircleBisectorPlus (c r : ℝ) (hc : c^2<r^2) : HalfPlaneLine :=
  .circle (c+r) (Real.sqrt ((c+r)^2+(r^2-c^2))) (Real.sqrt_pos.mpr (by nlinarith [sq_nonneg (c+r)]))

def axisCircleBisectorMinus (c r : ℝ) (hc : c^2<r^2) : HalfPlaneLine :=
  .circle (c-r) (Real.sqrt ((c-r)^2+(r^2-c^2))) (Real.sqrt_pos.mpr (by nlinarith [sq_nonneg (c-r)]))

theorem axisCircleBisectors_orthogonal (c r : ℝ) (hc : c^2<r^2) :
    (axisCircleBisectorPlus c r hc).Orthogonal (axisCircleBisectorMinus c r hc) := by
  rw [HalfPlaneLine.orthogonal_iff_coefficients]
  change ((c+r)-(c-r))^2=Real.sqrt ((c+r)^2+(r^2-c^2))^2+Real.sqrt ((c-r)^2+(r^2-c^2))^2
  rw [Real.sq_sqrt (by nlinarith [sq_nonneg (c+r)]),Real.sq_sqrt (by nlinarith [sq_nonneg (c-r)])]
  ring

theorem axisCircleBisectors_ne (c r : ℝ) (hc : c^2<r^2) :
    axisCircleBisectorPlus c r hc≠axisCircleBisectorMinus c r hc := by
  intro he
  have hh := (HalfPlaneLine.circle.inj he).1
  nlinarith [sq_nonneg c]

theorem axis_circle_bisector_signed (c r : ℝ) (hr : 0<r) (z : ℍ) :
    z ∈ (HalfPlaneLine.vertical 0).bisectorSet (HalfPlaneLine.circle c r hr) ↔
      (z.re-c)^2+z.im^2-r^2=2*r*z.re ∨ (z.re-c)^2+z.im^2-r^2= -(2*r*z.re) := by
  rw [HalfPlaneLine.mem_bisector_iff_sinh,verticalLine_pointDist_sinh,circleLine_pointDist_sinh,
    norm_sub_real_sq]
  simp only [sub_zero]
  rw [show 2*z.im*r=z.im*(2*r) by ring,show |z.re|/z.im=|z.re|/(z.im*1) by rw [mul_one],
    common_factor_div_eq_iff _ _ 1 (2*r) z.im z.im_ne_zero,div_one]
  rw [eq_div_iff (by positivity : (2*r : ℝ)≠0)]
  have he : |z.re| * (2*r)=|(z.re-c)^2+z.im^2-r^2| ↔
      (2*r*z.re)^2=((z.re-c)^2+z.im^2-r^2)^2 := by
    rw [← sq_eq_sq₀ (by positivity) (abs_nonneg _),mul_pow,sq_abs,sq_abs]
    ring_nf
  rw [he,sq_eq_sq_iff_eq_or_eq_neg]
  constructor
  · rintro (h|h) <;> first | exact Or.inl h.symm | exact Or.inr (by linarith)
  · rintro (h|h) <;> first | exact Or.inl h.symm | exact Or.inr (by linarith)

theorem axis_circle_bisectorSet (c r : ℝ) (hr : 0<r) (hc : c^2<r^2) :
    (HalfPlaneLine.vertical 0).bisectorSet (HalfPlaneLine.circle c r hr)=
      (axisCircleBisectorPlus c r hc).carrier ∪ (axisCircleBisectorMinus c r hc).carrier := by
  ext z
  rw [axis_circle_bisector_signed]
  have hsp := Real.sq_sqrt (by nlinarith [sq_nonneg (c+r)] : 0≤(c+r)^2+(r^2-c^2))
  have hsm := Real.sq_sqrt (by nlinarith [sq_nonneg (c-r)] : 0≤(c-r)^2+(r^2-c^2))
  constructor
  · rintro (h|h)
    · left
      apply norm_sub_real_eq_of_sq (Real.sqrt_pos.mpr (by nlinarith [sq_nonneg (c+r)]))
      rw [hsp]
      nlinarith
    · right
      apply norm_sub_real_eq_of_sq (Real.sqrt_pos.mpr (by nlinarith [sq_nonneg (c-r)]))
      rw [hsm]
      nlinarith
  · rintro (h|h)
    · left
      have hh := norm_sub_real_eq_radius_sq h
      rw [hsp] at hh
      nlinarith
    · right
      have hh := norm_sub_real_eq_radius_sq h
      rw [hsm] at hh
      nlinarith


theorem HalfPlaneLine.bisectorSet_image_isometry (L M L' M' : HalfPlaneLine)
    (f : ℍ → ℍ) (hf : Isometry f) (hL : f '' L.carrier=L'.carrier) (hM : f '' M.carrier=M'.carrier) :
    f '' L.bisectorSet M=L'.bisectorSet M' := by
  ext z
  constructor
  · rintro ⟨w,hw,rfl⟩
    change L'.pointDist (f w)=M'.pointDist (f w)
    rw [L.pointDist_isometry_image L' f hf hL,M.pointDist_isometry_image M' f hf hM]
    exact hw
  · intro hz
    obtain ⟨w,rfl⟩ := _root_.LowDimensionalTopology.Geometry.Hyperbolic.Isometry.halfPlane_surjective hf z
    refine ⟨w,?_,rfl⟩
    change L.pointDist w=M.pointDist w
    rw [← L.pointDist_isometry_image L' f hf hL,← M.pointDist_isometry_image M' f hf hM]
    exact hz

theorem HalfPlaneLine.eq_vertical_of_infty_ideal (L : HalfPlaneLine)
    (h : (∞ : OnePoint ℂ) ∈ L.idealEndpoints) : ∃ a : ℝ, L=HalfPlaneLine.vertical a := by
  cases L with
  | vertical a => exact ⟨a,rfl⟩
  | circle c r hr =>
    rw [circle_idealEndpoints] at h
    simp only [mem_insert_iff,mem_singleton_iff] at h
    rcases h with h|h <;> exact (OnePoint.coe_ne_infty _ h.symm).elim

theorem HalfPlaneLine.exists_parallel_vertical_normalizer (L M : HalfPlaneLine) (hpar : L.Parallel M) :
    ∃ (g : GL (Fin 2) ℝ) (a b : ℝ), 0<g.val.det ∧ a≠b ∧
      (g • · : ℍ → ℍ) '' L.carrier=(HalfPlaneLine.vertical a).carrier ∧
      (g • · : ℍ → ℍ) '' M.carrier=(HalfPlaneLine.vertical b).carrier := by
  obtain ⟨u,hu⟩ := hpar.2
  have hu' : u ∈ L.idealEndpoints ∩ M.idealEndpoints := hu.symm ▸ mem_singleton u
  obtain ⟨g,hg,hgu⟩ := exists_boundaryProjectiveChart hu'.1.2
  obtain ⟨L',hL⟩ := realGL_image_hLine g L
  obtain ⟨M',hM⟩ := realGL_image_hLine g M
  have hLu : (∞ : OnePoint ℂ) ∈ L'.idealEndpoints := by
    rw [L.idealEndpoints_realGL_image L' g hg hL,← hgu]
    exact mem_image_of_mem _ hu'.1
  have hMu : (∞ : OnePoint ℂ) ∈ M'.idealEndpoints := by
    rw [M.idealEndpoints_realGL_image M' g hg hM,← hgu]
    exact mem_image_of_mem _ hu'.2
  obtain ⟨a,rfl⟩ := L'.eq_vertical_of_infty_ideal hLu
  obtain ⟨b,rfl⟩ := M'.eq_vertical_of_infty_ideal hMu
  refine ⟨g,a,b,hg,?_,hL,hM⟩
  intro hab
  apply hpar.1
  apply HalfPlaneLine.carrier_injective
  apply (realGL_isometry g).injective.image_injective
  rw [hL,hM,hab]

theorem HalfPlaneLine.exists_intersecting_axis_circle_normalizer (L M : HalfPlaneLine)
    (hi : L.Intersecting M) :
    ∃ (g : GL (Fin 2) ℝ) (c r : ℝ) (hr : 0<r), 0<g.val.det ∧ c^2<r^2 ∧
      (g • · : ℍ → ℍ) '' L.carrier=(HalfPlaneLine.vertical 0).carrier ∧
      (g • · : ℍ → ℍ) '' M.carrier=(HalfPlaneLine.circle c r hr).carrier := by
  obtain ⟨g,hg,hL⟩ := L.exists_mobius_map (HalfPlaneLine.vertical 0)
  obtain ⟨M',hM⟩ := realGL_image_hLine g M
  obtain ⟨p,hpL,hpM⟩ := hi.2.2
  have hpL' : (g • p).re=0 := by
    have he : g • p ∈ (HalfPlaneLine.vertical 0).carrier := hL ▸ mem_image_of_mem _ hpL
    exact he
  have hpM' : g • p ∈ M'.carrier := hM ▸ mem_image_of_mem _ hpM
  cases M' with
  | vertical b =>
    have hb : b=0 := hpM'.symm.trans hpL'
    apply False.elim
    apply hi.1
    apply HalfPlaneLine.carrier_injective
    apply (realGL_isometry g).injective.image_injective
    rw [hL,hM,hb]
  | circle c r hr =>
    refine ⟨g,c,r,hr,hg,?_,hL,hM⟩
    have h := norm_sub_real_eq_radius_sq hpM'
    rw [hpL'] at h
    nlinarith [sq_pos_of_pos (g • p).im_pos]

theorem HalfPlaneLine.bisector_eq_line_of_normalized (L M L' M' B : HalfPlaneLine)
    (g : GL (Fin 2) ℝ) (hL : (g • · : ℍ → ℍ) '' L.carrier=L'.carrier)
    (hM : (g • · : ℍ → ℍ) '' M.carrier=M'.carrier) (hB : L'.bisectorSet M'=B.carrier) :
    ∃ N : HalfPlaneLine, L.bisectorSet M=N.carrier := by
  obtain ⟨N,hN⟩ := realGL_image_hLine g⁻¹ B
  have hb := L.bisectorSet_image_isometry M L' M' (g • ·) (realGL_isometry g) hL hM
  refine ⟨N,?_⟩
  rw [← hB,← hb,image_image] at hN
  simpa only [inv_smul_smul,Set.image_id'] using hN

theorem HalfPlaneLine.bisector_parallel (L M : HalfPlaneLine) (hp : L.Parallel M) :
    ∃ N : HalfPlaneLine, L.bisectorSet M=N.carrier := by
  obtain ⟨g,a,b,_,hab,hL,hM⟩ := L.exists_parallel_vertical_normalizer M hp
  exact L.bisector_eq_line_of_normalized M _ _ _ g hL hM (vertical_bisectorSet a b hab)

theorem HalfPlaneLine.bisector_disjoint (L M : HalfPlaneLine) (hd : L.HDisjoint M) :
    ∃ N : HalfPlaneLine, L.bisectorSet M=N.carrier := by
  obtain ⟨g,s,t,hs,ht,_,hst,hL,hM⟩ := L.exists_concentric_normalizer M hd
  exact L.bisector_eq_line_of_normalized M _ _ _ g hL hM (concentric_bisectorSet s t hs ht hst)

theorem HalfPlaneLine.bisector_intersecting (L M : HalfPlaneLine) (hi : L.Intersecting M) :
    ∃ N P : HalfPlaneLine, N≠P ∧ N.Orthogonal P ∧ L.bisectorSet M=N.carrier ∪ P.carrier := by
  obtain ⟨g,c,r,hr,_,hc,hL,hM⟩ := L.exists_intersecting_axis_circle_normalizer M hi
  let B := axisCircleBisectorPlus c r hc
  let C := axisCircleBisectorMinus c r hc
  obtain ⟨N,hN⟩ := realGL_image_hLine g⁻¹ B
  obtain ⟨P,hP⟩ := realGL_image_hLine g⁻¹ C
  refine ⟨N,P,?_,?_,?_⟩
  · intro he
    have hNg := realGL_inverse_image_eq g⁻¹ hN
    have hPg := realGL_inverse_image_eq g⁻¹ hP
    apply axisCircleBisectors_ne c r hc
    apply HalfPlaneLine.carrier_injective
    rw [← hNg,← hPg,he]
  · exact B.orthogonal_isometry_image C N P (g⁻¹ • ·) (realGL_isometry g⁻¹) hN hP
      (axisCircleBisectors_orthogonal c r hc)
  · have hb := L.bisectorSet_image_isometry M _ _ (g • ·) (realGL_isometry g) hL hM
    have he : (g⁻¹ • · : ℍ → ℍ) '' ((g • · : ℍ → ℍ) '' L.bisectorSet M)=L.bisectorSet M := by
      rw [image_image]
      simp only [inv_smul_smul,Set.image_id']
    rw [← he,hb,axis_circle_bisectorSet c r hr hc,image_union,hN,hP]

theorem HalfPlaneLine.bisector_classification (L M : HalfPlaneLine) (hne : L≠M) :
    (∃ N : HalfPlaneLine, L.bisectorSet M=N.carrier) ∨
      (∃ N P : HalfPlaneLine, N≠P ∧ N.Orthogonal P ∧ L.bisectorSet M=N.carrier ∪ P.carrier) := by
  rcases L.classification M hne with hp|hi|hd
  · exact Or.inl (L.bisector_parallel M hp)
  · exact Or.inr (L.bisector_intersecting M hi)
  · exact Or.inl (L.bisector_disjoint M hd)


theorem DiscLine.bisectorSet_eq_cayley (L M : DiscLine) :
    L.bisectorSet M=halfPlaneToDisc '' L.toHalfPlane.bisectorSet M.toHalfPlane := by
  ext z
  constructor
  · intro hz
    refine ⟨discToHalfPlane z,?_,halfPlaneToDisc_discToHalfPlane z⟩
    change L.toHalfPlane.pointDist (discToHalfPlane z)=M.toHalfPlane.pointDist (discToHalfPlane z)
    rw [← L.pointDist_eq_halfPlane,← M.pointDist_eq_halfPlane]
    exact hz
  · rintro ⟨w,hw,rfl⟩
    change L.pointDist (halfPlaneToDisc w)=M.pointDist (halfPlaneToDisc w)
    rw [L.pointDist_eq_halfPlane,M.pointDist_eq_halfPlane,discToHalfPlane_halfPlaneToDisc]
    exact hw

theorem DiscLine.parallel_toHalfPlane (L M : DiscLine) (hp : L.Parallel M) :
    L.toHalfPlane.Parallel M.toHalfPlane := by
  obtain ⟨u,hu⟩ := hp.2
  refine ⟨DiscLine.toHalfPlane_injective.ne hp.1,extendedCayley.symm u,?_⟩
  apply extendedCayley.injective.image_injective
  rw [Set.image_inter extendedCayley.injective,← L.idealEndpoints_eq_cayley_image,
    ← M.idealEndpoints_eq_cayley_image,hu,image_singleton,Homeomorph.apply_symm_apply]

theorem DiscLine.intersecting_toHalfPlane (L M : DiscLine) (hi : L.Intersecting M) :
    L.toHalfPlane.Intersecting M.toHalfPlane := by
  obtain ⟨p,hpL,hpM⟩ := hi.2.2
  refine ⟨DiscLine.toHalfPlane_injective.ne hi.1,?_,discToHalfPlane p,
    (L.mem_carrier p).mp hpL,(M.mem_carrier p).mp hpM⟩
  rw [← Set.disjoint_image_iff extendedCayley.injective,← L.idealEndpoints_eq_cayley_image,
    ← M.idealEndpoints_eq_cayley_image]
  exact hi.2.1

theorem DiscLine.bisector_parallel (L M : DiscLine) (hp : L.Parallel M) :
    ∃ N : DiscLine, L.bisectorSet M=N.carrier := by
  obtain ⟨N,hN⟩ := L.toHalfPlane.bisector_parallel M.toHalfPlane (L.parallel_toHalfPlane M hp)
  refine ⟨N.toDiscLine,?_⟩
  rw [L.bisectorSet_eq_cayley,hN,HalfPlaneLine.toDiscLine_carrier,HalfPlaneLine.discCarrier_eq_cayley_image]

theorem DiscLine.bisector_disjoint (L M : DiscLine) (hd : L.HDisjoint M) :
    ∃ N : DiscLine, L.bisectorSet M=N.carrier := by
  obtain ⟨N,hN⟩ := L.toHalfPlane.bisector_disjoint M.toHalfPlane ((L.hDisjoint_iff_halfPlane M).mp hd)
  refine ⟨N.toDiscLine,?_⟩
  rw [L.bisectorSet_eq_cayley,hN,HalfPlaneLine.toDiscLine_carrier,HalfPlaneLine.discCarrier_eq_cayley_image]

theorem DiscLine.bisector_intersecting (L M : DiscLine) (hi : L.Intersecting M) :
    ∃ N P : DiscLine, N≠P ∧ N.Orthogonal P ∧ L.bisectorSet M=N.carrier ∪ P.carrier := by
  obtain ⟨N,P,hne,ho,he⟩ := L.toHalfPlane.bisector_intersecting M.toHalfPlane
    (L.intersecting_toHalfPlane M hi)
  refine ⟨N.toDiscLine,P.toDiscLine,HalfPlaneLine.toDiscLine_injective.ne hne,?_,?_⟩
  · rw [DiscLine.orthogonal_iff_halfPlane,N.toDiscLine_toHalfPlane,P.toDiscLine_toHalfPlane]
    exact ho
  · rw [L.bisectorSet_eq_cayley,he,image_union,HalfPlaneLine.toDiscLine_carrier,
      HalfPlaneLine.toDiscLine_carrier,HalfPlaneLine.discCarrier_eq_cayley_image,
      HalfPlaneLine.discCarrier_eq_cayley_image]

theorem DiscLine.bisector_classification (L M : DiscLine) (hne : L≠M) :
    (∃ N : DiscLine, L.bisectorSet M=N.carrier) ∨
      (∃ N P : DiscLine, N≠P ∧ N.Orthogonal P ∧ L.bisectorSet M=N.carrier ∪ P.carrier) := by
  rcases L.classification M hne with hp|hi|hd
  · exact Or.inl (L.bisector_parallel M hp)
  · exact Or.inr (L.bisector_intersecting M hi)
  · exact Or.inl (L.bisector_disjoint M hd)

end
end LowDimensionalTopology.Geometry.Hyperbolic
