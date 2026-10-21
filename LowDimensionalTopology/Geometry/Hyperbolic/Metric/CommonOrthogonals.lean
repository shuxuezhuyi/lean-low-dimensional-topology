/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Hyperbolic.Metric.HypercycleDistance
public import LowDimensionalTopology.Geometry.Hyperbolic.Trigonometry.AngleParallelism

/-! # Actual line orthogonality transported through genuine metric isometries -/
@[expose] public section
open Set
open scoped UpperHalfPlane MatrixGroups Complex.UnitDisc OnePoint
namespace LowDimensionalTopology.Geometry.Hyperbolic
open LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
noncomputable section

theorem HalfPlaneLine.exists_point_ne (L : HalfPlaneLine) (p : ℍ) :
    ∃ z ∈ L.carrier, z ≠ p := by
  obtain ⟨u,v,hu,hv,huv⟩ := L.exists_two_points
  by_cases hup : u=p
  · exact ⟨v,hv,hup ▸ huv.symm⟩
  · exact ⟨u,hu,hup⟩

/-- The genuine closest-point property at two distinct points recovers actual tangent orthogonality. -/
theorem HalfPlaneLine.orthogonalAt_of_nearest (L M : HalfPlaneLine) {p z : ℍ}
    (hp : p ∈ L.carrier) (hpM : p ∈ M.carrier) (hzM : z ∈ M.carrier) (hzp : z ≠ p)
    (hnear : L.pointDist z = dist z p) : L.OrthogonalAt M p := by
  obtain ⟨N,⟨hzN,⟨q,hq⟩⟩,_⟩ := L.existsUnique_perpendicular z
  obtain ⟨w,_,huniq⟩ := L.exists_unique_nearest_point z
  have hpw := huniq p ⟨hp,hnear⟩
  have hqw := huniq q ⟨hq.1,L.pointDist_eq_dist_of_perpendicular N q z hq hzN⟩
  have hqp : q=p := hqw.trans hpw.symm
  rw [hqp] at hq
  have he : N=M := N.eq_of_two_points M hzp hzN hq.2.1 hzM hpM
  rwa [he] at hq

/-- Genuine metric isometries preserve the actual tangent orthogonality of image h-lines. -/
theorem HalfPlaneLine.orthogonalAt_isometry_image (L M L' M' : HalfPlaneLine)
    (f : ℍ → ℍ) (hf : Isometry f)
    (hL : f '' L.carrier = L'.carrier) (hM : f '' M.carrier = M'.carrier)
    {p : ℍ} (hp : L.OrthogonalAt M p) : L'.OrthogonalAt M' (f p) := by
  obtain ⟨z,hz,hzp⟩ := M.exists_point_ne p
  have hpL : f p ∈ L'.carrier := hL ▸ mem_image_of_mem f hp.1
  have hpM : f p ∈ M'.carrier := hM ▸ mem_image_of_mem f hp.2.1
  have hzM : f z ∈ M'.carrier := hM ▸ mem_image_of_mem f hz
  apply L'.orthogonalAt_of_nearest M' hpL hpM hzM (hf.injective.ne hzp)
  rw [L.pointDist_isometry_image L' f hf hL,hf.dist_eq]
  exact L.pointDist_eq_dist_of_perpendicular M p z hp hz

theorem HalfPlaneLine.orthogonal_isometry_image (L M L' M' : HalfPlaneLine)
    (f : ℍ → ℍ) (hf : Isometry f)
    (hL : f '' L.carrier = L'.carrier) (hM : f '' M.carrier = M'.carrier)
    (hp : L.Orthogonal M) : L'.Orthogonal M' := by
  obtain ⟨p,hp⟩ := hp
  exact ⟨f p,L.orthogonalAt_isometry_image M L' M' f hf hL hM hp⟩

theorem realGL_inverse_image_eq {L M : HalfPlaneLine} (g : GL (Fin 2) ℝ)
    (he : (g • · : ℍ → ℍ) '' L.carrier = M.carrier) :
    (g⁻¹ • · : ℍ → ℍ) '' M.carrier = L.carrier := by
  rw [← he,image_image]
  simp only [inv_smul_smul,Set.image_id']

theorem HalfPlaneLine.orthogonalAt_realGL_image_iff (L M L' M' : HalfPlaneLine)
    (g : GL (Fin 2) ℝ)
    (hL : (g • · : ℍ → ℍ) '' L.carrier = L'.carrier)
    (hM : (g • · : ℍ → ℍ) '' M.carrier = M'.carrier) (p : ℍ) :
    L'.OrthogonalAt M' (g • p) ↔ L.OrthogonalAt M p := by
  constructor
  · intro hp
    have h := L'.orthogonalAt_isometry_image M' L M (g⁻¹ • ·) (realGL_isometry g⁻¹)
      (realGL_inverse_image_eq g hL) (realGL_inverse_image_eq g hM) hp
    simpa only [inv_smul_smul] using h
  · exact L.orthogonalAt_isometry_image M L' M' (g • ·) (realGL_isometry g) hL hM

theorem HalfPlaneLine.orthogonal_realGL_image_iff (L M L' M' : HalfPlaneLine)
    (g : GL (Fin 2) ℝ)
    (hL : (g • · : ℍ → ℍ) '' L.carrier = L'.carrier)
    (hM : (g • · : ℍ → ℍ) '' M.carrier = M'.carrier) :
    L'.Orthogonal M' ↔ L.Orthogonal M := by
  constructor
  · intro hp
    exact L'.orthogonal_isometry_image M' L M (g⁻¹ • ·) (realGL_isometry g⁻¹)
      (realGL_inverse_image_eq g hL) (realGL_inverse_image_eq g hM) hp
  · exact L.orthogonal_isometry_image M L' M' (g • ·) (realGL_isometry g) hL hM


theorem HalfPlaneLine.idealEndpoints_realGL_image (L M : HalfPlaneLine)
    (g : GL (Fin 2) ℝ) (hg : 0 < g.val.det)
    (he : (g • · : ℍ → ℍ) '' L.carrier = M.carrier) :
    M.idealEndpoints = Mobius.fractionalLinear (complexifiedRealMobiusMatrix g) '' L.idealEndpoints := by
  change hTraceIdealEndpoints M.carrier =
    Mobius.fractionalLinear (complexifiedRealMobiusMatrix g) '' hTraceIdealEndpoints L.carrier
  rw [← he,realGL_traceIdealEndpoints g hg]

theorem HalfPlaneLine.hDisjoint_realGL_image (L M L' M' : HalfPlaneLine)
    (g : GL (Fin 2) ℝ) (hg : 0 < g.val.det)
    (hL : (g • · : ℍ → ℍ) '' L.carrier = L'.carrier)
    (hM : (g • · : ℍ → ℍ) '' M.carrier = M'.carrier)
    (hd : L.HDisjoint M) : L'.HDisjoint M' := by
  refine ⟨?_,?_,?_⟩
  · intro he
    apply hd.1
    apply HalfPlaneLine.carrier_injective
    apply (realGL_isometry g).injective.image_injective
    exact hL.trans ((congrArg HalfPlaneLine.carrier he).trans hM.symm)
  · rw [L.idealEndpoints_realGL_image L' g hg hL,M.idealEndpoints_realGL_image M' g hg hM,
      Set.disjoint_image_iff (show Function.Injective (Mobius.fractionalLinear (complexifiedRealMobiusMatrix g)) from
        (Mobius.fractionalLinearHomeomorph (complexifiedRealMobiusMatrix g)).injective)]
    exact hd.2.1
  · rw [← hL,← hM,Set.disjoint_image_iff (realGL_isometry g).injective]
    exact hd.2.2

theorem vertical_hDisjoint_circle_data (M : HalfPlaneLine)
    (hd : (HalfPlaneLine.vertical 0).HDisjoint M) :
    ∃ (c r : ℝ) (hr : 0 < r), M = HalfPlaneLine.circle c r hr ∧ r^2<c^2 := by
  cases M with
  | vertical x =>
    have h0 : (∞ : OnePoint ℂ) ∈ (HalfPlaneLine.vertical 0).idealEndpoints := by
      rw [vertical_idealEndpoints]
      exact mem_insert_of_mem _ (mem_singleton _)
    have hx : (∞ : OnePoint ℂ) ∈ (HalfPlaneLine.vertical x).idealEndpoints := by
      rw [vertical_idealEndpoints]
      exact mem_insert_of_mem _ (mem_singleton _)
    exact (Set.disjoint_left.mp hd.2.1 h0 hx).elim
  | circle c r hr =>
    refine ⟨c,r,hr,rfl,?_⟩
    have hn : r^2 ≠ c^2 := by
      intro he
      have hc : c=r ∨ c=-r := (sq_eq_sq_iff_eq_or_eq_neg).mp he.symm
      have h0 : ((0 : ℂ) : OnePoint ℂ) ∈ (HalfPlaneLine.vertical 0).idealEndpoints := by
        rw [vertical_idealEndpoints]
        exact mem_insert _ _
      have hC : ((0 : ℂ) : OnePoint ℂ) ∈ (HalfPlaneLine.circle c r hr).idealEndpoints := by
        rw [circle_idealEndpoints]
        rcases hc with rfl | rfl
        · simp
        · have he : -r+r=0 := by ring
          rw [he]
          exact mem_insert_of_mem _ (mem_singleton _)
      exact Set.disjoint_left.mp hd.2.1 h0 hC
    have hle : r^2≤c^2 := by
      by_contra hh
      have hp : 0 < r^2-c^2 := sub_pos.mpr (lt_of_not_ge hh)
      let z : ℍ := UpperHalfPlane.mk ⟨0,Real.sqrt (r^2-c^2)⟩ (Real.sqrt_pos.mpr hp)
      have hz0 : z ∈ (HalfPlaneLine.vertical 0).carrier := rfl
      have hzC : z ∈ (HalfPlaneLine.circle c r hr).carrier := by
        apply norm_sub_real_eq_of_sq hr
        change (0-c)^2+Real.sqrt (r^2-c^2)^2=r^2
        rw [Real.sq_sqrt hp.le]
        ring
      exact Set.disjoint_left.mp hd.2.2 hz0 hzC
    exact lt_of_le_of_ne hle hn

theorem existsUnique_normalized_commonOrthogonal (c r : ℝ) (hr : 0 < r)
    (hc : r^2<c^2) :
    ∃! N : HalfPlaneLine, (HalfPlaneLine.vertical 0).Orthogonal N ∧
      (HalfPlaneLine.circle c r hr).Orthogonal N := by
  let t := Real.sqrt (c^2-r^2)
  have ht : 0 < t := Real.sqrt_pos.mpr (sub_pos.mpr hc)
  have hts : t^2=c^2-r^2 := Real.sq_sqrt (sub_pos.mpr hc).le
  let N := HalfPlaneLine.circle 0 t ht
  have hN : (HalfPlaneLine.vertical 0).Orthogonal N ∧
      (HalfPlaneLine.circle c r hr).Orthogonal N := by
    constructor
    · rw [HalfPlaneLine.orthogonal_iff_coefficients]
      rfl
    · rw [HalfPlaneLine.orthogonal_iff_coefficients]
      change (c-0)^2=r^2+t^2
      nlinarith
  refine ⟨N,hN,?_⟩
  intro M hM
  have hM0 := ((HalfPlaneLine.vertical 0).orthogonal_iff_coefficients M).mp hM.1
  have hMC := ((HalfPlaneLine.circle c r hr).orthogonal_iff_coefficients M).mp hM.2
  cases M with
  | vertical x => exact hM0.elim
  | circle d s hs =>
    change 0=d at hM0
    subst d
    change (c-0)^2=r^2+s^2 at hMC
    have hst : s=t := by nlinarith
    subst s
    rfl

/-- The source's unique common perpendicular for genuinely disjoint H-lines. -/
theorem HalfPlaneLine.existsUnique_commonOrthogonal (L M : HalfPlaneLine) (hd : L.HDisjoint M) :
    ∃! N : HalfPlaneLine, L.Orthogonal N ∧ M.Orthogonal N := by
  obtain ⟨g,hg,hL⟩ := L.exists_mobius_map (HalfPlaneLine.vertical 0)
  obtain ⟨M',hM⟩ := realGL_image_hLine g M
  have hd' := L.hDisjoint_realGL_image M _ M' g hg hL hM hd
  obtain ⟨c,r,hr,rfl,hc⟩ := vertical_hDisjoint_circle_data M' hd'
  obtain ⟨K,hK,huniq⟩ := existsUnique_normalized_commonOrthogonal c r hr hc
  obtain ⟨N,hN⟩ := realGL_image_hLine g⁻¹ K
  have hNg : (g • · : ℍ → ℍ) '' N.carrier = K.carrier := by
    simpa only [inv_inv] using realGL_inverse_image_eq g⁻¹ hN
  have hp : L.Orthogonal N ∧ M.Orthogonal N :=
    ⟨(L.orthogonal_realGL_image_iff N _ K g hL hNg).mp hK.1,
      (M.orthogonal_realGL_image_iff N _ K g hM hNg).mp hK.2⟩
  refine ⟨N,hp,?_⟩
  intro P hP
  obtain ⟨P',hP'⟩ := realGL_image_hLine g P
  have he : P'=K := huniq P'
    ⟨L.orthogonal_isometry_image P _ P' (g • ·) (realGL_isometry g) hL hP' hP.1,
      M.orthogonal_isometry_image P _ P' (g • ·) (realGL_isometry g) hM hP' hP.2⟩
  apply HalfPlaneLine.carrier_injective
  apply (realGL_isometry g).injective.image_injective
  rw [hP',he,hNg]

theorem DiscLine.hDisjoint_iff_halfPlane (L M : DiscLine) :
    L.HDisjoint M ↔ L.toHalfPlane.HDisjoint M.toHalfPlane := by
  change (L ≠ M ∧ Disjoint L.idealEndpoints M.idealEndpoints ∧ Disjoint L.carrier M.carrier) ↔ _
  rw [L.idealEndpoints_eq_cayley_image,M.idealEndpoints_eq_cayley_image,
    Set.disjoint_image_iff extendedCayley.injective,L.carrier_eq_cayley_image_halfPlane,
    M.carrier_eq_cayley_image_halfPlane,Set.disjoint_image_iff (show Function.Injective halfPlaneToDisc from
      cayleyHomeomorph.injective)]
  change (L ≠ M ∧ _ ∧ _) ↔ (L.toHalfPlane ≠ M.toHalfPlane ∧ _ ∧ _)
  exact and_congr (not_congr DiscLine.toHalfPlane_injective.eq_iff.symm) (Iff.rfl)

/-- The same unique common perpendicular on actual native disc circle/diameter h-lines. -/
theorem DiscLine.existsUnique_commonOrthogonal (L M : DiscLine) (hd : L.HDisjoint M) :
    ∃! N : DiscLine, L.Orthogonal N ∧ M.Orthogonal N := by
  obtain ⟨N,hN,huniq⟩ := L.toHalfPlane.existsUnique_commonOrthogonal M.toHalfPlane
    ((L.hDisjoint_iff_halfPlane M).mp hd)
  refine ⟨N.toDiscLine,?_,?_⟩
  · change L.Orthogonal N.toDiscLine ∧ M.Orthogonal N.toDiscLine
    rw [L.orthogonal_iff_halfPlane,M.orthogonal_iff_halfPlane,N.toDiscLine_toHalfPlane]
    exact hN
  · intro P hP
    have he : P.toHalfPlane=N := huniq P.toHalfPlane
      ⟨(L.orthogonal_iff_halfPlane P).mp hP.1,(M.orthogonal_iff_halfPlane P).mp hP.2⟩
    rw [← P.toHalfPlane_spec,he]

end
end LowDimensionalTopology.Geometry.Hyperbolic
