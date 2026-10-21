/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Hyperbolic.Metric.LineDistances
public import LowDimensionalTopology.Geometry.Hyperbolic.Angle.BoundaryOrder

/-! # Algebra for the actual ideal-endpoint line-distance identity -/
@[expose] public section
open Set
open scoped UpperHalfPlane MatrixGroups Complex.UnitDisc OnePoint
namespace LowDimensionalTopology.Geometry.Hyperbolic
open LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
noncomputable section

theorem tanh_half_exp (x : ℝ) : Real.tanh (x/2)=(Real.exp x-1)/(Real.exp x+1) := by
  have he : Real.exp x=Real.exp (x/2)^2 := by
    rw [pow_two,← Real.exp_add]
    congr 1
    ring
  rw [Real.tanh_eq,Real.exp_neg,he]
  field_simp

theorem tanh_abs_half_sq (x : ℝ) : Real.tanh (|x|/2)^2=Real.tanh (x/2)^2 := by
  by_cases hx : 0≤x
  · rw [abs_of_nonneg hx]
  · rw [abs_of_neg (lt_of_not_ge hx),neg_div,Real.tanh_neg,neg_sq]

theorem tanh_log_ratio_half_sq (s t : ℝ) (hs : 0<s) (ht : 0<t) :
    Real.tanh (|Real.log (s/t)|/2)^2=(s-t)^2/(s+t)^2 := by
  rw [tanh_abs_half_sq,tanh_half_exp,Real.exp_log (div_pos hs ht)]
  have he : (s/t-1)/(s/t+1)=(s-t)/(s+t) := by
    field_simp
  rw [he,div_pow]

theorem concentric_crossRatio (s t : ℝ) :
    Mobius.extendedCrossRatio (((-s : ℝ) : ℂ) : OnePoint ℂ) (((-t : ℝ) : ℂ) : OnePoint ℂ)
      (((t : ℝ) : ℂ) : OnePoint ℂ) (((s : ℝ) : ℂ) : OnePoint ℂ)=
      (((s+t)^2/(s-t)^2 : ℝ) : ℂ) := by
  rw [Mobius.extendedCrossRatio_coe]
  push_cast
  congr 1 <;> ring

theorem concentric_crossRatio_opposite (s t : ℝ) :
    Mobius.extendedCrossRatio (((-s : ℝ) : ℂ) : OnePoint ℂ) (((t : ℝ) : ℂ) : OnePoint ℂ)
      (((-t : ℝ) : ℂ) : OnePoint ℂ) (((s : ℝ) : ℂ) : OnePoint ℂ)=
      (((s-t)^2/(s+t)^2 : ℝ) : ℂ) := by
  rw [Mobius.extendedCrossRatio_coe]
  push_cast
  congr 1 <;> ring

theorem concentric_crossRatio_small (s t : ℝ) (hs : 0<s) (ht : 0<t) :
    (s-t)^2/(s+t)^2<1 := by
  apply (div_lt_one (by positivity : 0<(s+t)^2)).mpr
  nlinarith [mul_pos hs ht]

theorem concentric_crossRatio_distance (s t : ℝ) (hs : 0<s) (ht : 0<t) (hst : s≠t) :
    Mobius.extendedCrossRatio (((-s : ℝ) : ℂ) : OnePoint ℂ) (((-t : ℝ) : ℂ) : OnePoint ℂ)
      (((t : ℝ) : ℂ) : OnePoint ℂ) (((s : ℝ) : ℂ) : OnePoint ℂ) *
      ((Real.tanh ((HalfPlaneLine.circle 0 s hs).lineDist (HalfPlaneLine.circle 0 t ht)/2)^2 : ℝ) : ℂ)=1 := by
  rw [concentric_crossRatio,concentric_lineDist,tanh_log_ratio_half_sq s t hs ht]
  have hr : (s+t)^2/(s-t)^2*((s-t)^2/(s+t)^2)=1 := by
    field_simp [sub_ne_zero.mpr hst,ne_of_gt (add_pos hs ht)]
  exact_mod_cast hr


theorem extendedCrossRatio_reverse_all (a b c d : OnePoint ℂ) :
    Mobius.extendedCrossRatio a b c d=Mobius.extendedCrossRatio d c b a := by
  unfold Mobius.extendedCrossRatio Mobius.homogeneousCrossRatio Mobius.complexWedge
  congr 1 <;> ring

theorem HalfPlaneLine.exists_concentric_normalizer (L M : HalfPlaneLine) (hd : L.HDisjoint M) :
    ∃ (g : GL (Fin 2) ℝ) (s t : ℝ) (hs : 0<s) (ht : 0<t), 0<g.val.det ∧ s≠t ∧
      (g • · : ℍ → ℍ) '' L.carrier=(HalfPlaneLine.circle 0 s hs).carrier ∧
      (g • · : ℍ → ℍ) '' M.carrier=(HalfPlaneLine.circle 0 t ht).carrier := by
  obtain ⟨N,⟨⟨p,hp⟩,⟨q,hq⟩⟩,_⟩ := L.existsUnique_commonOrthogonal M hd
  obtain ⟨g,hg,hN⟩ := N.exists_mobius_map (HalfPlaneLine.vertical 0)
  obtain ⟨L',hL⟩ := realGL_image_hLine g L
  obtain ⟨M',hM⟩ := realGL_image_hLine g M
  have hp' := L.orthogonalAt_isometry_image N L' _ (g • ·) (realGL_isometry g) hL hN hp
  have hq' := M.orthogonalAt_isometry_image N M' _ (g • ·) (realGL_isometry g) hM hN hq
  have hcL := (L'.orthogonalAt_iff_coefficients _ _ hp'.1 hp'.2.1).mp hp'
  have hcM := (M'.orthogonalAt_iff_coefficients _ _ hq'.1 hq'.2.1).mp hq'
  cases L' with
  | vertical a => exact hcL.elim
  | circle a s hs =>
    change a=0 at hcL
    subst a
    cases M' with
    | vertical b => exact hcM.elim
    | circle b t ht =>
      change b=0 at hcM
      subst b
      refine ⟨g,s,t,hs,ht,hg,?_,hL,hM⟩
      intro he
      apply hd.1
      apply HalfPlaneLine.carrier_injective
      apply (realGL_isometry g).injective.image_injective
      rw [hL,hM]
      subst t
      rfl

theorem concentric_endpoint_crossRatio_distance (s t : ℝ) (hs : 0<s) (ht : 0<t) (hst : s≠t)
    (a b c d : OnePoint ℂ)
    (ha : a ∈ (HalfPlaneLine.circle 0 s hs).idealEndpoints)
    (hd : d ∈ (HalfPlaneLine.circle 0 s hs).idealEndpoints) (had : a≠d)
    (hb : b ∈ (HalfPlaneLine.circle 0 t ht).idealEndpoints)
    (hc : c ∈ (HalfPlaneLine.circle 0 t ht).idealEndpoints) (hbc : b≠c)
    (hR : 1<(Mobius.extendedCrossRatio a b c d).re) :
    Mobius.extendedCrossRatio a b c d*
      ((Real.tanh ((HalfPlaneLine.circle 0 s hs).lineDist (HalfPlaneLine.circle 0 t ht)/2)^2 : ℝ) : ℂ)=1 := by
  simp only [circle_idealEndpoints,zero_sub,zero_add,mem_insert_iff,mem_singleton_iff] at ha hb hc hd
  rcases ha with rfl | rfl
  · have hd' := hd.resolve_left (fun hh => had hh.symm)
    subst d
    rcases hb with rfl | rfl
    · have hc' := hc.resolve_left (fun hh => hbc hh.symm)
      subst c
      exact concentric_crossRatio_distance s t hs ht hst
    · have hc' := hc.resolve_right (fun hh => hbc hh.symm)
      subst c
      rw [concentric_crossRatio_opposite,Complex.ofReal_re] at hR
      exact (not_lt_of_ge (concentric_crossRatio_small s t hs ht).le hR).elim
  · have hd' := hd.resolve_right (fun hh => had hh.symm)
    subst d
    rcases hb with rfl | rfl
    · have hc' := hc.resolve_left (fun hh => hbc hh.symm)
      subst c
      rw [extendedCrossRatio_reverse_all,concentric_crossRatio_opposite,Complex.ofReal_re] at hR
      exact (not_lt_of_ge (concentric_crossRatio_small s t hs ht).le hR).elim
    · have hc' := hc.resolve_right (fun hh => hbc hh.symm)
      subst c
      rw [extendedCrossRatio_reverse_all]
      exact concentric_crossRatio_distance s t hs ht hst


/-- The ideal ends occur in the source actual cyclic order. -/
theorem HalfPlaneLine.endpoint_crossRatio_distance (L M : HalfPlaneLine) (hdis : L.HDisjoint M)
    (a b c d : OnePoint ℂ) (ha : a ∈ L.idealEndpoints) (hd : d ∈ L.idealEndpoints) (had : a≠d)
    (hb : b ∈ M.idealEndpoints) (hc : c ∈ M.idealEndpoints) (hbc : b≠c)
    (hcyc : HBoundaryCyclic a b c d) :
    Mobius.extendedCrossRatio a b c d*((Real.tanh (L.lineDist M/2)^2 : ℝ) : ℂ)=1 := by
  obtain ⟨g,s,t,hs,ht,hg,hst,hL,hM⟩ := L.exists_concentric_normalizer M hdis
  have hEL := L.idealEndpoints_realGL_image _ g hg hL
  have hEM := M.idealEndpoints_realGL_image _ g hg hM
  have hA : Mobius.fractionalLinear (complexifiedRealMobiusMatrix g) a ∈ (HalfPlaneLine.circle 0 s hs).idealEndpoints :=
    hEL.symm ▸ mem_image_of_mem _ ha
  have hD : Mobius.fractionalLinear (complexifiedRealMobiusMatrix g) d ∈ (HalfPlaneLine.circle 0 s hs).idealEndpoints :=
    hEL.symm ▸ mem_image_of_mem _ hd
  have hB : Mobius.fractionalLinear (complexifiedRealMobiusMatrix g) b ∈ (HalfPlaneLine.circle 0 t ht).idealEndpoints :=
    hEM.symm ▸ mem_image_of_mem _ hb
  have hC : Mobius.fractionalLinear (complexifiedRealMobiusMatrix g) c ∈ (HalfPlaneLine.circle 0 t ht).idealEndpoints :=
    hEM.symm ▸ mem_image_of_mem _ hc
  have hR := Mobius.extendedCrossRatio_fractionalLinear (complexifiedRealMobiusMatrix g) a b c d
  have hdist := L.lineDist_isometry_image M _ _ (g • ·) (realGL_isometry g) hL hM
  rw [← hdist,← hR]
  apply concentric_endpoint_crossRatio_distance s t hs ht hst _ _ _ _ hA hD
    ((Mobius.fractionalLinear (complexifiedRealMobiusMatrix g)).injective.ne had) hB hC
    ((Mobius.fractionalLinear (complexifiedRealMobiusMatrix g)).injective.ne hbc)
  rw [hR]
  exact hcyc.crossRatio_real_gt_one.2

/-- The same source cross-ratio identity on the actual native disc ideal circle. -/
theorem DiscLine.endpoint_crossRatio_distance (L M : DiscLine) (hdis : L.HDisjoint M)
    (a b c d : OnePoint ℂ) (ha : a ∈ L.idealEndpoints) (hd : d ∈ L.idealEndpoints) (had : a≠d)
    (hb : b ∈ M.idealEndpoints) (hc : c ∈ M.idealEndpoints) (hbc : b≠c)
    (hcyc : DBoundaryCyclic a b c d) :
    Mobius.extendedCrossRatio a b c d*((Real.tanh (L.lineDist M/2)^2 : ℝ) : ℂ)=1 := by
  have hmem (K : DiscLine) (u : OnePoint ℂ) (hu : u ∈ K.idealEndpoints) :
      extendedCayley.symm u ∈ K.toHalfPlane.idealEndpoints := by
    rw [K.idealEndpoints_eq_cayley_image] at hu
    obtain ⟨x,hx,rfl⟩ := hu
    simpa only [Homeomorph.symm_apply_apply] using hx
  have he := L.toHalfPlane.endpoint_crossRatio_distance M.toHalfPlane
    ((L.hDisjoint_iff_halfPlane M).mp hdis) (extendedCayley.symm a) (extendedCayley.symm b)
    (extendedCayley.symm c) (extendedCayley.symm d) (hmem L a ha) (hmem L d hd)
    (extendedCayley.symm.injective.ne had) (hmem M b hb) (hmem M c hc)
    (extendedCayley.symm.injective.ne hbc) (show HBoundaryCyclic _ _ _ _ from hcyc)
  rwa [extendedCrossRatio_inverseCayley,← L.lineDist_eq_halfPlane] at he

end
end LowDimensionalTopology.Geometry.Hyperbolic
