/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Hyperbolic.Trigonometry.TriangleSineRules
public import Mathlib.Analysis.SpecialFunctions.Arcosh

@[expose] public section
open Set
open scoped UpperHalfPlane MatrixGroups Complex.UnitDisc
namespace LowDimensionalTopology.Geometry.Hyperbolic
noncomputable section

theorem exists_sl2_normalized_pair (z w : ℍ) (hzw : z ≠ w) :
    ∃ s : Matrix.SpecialLinearGroup (Fin 2) ℝ, ∃ k : ℝ, ∃ hk : 1 < k,
      s • z = UpperHalfPlane.I ∧ s • w = metricProbe 0 k (lt_trans zero_lt_one hk) := by
  obtain ⟨s,hz,hw,hlt⟩ := exists_sl2_ordered_imaginary z w hzw
  let d := verticalDilationSL (1 / (s • z).im) (by positivity)
  let k := (s • w).im / (s • z).im
  have hk : 1 < k := (one_lt_div (s • z).im_pos).mpr hlt
  refine ⟨d * s,k,hk,?_,?_⟩
  · apply UpperHalfPlane.ext
    apply Complex.ext
    · change ((d * s) • z).re = 0
      rw [mul_smul,verticalDilationSL_re,hz,mul_zero]
    · change ((d * s) • z).im = 1
      rw [mul_smul,verticalDilationSL_im]
      exact one_div_mul_cancel (s • z).im_ne_zero
  · apply UpperHalfPlane.ext
    apply Complex.ext
    · change ((d * s) • w).re = 0
      rw [mul_smul,verticalDilationSL_re,hw,mul_zero]
    · change ((d * s) • w).im = k
      rw [mul_smul,verticalDilationSL_im]
      dsimp only [k]
      ring

theorem imaginary_probes_parameter_eq {k l : ℝ} (hk : 1 < k) (hl : 1 < l)
    (h : dist UpperHalfPlane.I (metricProbe 0 k (lt_trans zero_lt_one hk)) =
      dist UpperHalfPlane.I (metricProbe 0 l (lt_trans zero_lt_one hl))) : k = l := by
  have hc := congrArg Real.cosh h
  rw [UpperHalfPlane.cosh_dist',UpperHalfPlane.cosh_dist'] at hc
  norm_num [metricProbe] at hc
  have he := (div_eq_div_iff (by positivity : 2 * k ≠ 0)
    (by positivity : 2 * l ≠ 0)).mp hc
  have hf : (k - l) * (k * l - 1) = 0 := by nlinarith only [he]
  have hkl : k * l - 1 ≠ 0 := ne_of_gt (by nlinarith)
  exact sub_eq_zero.mp ((mul_eq_zero.mp hf).resolve_right hkl)

theorem equal_two_imaginary_probe_distances {z w : ℍ} {k : ℝ} (hk : 1 < k)
    (h₁ : dist z UpperHalfPlane.I = dist w UpperHalfPlane.I)
    (h₂ : dist z (metricProbe 0 k (lt_trans zero_lt_one hk)) =
      dist w (metricProbe 0 k (lt_trans zero_lt_one hk))) :
    z.im = w.im ∧ z.re ^ 2 = w.re ^ 2 := by
  have h₁' := congrArg Real.cosh h₁
  have h₂' := congrArg Real.cosh h₂
  rw [UpperHalfPlane.cosh_dist',UpperHalfPlane.cosh_dist'] at h₁' h₂'
  norm_num [metricProbe] at h₁' h₂'
  have hA := (div_eq_div_iff (by positivity : 2 * z.im ≠ 0)
    (by positivity : 2 * w.im ≠ 0)).mp h₁'
  simp only [div_mul_eq_div_div] at h₂'
  have h₂'' : (z.re ^ 2 + z.im ^ 2 + k ^ 2) / (2 * z.im) =
      (w.re ^ 2 + w.im ^ 2 + k ^ 2) / (2 * w.im) := by
    apply (div_left_inj' (by positivity : k ≠ 0)).mp
    simpa only [div_mul_eq_div_div] using h₂'
  have hB := (div_eq_div_iff (by positivity : 2 * z.im ≠ 0)
    (by positivity : 2 * w.im ≠ 0)).mp h₂''
  have hf : (z.im - w.im) * (k ^ 2 - 1) = 0 := by
    nlinarith only [hA,hB]
  have hk' : k ^ 2 - 1 ≠ 0 := ne_of_gt (by nlinarith)
  have hy : z.im = w.im := sub_eq_zero.mp ((mul_eq_zero.mp hf).resolve_right hk')
  refine ⟨hy,?_⟩
  rw [hy] at hA
  nlinarith [w.im_pos]

/-- Three pairwise distances determine an actual hyperbolic triangle up to an actual isometry. -/
theorem HTriangle.exists_isometry_of_lengths_eq (T S : HTriangle)
    (hA : T.lengthA = S.lengthA) (hB : T.lengthB = S.lengthB)
    (hC : T.lengthC = S.lengthC) :
    ∃ g : GL (Fin 2) ℝ, g • T.a = S.a ∧ g • T.b = S.b ∧ g • T.c = S.c := by
  obtain ⟨s,k,hk,hsa,hsb⟩ := exists_sl2_normalized_pair T.a T.b T.a_ne_b
  obtain ⟨t,l,hl,hta,htb⟩ := exists_sl2_normalized_pair S.a S.b S.a_ne_b
  have hd : dist UpperHalfPlane.I (metricProbe 0 k (lt_trans zero_lt_one hk)) =
      dist UpperHalfPlane.I (metricProbe 0 l (lt_trans zero_lt_one hl)) := by
    have he : dist (s • T.a) (s • T.b) = dist (t • S.a) (t • S.b) := by
      rw [(isometry_smul ℍ s).dist_eq,(isometry_smul ℍ t).dist_eq]
      exact hC
    simpa only [hsa,hsb,hta,htb] using he
  have hkl := imaginary_probes_parameter_eq hk hl hd
  subst l
  have h₁ : dist (s • T.c) UpperHalfPlane.I = dist (t • S.c) UpperHalfPlane.I := by
    have he : dist (s • T.c) (s • T.a) = dist (t • S.c) (t • S.a) := by
      rw [(isometry_smul ℍ s).dist_eq,(isometry_smul ℍ t).dist_eq]
      exact hB
    simpa only [hsa,hta] using he
  have h₂ : dist (s • T.c) (metricProbe 0 k (lt_trans zero_lt_one hk)) =
      dist (t • S.c) (metricProbe 0 k (lt_trans zero_lt_one hk)) := by
    have he : dist (s • T.c) (s • T.b) = dist (t • S.c) (t • S.b) := by
      rw [(isometry_smul ℍ s).dist_eq,(isometry_smul ℍ t).dist_eq]
      exact dist_comm T.c T.b |>.trans (hA.trans (dist_comm S.b S.c))
    simpa only [hsb,htb] using he
  obtain ⟨hy,hx⟩ := equal_two_imaginary_probe_distances hk h₁ h₂
  have hor : s • T.c = t • S.c ∨ UpperHalfPlane.J • (s • T.c) = t • S.c := by
    rcases (sq_eq_sq_iff_eq_or_eq_neg).mp hx with h | h
    · left
      apply UpperHalfPlane.ext
      exact Complex.ext h hy
    · right
      apply UpperHalfPlane.ext
      apply Complex.ext
      · rw [UpperHalfPlane.coe_J_smul]
        change -(s • T.c).re = (t • S.c).re
        linarith
      · rw [UpperHalfPlane.coe_J_smul]
        simpa only [Complex.neg_im,Complex.conj_im,neg_neg,UpperHalfPlane.coe_im] using hy
  let s' := Matrix.SpecialLinearGroup.mapGL ℝ s
  let t' := Matrix.SpecialLinearGroup.mapGL ℝ t
  rcases hor with hor | hor
  · refine ⟨t'⁻¹ * s',?_,?_,?_⟩
    all_goals rw [mul_smul,inv_smul_eq_iff]
    · exact hsa.trans hta.symm
    · exact hsb.trans htb.symm
    · exact hor
  · refine ⟨t'⁻¹ * UpperHalfPlane.J * s',?_,?_,?_⟩
    all_goals rw [mul_smul,mul_smul,inv_smul_eq_iff]
    · change UpperHalfPlane.J • (s • T.a) = t • S.a
      rw [hsa,hta]
      apply UpperHalfPlane.ext
      rw [UpperHalfPlane.coe_J_smul]
      apply Complex.ext <;> norm_num
    · change UpperHalfPlane.J • (s • T.b) = t • S.b
      rw [hsb,htb]
      apply UpperHalfPlane.ext
      rw [UpperHalfPlane.coe_J_smul]
      apply Complex.ext <;> simp [metricProbe]
    · exact hor

theorem HTriangle.cosine_rule_II_A (T : HTriangle) :
    Real.cosh T.lengthA = (Real.cos T.beta * Real.cos T.gamma + Real.cos T.alpha) /
      (Real.sin T.beta * Real.sin T.gamma) :=
  hyperbolic_second_cosine_rule T.lengths_pos.2.1 T.lengths_pos.2.2 T.lengths_pos.1
    T.angles_mem_Ioo.2.1 T.angles_mem_Ioo.2.2 T.cosine_rule_B T.cosine_rule_I T.cosine_rule_A

theorem HTriangle.cosine_rule_II_B (T : HTriangle) :
    Real.cosh T.lengthB = (Real.cos T.gamma * Real.cos T.alpha + Real.cos T.beta) /
      (Real.sin T.gamma * Real.sin T.alpha) :=
  hyperbolic_second_cosine_rule T.lengths_pos.2.2 T.lengths_pos.1 T.lengths_pos.2.1
    T.angles_mem_Ioo.2.2 T.angles_mem_Ioo.1 T.cosine_rule_I T.cosine_rule_A T.cosine_rule_B

theorem HTriangle.lengths_eq_of_angles_eq (T S : HTriangle)
    (hα : T.alpha = S.alpha) (hβ : T.beta = S.beta) (hγ : T.gamma = S.gamma) :
    T.lengthA = S.lengthA ∧ T.lengthB = S.lengthB ∧ T.lengthC = S.lengthC := by
  have hA := T.cosine_rule_II_A
  have hB := T.cosine_rule_II_B
  have hC := T.cosine_rule_II
  rw [hα,hβ,hγ] at hA hB hC
  exact ⟨Real.cosh_injOn T.lengths_pos.1.le S.lengths_pos.1.le (hA.trans S.cosine_rule_II_A.symm),
    Real.cosh_injOn T.lengths_pos.2.1.le S.lengths_pos.2.1.le (hB.trans S.cosine_rule_II_B.symm),
    Real.cosh_injOn T.lengths_pos.2.2.le S.lengths_pos.2.2.le (hC.trans S.cosine_rule_II.symm)⟩

/-- Actual hyperbolic triangles with corresponding equal angles have an actual isometry
carrying all three corresponding vertices to one another. -/
theorem HTriangle.exists_isometry_of_angles_eq (T S : HTriangle)
    (hα : T.alpha = S.alpha) (hβ : T.beta = S.beta) (hγ : T.gamma = S.gamma) :
    ∃ g : GL (Fin 2) ℝ, g • T.a = S.a ∧ g • T.b = S.b ∧ g • T.c = S.c := by
  obtain ⟨hA,hB,hC⟩ := T.lengths_eq_of_angles_eq S hα hβ hγ
  exact T.exists_isometry_of_lengths_eq S hA hB hC

theorem realGL_image_line_of_corresponding_points (g : GL (Fin 2) ℝ)
    (L M : HalfPlaneLine) {z w : ℍ} (hzw : z ≠ w)
    (hzL : z ∈ L.carrier) (hwL : w ∈ L.carrier)
    (hzM : g • z ∈ M.carrier) (hwM : g • w ∈ M.carrier) :
    (g • · : ℍ → ℍ) '' L.carrier = M.carrier := by
  obtain ⟨N,hN⟩ := realGL_image_hLine g L
  have he : N = M := N.eq_of_two_points M ((realGL_isometry g).injective.ne hzw)
    (hN ▸ mem_image_of_mem (g • ·) hzL) (hN ▸ mem_image_of_mem (g • ·) hwL) hzM hwM
  rwa [he] at hN

theorem realGL_image_openHalfPlane (g : GL (Fin 2) ℝ) (L M : HalfPlaneLine)
    (hLM : (g • · : ℍ → ℍ) '' L.carrier = M.carrier) (z : ℍ) (hz : z ∉ L.carrier) :
    (g • · : ℍ → ℍ) '' openHHalfPlane L z = openHHalfPlane M (g • z) := by
  have he := (Homeomorph.smul g : ℍ ≃ₜ ℍ).image_connectedComponentIn
    (show z ∈ L.carrierᶜ from hz)
  have hc : (g • · : ℍ → ℍ) '' L.carrierᶜ = M.carrierᶜ := by
    rw [← hLM]
    exact (Homeomorph.smul g : ℍ ≃ₜ ℍ).toEquiv.image_compl L.carrier
  change (g • · : ℍ → ℍ) '' openHHalfPlane L z =
    connectedComponentIn ((g • · : ℍ → ℍ) '' L.carrierᶜ) (g • z) at he
  rwa [hc] at he

/-- An actual real fractional-linear map carrying the vertices also carries the actual open triangle. -/
theorem HTriangle.realGL_image_interior (T S : HTriangle) (g : GL (Fin 2) ℝ)
    (ha : g • T.a = S.a) (hb : g • T.b = S.b) (hc : g • T.c = S.c) :
    (g • · : ℍ → ℍ) '' T.interior = S.interior := by
  have hA := realGL_image_line_of_corresponding_points g T.sideLineA S.sideLineA T.b_ne_c
    T.rayBC.start_mem_support (T.rayBC.subset_support T.c_mem_rayBC)
    (hb ▸ S.rayBC.start_mem_support) (hc ▸ S.rayBC.subset_support S.c_mem_rayBC)
  have hB := realGL_image_line_of_corresponding_points g T.sideLineB S.sideLineB T.c_ne_a
    T.rayCA.start_mem_support (T.rayCA.subset_support T.a_mem_rayCA)
    (hc ▸ S.rayCA.start_mem_support) (ha ▸ S.rayCA.subset_support S.a_mem_rayCA)
  have hC := realGL_image_line_of_corresponding_points g T.sideLineC S.sideLineC T.a_ne_b
    T.rayAB.start_mem_support (T.rayAB.subset_support T.b_mem_rayAB)
    (ha ▸ S.rayAB.start_mem_support) (hb ▸ S.rayAB.subset_support S.b_mem_rayAB)
  rw [T.interior_eq_halfPlanes,S.interior_eq_halfPlanes,
    image_inter (realGL_isometry g).injective,image_inter (realGL_isometry g).injective]
  simp only [HTriangle.halfPlaneA,HTriangle.halfPlaneB,HTriangle.halfPlaneC]
  rw [realGL_image_openHalfPlane g T.sideLineA S.sideLineA hA T.a T.a_not_mem_sideLineA,
    realGL_image_openHalfPlane g T.sideLineB S.sideLineB hB T.b T.b_not_mem_sideLineB,
    realGL_image_openHalfPlane g T.sideLineC S.sideLineC hC T.c T.c_not_mem_sideLineC,ha,hb,hc]

theorem HTriangle.angles_determine_triangle_isometry (T S : HTriangle)
    (hα : T.alpha = S.alpha) (hβ : T.beta = S.beta) (hγ : T.gamma = S.gamma) :
    ∃ g : GL (Fin 2) ℝ, g • T.a = S.a ∧ g • T.b = S.b ∧ g • T.c = S.c ∧
      (g • · : ℍ → ℍ) '' T.interior = S.interior := by
  obtain ⟨g,ha,hb,hc⟩ := T.exists_isometry_of_angles_eq S hα hβ hγ
  exact ⟨g,ha,hb,hc,T.realGL_image_interior S g ha hb hc⟩

def discRealGLHomeomorph (g : GL (Fin 2) ℝ) : 𝔻 ≃ₜ 𝔻 :=
  cayleyHomeomorph.symm.trans ((Homeomorph.smul g).trans cayleyHomeomorph)

theorem discRealGLHomeomorph_distance (g : GL (Fin 2) ℝ) (z w : 𝔻) :
    discPathDist (discRealGLHomeomorph g z) (discRealGLHomeomorph g w) = discPathDist z w := by
  change discPathDist (halfPlaneToDisc (g • discToHalfPlane z))
    (halfPlaneToDisc (g • discToHalfPlane w)) = discPathDist z w
  rw [discPathDist_eq_halfPlane,discToHalfPlane_halfPlaneToDisc,discToHalfPlane_halfPlaneToDisc,
    (realGL_isometry g).dist_eq,discPathDist_eq_halfPlane]

theorem DiscTriangle.angles_determine_triangle_isometry (T S : DiscTriangle)
    (hα : T.alpha = S.alpha) (hβ : T.beta = S.beta) (hγ : T.gamma = S.gamma) :
    ∃ e : 𝔻 ≃ₜ 𝔻, (∀ z w, discPathDist (e z) (e w) = discPathDist z w) ∧
      e T.a = S.a ∧ e T.b = S.b ∧ e T.c = S.c ∧ e '' T.interior = S.interior := by
  have hα' : T.toHalfPlane.alpha = S.toHalfPlane.alpha :=
    T.angles_eq_halfPlane.1.symm.trans (hα.trans S.angles_eq_halfPlane.1)
  have hβ' : T.toHalfPlane.beta = S.toHalfPlane.beta :=
    T.angles_eq_halfPlane.2.1.symm.trans (hβ.trans S.angles_eq_halfPlane.2.1)
  have hγ' : T.toHalfPlane.gamma = S.toHalfPlane.gamma :=
    T.angles_eq_halfPlane.2.2.symm.trans (hγ.trans S.angles_eq_halfPlane.2.2)
  obtain ⟨g,ha,hb,hc,hi⟩ := T.toHalfPlane.angles_determine_triangle_isometry S.toHalfPlane hα' hβ' hγ'
  refine ⟨discRealGLHomeomorph g,discRealGLHomeomorph_distance g,?_,?_,?_,?_⟩
  · change halfPlaneToDisc (g • discToHalfPlane T.a) = S.a
    exact (congrArg halfPlaneToDisc ha).trans (halfPlaneToDisc_discToHalfPlane S.a)
  · change halfPlaneToDisc (g • discToHalfPlane T.b) = S.b
    exact (congrArg halfPlaneToDisc hb).trans (halfPlaneToDisc_discToHalfPlane S.b)
  · change halfPlaneToDisc (g • discToHalfPlane T.c) = S.c
    exact (congrArg halfPlaneToDisc hc).trans (halfPlaneToDisc_discToHalfPlane S.c)
  · rw [T.interior_eq_cayley,S.interior_eq_cayley,image_image]
    have he : (fun z : ℍ => discRealGLHomeomorph g (halfPlaneToDisc z)) =
        (fun z : ℍ => halfPlaneToDisc (g • z)) := by
      funext z
      change halfPlaneToDisc (g • discToHalfPlane (halfPlaneToDisc z)) = _
      rw [discToHalfPlane_halfPlaneToDisc]
    rw [he]
    rw [← image_image,hi]

end
end LowDimensionalTopology.Geometry.Hyperbolic
