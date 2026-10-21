/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Hyperbolic.Metric.CommonOrthogonals

/-! # Actual projective cyclic order of the hyperbolic ideal boundary -/
@[expose] public section
open Set
open scoped UpperHalfPlane MatrixGroups Complex.UnitDisc OnePoint
namespace LowDimensionalTopology.Geometry.Hyperbolic
open LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
noncomputable section

/-- Cyclic order in a genuine oriented projective chart of the real ideal circle.
Both orientations of the listed quadruple are admitted. -/
def HBoundaryCyclic (a b c d : OnePoint ℂ) : Prop :=
  ∃ (g : GL (Fin 2) ℝ) (x y z : ℝ), 0 < g.val.det ∧
    Mobius.fractionalLinear (complexifiedRealMobiusMatrix g) a=∞ ∧
    Mobius.fractionalLinear (complexifiedRealMobiusMatrix g) b=((x : ℂ) : OnePoint ℂ) ∧
    Mobius.fractionalLinear (complexifiedRealMobiusMatrix g) c=((y : ℂ) : OnePoint ℂ) ∧
    Mobius.fractionalLinear (complexifiedRealMobiusMatrix g) d=((z : ℂ) : OnePoint ℂ) ∧
    ((x<y ∧ y<z) ∨ (z<y ∧ y<x))

theorem realMobius_fix_infty_coeff (g : GL (Fin 2) ℝ)
    (h : Mobius.fractionalLinear (complexifiedRealMobiusMatrix g) ∞=∞) : g 1 0=0 := by
  by_contra hn
  have hn' : (g 1 0 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hn
  rw [Mobius.fractionalLinear_infty] at h
  change (if (g 1 0 : ℂ)=0 then ∞ else
    (((g 0 0 : ℂ)/(g 1 0 : ℂ) : ℂ) : OnePoint ℂ))=∞ at h
  rw [ite_eq_right_iff.mpr (fun hh => (hn' hh).elim)] at h
  exact OnePoint.coe_ne_infty _ h

theorem realMobius_fix_infty_affine (g : GL (Fin 2) ℝ) (hg : 0<g.val.det)
    (h : Mobius.fractionalLinear (complexifiedRealMobiusMatrix g) ∞=∞) :
    ∃ α β : ℝ, 0<α ∧ ∀ x : ℝ, Mobius.fractionalLinear (complexifiedRealMobiusMatrix g) ((x : ℂ) : OnePoint ℂ)=
      (((α*x+β : ℝ) : ℂ) : OnePoint ℂ) := by
  have hc := realMobius_fix_infty_coeff g h
  have hd : 0<g 0 0*g 1 1 := by
    rw [Matrix.det_fin_two] at hg
    simpa only [hc,mul_zero,sub_zero] using hg
  have h11 : g 1 1 ≠ 0 := by intro he; rw [he,mul_zero] at hd; exact lt_irrefl _ hd
  have hα : 0<g 0 0/g 1 1 := by
    exact div_pos_iff.mpr (mul_pos_iff.mp hd)
  refine ⟨g 0 0/g 1 1,g 0 1/g 1 1,hα,?_⟩
  intro x
  rw [Mobius.fractionalLinear_coe]
  have hn : (g 1 0 : ℂ)*(x : ℂ)+g 1 1 ≠ 0 := by
    rw [hc,Complex.ofReal_zero,zero_mul,zero_add]
    exact Complex.ofReal_ne_zero.mpr h11
  change (if (g 1 0 : ℂ)*(x : ℂ)+g 1 1=0 then ∞ else
    ((((g 0 0 : ℂ)*(x : ℂ)+g 0 1)/((g 1 0 : ℂ)*(x : ℂ)+g 1 1) : ℂ) : OnePoint ℂ))=_
  rw [ite_eq_right_iff.mpr (fun hh => (hn hh).elim),hc,Complex.ofReal_zero,zero_mul,zero_add]
  apply OnePoint.coe_injective
  push_cast
  field_simp [Complex.ofReal_ne_zero.mpr h11]

theorem hBoundaryCyclic_infty_real (x y z : ℝ) :
    HBoundaryCyclic ∞ ((x : ℂ) : OnePoint ℂ) ((y : ℂ) : OnePoint ℂ) ((z : ℂ) : OnePoint ℂ) ↔
      (x<y ∧ y<z) ∨ (z<y ∧ y<x) := by
  constructor
  · rintro ⟨g,u,v,w,hg,hInf,hu,hv,hw,hord⟩
    obtain ⟨α,β,hα,hf⟩ := realMobius_fix_infty_affine g hg hInf
    have hu' : α*x+β=u := realOnePoint_injective ((hf x).symm.trans hu)
    have hv' : α*y+β=v := realOnePoint_injective ((hf y).symm.trans hv)
    have hw' : α*z+β=w := realOnePoint_injective ((hf z).symm.trans hw)
    rcases hord with h | h
    · left
      constructor <;> nlinarith [h.1,h.2]
    · right
      constructor <;> nlinarith [h.1,h.2]
  · intro h
    refine ⟨1,x,y,z,?_,?_,?_,?_,?_,h⟩
    · simp
    all_goals simp [complexifiedRealMobiusMatrix,Mobius.fractionalLinear_one]

theorem HBoundaryCyclic.realGL_image (a b c d : OnePoint ℂ) (g : GL (Fin 2) ℝ)
    (hg : 0<g.val.det) (h : HBoundaryCyclic a b c d) :
    HBoundaryCyclic (Mobius.fractionalLinear (complexifiedRealMobiusMatrix g) a)
      (Mobius.fractionalLinear (complexifiedRealMobiusMatrix g) b) (Mobius.fractionalLinear
        (complexifiedRealMobiusMatrix g) c)
      (Mobius.fractionalLinear (complexifiedRealMobiusMatrix g) d) := by
  obtain ⟨k,x,y,z,hk,ha,hb,hc,hd,ho⟩ := h
  have hmat : complexifiedRealMobiusMatrix (k*g⁻¹)=complexifiedRealMobiusMatrix k*(complexifiedRealMobiusMatrix g)⁻¹ := by
    unfold complexifiedRealMobiusMatrix
    rw [map_mul,map_inv]
  refine ⟨k*g⁻¹,x,y,z,gl_pos_mul k g⁻¹ hk (gl_pos_inverse g hg),?_,?_,?_,?_,ho⟩
  all_goals
    rwa [hmat,Mobius.fractionalLinear_mul,Mobius.fractionalLinear_inv_apply]

theorem HBoundaryCyclic.crossRatio_real_gt_one {a b c d : OnePoint ℂ}
    (h : HBoundaryCyclic a b c d) :
    (Mobius.extendedCrossRatio a b c d).im=0 ∧ 1<(Mobius.extendedCrossRatio a b c d).re := by
  obtain ⟨g,x,y,z,hg,ha,hb,hc,hd,ho⟩ := h
  have he := Mobius.extendedCrossRatio_fractionalLinear (complexifiedRealMobiusMatrix g) a b c d
  rw [ha,hb,hc,hd,Mobius.extendedCrossRatio_infty_first] at he
  have he' : Mobius.extendedCrossRatio a b c d=(((x-z)/(y-z) : ℝ) : ℂ) := by
    rw [← he]
    push_cast
    rfl
  rw [he',Complex.ofReal_im,Complex.ofReal_re]
  refine ⟨rfl,?_⟩
  rcases ho with ho | ho
  · exact (one_lt_div_of_neg (sub_neg.mpr ho.2)).mpr (by linarith [ho.1])
  · exact (one_lt_div₀ (sub_pos.mpr ho.1)).mpr (by linarith [ho.2])


theorem hBoundaryCyclic_realGL_iff (a b c d : OnePoint ℂ) (g : GL (Fin 2) ℝ)
    (hg : 0<g.val.det) :
    HBoundaryCyclic (Mobius.fractionalLinear (complexifiedRealMobiusMatrix g) a)
      (Mobius.fractionalLinear (complexifiedRealMobiusMatrix g) b) (Mobius.fractionalLinear
        (complexifiedRealMobiusMatrix g) c)
      (Mobius.fractionalLinear (complexifiedRealMobiusMatrix g) d) ↔ HBoundaryCyclic a b c d := by
  refine ⟨fun h => ?_,fun h => h.realGL_image a b c d g hg⟩
  have hi := h.realGL_image _ _ _ _ g⁻¹ (gl_pos_inverse g hg)
  simpa only [realMobiusMatrix_inv,Mobius.fractionalLinear_inv_apply] using hi

theorem hBoundaryCyclic_chart_iff (a b c d : OnePoint ℂ) (g : GL (Fin 2) ℝ)
    (hg : 0<g.val.det) (x y z : ℝ)
    (ha : Mobius.fractionalLinear (complexifiedRealMobiusMatrix g) a=∞)
    (hb : Mobius.fractionalLinear (complexifiedRealMobiusMatrix g) b=((x : ℂ) : OnePoint ℂ))
    (hc : Mobius.fractionalLinear (complexifiedRealMobiusMatrix g) c=((y : ℂ) : OnePoint ℂ))
    (hd : Mobius.fractionalLinear (complexifiedRealMobiusMatrix g) d=((z : ℂ) : OnePoint ℂ)) :
    HBoundaryCyclic a b c d ↔ (x<y ∧ y<z) ∨ (z<y ∧ y<x) := by
  rw [← hBoundaryCyclic_realGL_iff a b c d g hg,ha,hb,hc,hd,hBoundaryCyclic_infty_real]

theorem exists_boundaryProjectiveChart {a : OnePoint ℂ} (ha : a ∈ halfPlaneIdealBoundary) :
    ∃ g : GL (Fin 2) ℝ, 0<g.val.det ∧ Mobius.fractionalLinear (complexifiedRealMobiusMatrix g) a=∞ := by
  rw [halfPlaneIdealBoundary_eq_real_infty] at ha
  rcases ha with rfl | ⟨x,rfl⟩
  · refine ⟨1,?_,?_⟩ <;> simp [complexifiedRealMobiusMatrix,Mobius.fractionalLinear_one]
  · let g : GL (Fin 2) ℝ := Matrix.GeneralLinearGroup.mkOfDetNeZero !![0,-1;1,-x]
      (by simp [Matrix.det_fin_two])
    refine ⟨g,by simp [g,Matrix.det_fin_two],?_⟩
    rw [Mobius.fractionalLinear_coe]
    simp [g,complexifiedRealMobiusMatrix]


theorem HBoundaryCyclic.boundary {a b c d : OnePoint ℂ} (h : HBoundaryCyclic a b c d) :
    a ∈ halfPlaneIdealBoundary ∧ b ∈ halfPlaneIdealBoundary ∧
      c ∈ halfPlaneIdealBoundary ∧ d ∈ halfPlaneIdealBoundary := by
  obtain ⟨g,x,y,z,_,ha,hb,hc,hd,_⟩ := h
  have hback {p q : OnePoint ℂ} (he : Mobius.fractionalLinear (complexifiedRealMobiusMatrix g) p=q)
      (hq : q ∈ halfPlaneIdealBoundary) : p ∈ halfPlaneIdealBoundary := by
    rw [← realMobiusMatrix_preimage_boundary g]
    change Mobius.fractionalLinear (complexifiedRealMobiusMatrix g) p ∈ halfPlaneIdealBoundary
    rw [he]
    exact hq
  refine ⟨hback ha ?_,hback hb ?_,hback hc ?_,hback hd ?_⟩
  · simp [halfPlaneIdealBoundary]
  all_goals simp [coe_mem_halfPlaneIdealBoundary]

/-- The actual native boundary circle order, using the genuine compactified Cayley chart. -/
def DBoundaryCyclic (a b c d : OnePoint ℂ) : Prop :=
  HBoundaryCyclic (extendedCayley.symm a) (extendedCayley.symm b)
    (extendedCayley.symm c) (extendedCayley.symm d)

theorem dBoundaryCyclic_cayley_iff (a b c d : OnePoint ℂ) :
    DBoundaryCyclic (extendedCayley a) (extendedCayley b) (extendedCayley c) (extendedCayley d) ↔
      HBoundaryCyclic a b c d := by
  simp only [DBoundaryCyclic,Homeomorph.symm_apply_apply]

theorem extendedCrossRatio_inverseCayley (a b c d : OnePoint ℂ) :
    Mobius.extendedCrossRatio (extendedCayley.symm a) (extendedCayley.symm b)
      (extendedCayley.symm c) (extendedCayley.symm d)=Mobius.extendedCrossRatio a b c d := by
  have he := Mobius.extendedCrossRatio_fractionalLinear extendedCayleyMatrix
    (extendedCayley.symm a) (extendedCayley.symm b) (extendedCayley.symm c) (extendedCayley.symm d)
  change Mobius.extendedCrossRatio (extendedCayley (extendedCayley.symm a))
    (extendedCayley (extendedCayley.symm b)) (extendedCayley (extendedCayley.symm c))
    (extendedCayley (extendedCayley.symm d))=_ at he
  simpa only [Homeomorph.apply_symm_apply] using he.symm

theorem DBoundaryCyclic.crossRatio_real_gt_one {a b c d : OnePoint ℂ}
    (h : DBoundaryCyclic a b c d) :
    (Mobius.extendedCrossRatio a b c d).im=0 ∧ 1<(Mobius.extendedCrossRatio a b c d).re := by
  have he := (show HBoundaryCyclic _ _ _ _ from h).crossRatio_real_gt_one
  rwa [extendedCrossRatio_inverseCayley] at he

end
end LowDimensionalTopology.Geometry.Hyperbolic
