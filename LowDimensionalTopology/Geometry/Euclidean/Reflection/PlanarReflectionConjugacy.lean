/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Euclidean.Reflection.FiniteDihedralGroups
public import LowDimensionalTopology.Geometry.Euclidean.Reflection.AngleNormalForms
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Topology
open scoped ComplexConjugate
namespace LowDimensionalTopology.Geometry.Euclidean

/-- An actual planar orthogonal chart conjugates mirrors to the actual image mirror. -/
theorem finitePlanarOrthogonalMap_conjugate_mirror (a v : Circle) (b : Bool) :
    finitePlanarOrthogonalMap a b*finitePlanarOrthogonalMap (v*v) true*
      (finitePlanarOrthogonalMap a b)⁻¹=
      finitePlanarOrthogonalMap
        ((a*(if b then v⁻¹ else v))*(a*(if b then v⁻¹ else v))) true := by
  rw [finitePlanarOrthogonalMap_inv,finitePlanarOrthogonalMap_mul,finitePlanarOrthogonalMap_mul]
  cases b <;> simp only [Bool.false_eq_true,ite_false,ite_true,Bool.false_xor,Bool.true_xor,
    Bool.not_true,Bool.not_false,inv_inv]
  · congr 1
    ac_rfl
  · congr 1
    rw [mul_inv_rev]
    ac_rfl

def planarUnitDirection (L : ℂ ≃ₗᵢ[ℝ] ℂ) (v : Circle) : Circle :=
  ⟨L (v:ℂ),mem_sphere_zero_iff_norm.mpr (by rw [L.norm_map,Circle.norm_coe])⟩

theorem planarUnitDirection_coe (L : ℂ ≃ₗᵢ[ℝ] ℂ) (v : Circle) :
    (planarUnitDirection L v:ℂ)=L (v:ℂ) := rfl

theorem planarUnitDirection_normal_form (a v : Circle) (b : Bool) :
    planarUnitDirection (finitePlanarOrthogonalMap a b) v=a*(if b then v⁻¹ else v) := by
  apply Circle.ext
  cases b <;> simp only [planarUnitDirection_coe,finitePlanarOrthogonalMap_apply,
    Bool.false_eq_true,ite_false,ite_true,Circle.coe_mul,Circle.coe_inv_eq_conj]

/-- This conjugacy holds for every actual real-linear isometry, without orientation assumptions. -/
theorem planar_reflection_conjugation (L : ℂ ≃ₗᵢ[ℝ] ℂ) (v : Circle) :
    L*finitePlanarOrthogonalMap (v*v) true*L⁻¹=
      finitePlanarOrthogonalMap ((planarUnitDirection L v)*(planarUnitDirection L v)) true := by
  obtain ⟨a,ha|ha⟩:=linear_isometry_complex L
  · change L=finitePlanarOrthogonalMap a false at ha
    subst L
    rw [planarUnitDirection_normal_form]
    exact finitePlanarOrthogonalMap_conjugate_mirror a v false
  · change L=finitePlanarOrthogonalMap a true at ha
    subst L
    rw [planarUnitDirection_normal_form]
    exact finitePlanarOrthogonalMap_conjugate_mirror a v true

/-- The original two actual mirrors in arbitrary proper unit-ray directions. -/
def planarMirrorGroup (u v : Circle) : Subgroup (ℂ ≃ₗᵢ[ℝ] ℂ) :=
  Subgroup.closure {finitePlanarOrthogonalMap (u*u) true,finitePlanarOrthogonalMap (v*v) true}

/-- An actual angular chart proves finiteness of the original two-reflection subgroup. -/
theorem planarMirrorGroup_finite_of_chart (n : ℕ) (hn : 0<n) (u v : Circle)
    (L : ℂ ≃ₗᵢ[ℝ] ℂ) (hu : planarUnitDirection L u=1)
    (hv : planarUnitDirection L v=Circle.exp (finiteRotationPeriod n/2)) :
    (planarMirrorGroup u v : Set (ℂ ≃ₗᵢ[ℝ] ℂ)).Finite := by
  let f : (ℂ ≃ₗᵢ[ℝ] ℂ)→* (ℂ ≃ₗᵢ[ℝ] ℂ):=(MulAut.conj L).toMonoidHom
  have hle : planarMirrorGroup u v≤(finitePlanarDihedralGroup n).comap f:=by
    apply (Subgroup.closure_le _).mpr
    rintro g (rfl|hg)
    · change L*finitePlanarOrthogonalMap (u*u) true*L⁻¹∈finitePlanarDihedralGroup n
      rw [planar_reflection_conjugation,hu,one_mul]
      exact Subgroup.subset_closure (Or.inl rfl)
    · have he : g=finitePlanarOrthogonalMap (v*v) true:=mem_singleton_iff.mp hg
      subst g
      change L*finitePlanarOrthogonalMap (v*v) true*L⁻¹∈finitePlanarDihedralGroup n
      rw [planar_reflection_conjugation,hv,←pow_two,finiteRotationGenerator_half_square]
      exact Subgroup.subset_closure (Or.inr (mem_singleton _))
  have hi : Function.Injective f:=(MulAut.conj L).injective
  exact ((finitePlanarDihedralGroup_finite n hn).preimage hi.injOn).subset hle

/-- The original two mirrors generate a finite actual group whenever their genuine angle is pi/n. -/
theorem planarMirrorGroup_finite_of_angle (n : ℕ) (hn : 2≤n) (u v : Circle)
    (hangle : InnerProductGeometry.angle (u:ℂ) (v:ℂ)=Real.pi/(n:ℝ)) :
    (planarMirrorGroup u v : Set (ℂ ≃ₗᵢ[ℝ] ℂ)).Finite := by
  have hnpos : 0<n:=by omega
  have hnR : (2:ℝ)≤(n:ℝ):=by exact_mod_cast hn
  have hnRpos : 0<(n:ℝ):=by positivity
  have hθπ : Real.pi/(n:ℝ)<Real.pi:=by
    apply (div_lt_iff₀ hnRpos).mpr
    nlinarith [Real.pi_pos]
  have hperiod : finiteRotationPeriod n/2=Real.pi/(n:ℝ):=by
    dsimp only [finiteRotationPeriod]
    ring
  obtain ⟨L,hL⟩:=circle_pair_rotation_normal_form u v (finiteRotationPeriod n/2)
    (hangle.trans hperiod.symm) (by rwa [hperiod])
  rcases hL with ⟨h1,h2⟩|⟨h1,h2⟩
  · exact planarMirrorGroup_finite_of_chart n hnpos u v L (Circle.ext h1) (Circle.ext h2)
  · have he : planarMirrorGroup u v=planarMirrorGroup v u:=by
      simp only [planarMirrorGroup,Set.pair_comm]
    rw [he]
    exact planarMirrorGroup_finite_of_chart n hnpos v u L (Circle.ext h1) (Circle.ext h2)

end LowDimensionalTopology.Geometry.Euclidean
