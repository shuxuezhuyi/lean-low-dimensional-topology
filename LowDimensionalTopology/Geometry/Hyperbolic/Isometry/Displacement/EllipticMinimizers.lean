/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Hyperbolic.Isometry.Displacement.DisplacementInvariants
public import LowDimensionalTopology.Geometry.Hyperbolic.Convexity.ModelCoordinates
public import LowDimensionalTopology.Geometry.Hyperbolic.Isometry.Displacement.EllipticRotationAngles
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set
open scoped UpperHalfPlane
namespace LowDimensionalTopology.Geometry.Hyperbolic
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- An actual geodesic segment contains a point balancing any two positive radial weights. -/
theorem exists_balanced_radial_point (u v : ℍ) (A B : ℝ) (hA : 0<A) (hB : 0<B) :
    ∃ z∈closedHSegment u v,
      A*Real.sinh (dist u z)=B*Real.sinh (dist v z) := by
  by_cases he : u=v
  · subst v
    refine ⟨u,?_,?_⟩
    · rw [closedHSegment_self]
      exact Set.mem_singleton _
    · simp only [dist_self,Real.sinh_zero,mul_zero]
  · obtain ⟨a,b,γ,s,t,_,_,_,hγ,hline,hst,hs,ht,_⟩:=
      exists_ordered_geodesic_distance_crossRatio u v he
    let F : ℝ→ℝ:=fun r=>A*Real.sinh (dist u (γ r))-B*Real.sinh (dist v (γ r))
    have hγc : Continuous γ:=hγ.continuous
    have hF : Continuous F := by dsimp [F];fun_prop
    have hFs : F s≤0 := by
      dsimp only [F]
      rw [hs,dist_self,Real.sinh_zero,mul_zero,zero_sub]
      exact neg_nonpos.mpr (mul_nonneg hB.le (Real.sinh_nonneg_iff.mpr dist_nonneg))
    have hFt : 0≤F t := by
      dsimp only [F]
      rw [ht,dist_self,Real.sinh_zero,mul_zero,sub_zero]
      exact mul_nonneg hA.le (Real.sinh_nonneg_iff.mpr dist_nonneg)
    obtain ⟨r,hr,hFr⟩:=intermediate_value_Icc hst.le hF.continuousOn ⟨hFs,hFt⟩
    refine ⟨γ r,?_,sub_eq_zero.mp hFr⟩
    rw [←hs,←ht,closedHSegment_eq_image_Icc ⟨hγ,hline⟩ hst]
    exact ⟨r,hr,rfl⟩

/-- Balancing on the actual joining segment minimizes the larger radial displacement globally. -/
theorem balanced_radial_point_minimizes (u v z : ℍ) (hz : z∈closedHSegment u v)
    (A B : ℝ) (hA : 0≤A) (hB : 0≤B)
    (heq : A*Real.sinh (dist u z)=B*Real.sinh (dist v z)) (w : ℍ) :
    max (A*Real.sinh (dist u z)) (B*Real.sinh (dist v z))≤
      max (A*Real.sinh (dist u w)) (B*Real.sinh (dist v w)) := by
  rw [←heq,max_self]
  by_cases h : dist u z≤dist u w
  · exact (mul_le_mul_of_nonneg_left (Real.sinh_le_sinh.mpr h) hA).trans (le_max_left _ _)
  · have hs:=dist_triangle_eq_of_mem_closedHSegment hz
    have hw:=dist_triangle u w v
    have hd : dist v z≤dist v w := by
      rw [dist_comm z v] at hs
      rw [dist_comm w v] at hw
      linarith [lt_of_not_ge h]
    rw [heq]
    exact (mul_le_mul_of_nonneg_left (Real.sinh_le_sinh.mpr hd) hB).trans (le_max_right _ _)

/-- Every genuine pair with the proved elliptic radial displacement formulas has a true
balanced minimizer on the actual joining segment, for the actual infimum over the entire plane. -/
theorem radial_displacementM_attained (g h : ℍ ≃ᵢ ℍ) (u v : ℍ) (A B : ℝ)
    (hA : 0<A) (hB : 0<B)
    (hg : ∀ z : ℍ,hSinhDisplacement g z=A*Real.sinh (dist u z))
    (hh : ∀ z : ℍ,hSinhDisplacement h z=B*Real.sinh (dist v z)) :
    ∃ z∈closedHSegment u v,
      hSinhDisplacement g z=hSinhDisplacement h z ∧
      displacementM g h=hSinhDisplacement g z := by
  obtain ⟨z,hz,heq⟩:=exists_balanced_radial_point u v A B hA hB
  refine ⟨z,hz,?_,?_⟩
  · rw [hg,hh]
    exact heq
  · apply le_antisymm
    · rw [hg]
      have he:=displacementM_le g h z
      rwa [hg,hh,←heq,max_self] at he
    · apply (displacementM_lower_bound g h _).mpr
      intro w
      rw [hg,hg,hh]
      have he:=balanced_radial_point_minimizes u v z hz A B hA.le hB.le heq w
      rwa [←heq,max_self] at he

/-- Actual elliptic maps construct the weights and centers; no radial model is assumed. -/
theorem elliptic_pair_displacementM_attained (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : Mobius.MobiusElliptic (realSLMobius A)) (hB : Mobius.MobiusElliptic (realSLMobius B)) :
    let u:=hEllipticCenter A ((realSLMobius_elliptic_iff A hA.1).mp hA)
    let v:=hEllipticCenter B ((realSLMobius_elliptic_iff B hB.1).mp hB)
    ∃ z∈closedHSegment u v,
      hSinhDisplacement (hSLIsometry A) z=hSinhDisplacement (hSLIsometry B) z ∧
      displacementM (hSLIsometry A) (hSLIsometry B)=hSinhDisplacement (hSLIsometry A) z := by
  obtain ⟨a,b,hu,hb,hdispA,_⟩:=elliptic_half_displacement A hA
  obtain ⟨c,d,hv,hd,hdispB,_⟩:=elliptic_half_displacement B hB
  apply radial_displacementM_attained _ _ _ _ |b| |d| (abs_pos.mpr hb) (abs_pos.mpr hd)
  · intro z
    change Real.sinh (dist z (A•z)/2)=_
    rw [hdispA,mul_comm,dist_comm]
  · intro z
    change Real.sinh (dist z (B•z)/2)=_
    rw [hdispB,mul_comm,dist_comm]

/-- Exact scalar identity at the genuine balanced displacement point. -/
theorem balanced_sinh_square_identity (A B s t : ℝ)
    (he : A*Real.sinh s=B*Real.sinh t) :
    (A*Real.sinh s)^2*(A^2+B^2+2*A*B*Real.cosh (s+t))=
      A^2*B^2*(Real.sinh (s+t))^2 := by
  have hnum : A*B*Real.sinh (s+t)=
      (A*Real.sinh s)*(B*Real.cosh t+A*Real.cosh s) := by
    rw [Real.sinh_add]
    calc
      A*B*(Real.sinh s*Real.cosh t+Real.cosh s*Real.sinh t)=
        B*Real.cosh t*(A*Real.sinh s)+A*Real.cosh s*(B*Real.sinh t) := by ring
      _=B*Real.cosh t*(A*Real.sinh s)+A*Real.cosh s*(A*Real.sinh s) := by rw [←he]
      _=_ := by ring
  have hraw : (B*Real.cosh t+A*Real.cosh s)^2-
      (A^2+B^2+2*A*B*Real.cosh (s+t))-(A*Real.sinh s-B*Real.sinh t)^2=
      B^2*(Real.cosh t^2-Real.sinh t^2-1)+A^2*(Real.cosh s^2-Real.sinh s^2-1) := by
    rw [Real.cosh_add]
    ring
  rw [he,sub_self,zero_pow (by norm_num : 2≠0),sub_zero,
    Real.cosh_sq_sub_sinh_sq,Real.cosh_sq_sub_sinh_sq,sub_self,mul_zero,mul_zero,zero_add] at hraw
  have hden : (B*Real.cosh t+A*Real.cosh s)^2=A^2+B^2+2*A*B*Real.cosh (s+t) :=
    sub_eq_zero.mp hraw
  calc
    _=(A*Real.sinh s)^2*(B*Real.cosh t+A*Real.cosh s)^2 := by rw [hden]
    _=((A*Real.sinh s)*(B*Real.cosh t+A*Real.cosh s))^2 := (mul_pow _ _ _).symm
    _=(A*B*Real.sinh (s+t))^2 := by rw [←hnum]
    _=_ := by ring

/-- The exact maximum-displacement infimum for every proved positive elliptic radial pair. -/
theorem radial_displacementM_square (g h : ℍ ≃ᵢ ℍ) (u v : ℍ) (A B : ℝ)
    (hA : 0<A) (hB : 0<B)
    (hg : ∀ z : ℍ,hSinhDisplacement g z=A*Real.sinh (dist u z))
    (hh : ∀ z : ℍ,hSinhDisplacement h z=B*Real.sinh (dist v z)) :
    (displacementM g h)^2=
      A^2*B^2*(Real.sinh (dist u v))^2/(A^2+B^2+2*A*B*Real.cosh (dist u v)) := by
  obtain ⟨z,hz,hbal,hM⟩:=radial_displacementM_attained g h u v A B hA hB hg hh
  rw [hg,hh] at hbal
  rw [hg] at hM
  have hsum:=dist_triangle_eq_of_mem_closedHSegment hz
  rw [dist_comm z v] at hsum
  have hden : 0<A^2+B^2+2*A*B*Real.cosh (dist u v) := by positivity
  apply (eq_div_iff hden.ne').mpr
  rw [hM]
  have he:=balanced_sinh_square_identity A B (dist u z) (dist v z) hbal
  rwa [hsum] at he

/-- The weight is the sine of half the actual, uniquely determined rotation angle. -/
theorem elliptic_actual_angle_radial (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : Mobius.MobiusElliptic (realSLMobius A)) (z : ℍ) :
    hSinhDisplacement (hSLIsometry A) z=
      Real.sin (hEllipticRotationAngle A hA/2)*
        Real.sinh (dist (hEllipticCenter A ((realSLMobius_elliptic_iff A hA.1).mp hA)) z) := by
  obtain ⟨a,b,hu,_hb,hdisp,q,hq⟩:=elliptic_half_displacement A hA
  have hp:=hEllipticRotationAngle_spec A hA
  have hspos : 0<Real.sin (hEllipticRotationAngle A hA/2) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hEllipticRotationAngle_pos A hA])
      (by linarith [hp.1.2])
  have ht:=hSL_trace_conjugation A q
  rw [hq] at ht
  have ht2 : (Matrix.trace A.val)^2=4*a^2 := by
    rw [←ht]
    simp only [hRotationSL,Matrix.trace_fin_two,Matrix.of_apply,Matrix.cons_val_zero,
      Matrix.cons_val_one]
    ring
  have hb : Real.sin (hEllipticRotationAngle A hA/2)=|b| := by
    nlinarith [hp.2.2.2,Real.sin_sq_add_cos_sq (hEllipticRotationAngle A hA/2),
      abs_nonneg b,sq_abs b]
  change Real.sinh (dist z (A•z)/2)=_
  rw [hdisp,hb,mul_comm,dist_comm]

/-- The exact infimum formula holds for every actual elliptic pair and its actual angles. -/
theorem elliptic_pair_displacementM_square (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : Mobius.MobiusElliptic (realSLMobius A)) (hB : Mobius.MobiusElliptic (realSLMobius B)) :
    let u:=hEllipticCenter A ((realSLMobius_elliptic_iff A hA.1).mp hA)
    let v:=hEllipticCenter B ((realSLMobius_elliptic_iff B hB.1).mp hB)
    let s:=Real.sin (hEllipticRotationAngle A hA/2)
    let t:=Real.sin (hEllipticRotationAngle B hB/2)
    (displacementM (hSLIsometry A) (hSLIsometry B))^2=
      (s*t)^2*(Real.cosh (dist u v)^2-1)/(s^2+t^2+2*s*t*Real.cosh (dist u v)) := by
  have hpos (X : Matrix.SpecialLinearGroup (Fin 2) ℝ)
      (hX : Mobius.MobiusElliptic (realSLMobius X)) :
      0<Real.sin (hEllipticRotationAngle X hX/2) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hEllipticRotationAngle_pos X hX])
      (by linarith [(hEllipticRotationAngle_spec X hX).1.2])
  have he:=radial_displacementM_square (hSLIsometry A) (hSLIsometry B) _ _ _ _
    (hpos A hA) (hpos B hB) (elliptic_actual_angle_radial A hA) (elliptic_actual_angle_radial B hB)
  dsimp only
  rw [he,mul_pow,Real.sinh_sq]

/-- The elliptic displacement formula has the actual minimal positive rotation angles explicit. -/
theorem elliptic_pair_order_angle_formula (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : Mobius.MobiusElliptic (realSLMobius A)) (hB : Mobius.MobiusElliptic (realSLMobius B))
    (p q : ℕ) (hθA : hEllipticRotationAngle A hA=2*Real.pi/p)
    (hθB : hEllipticRotationAngle B hB=2*Real.pi/q) :
    let u:=hEllipticCenter A ((realSLMobius_elliptic_iff A hA.1).mp hA)
    let v:=hEllipticCenter B ((realSLMobius_elliptic_iff B hB.1).mp hB)
    let s:=Real.sin (Real.pi/p)
    let t:=Real.sin (Real.pi/q)
    (displacementM (hSLIsometry A) (hSLIsometry B))^2=
      (s*t)^2*(Real.cosh (dist u v)^2-1)/(s^2+t^2+2*s*t*Real.cosh (dist u v)) := by
  have he:=elliptic_pair_displacementM_square A B hA hB
  dsimp only at he ⊢
  rw [hθA,hθB] at he
  convert he using 1; ring_nf

end LowDimensionalTopology.Geometry.Hyperbolic
