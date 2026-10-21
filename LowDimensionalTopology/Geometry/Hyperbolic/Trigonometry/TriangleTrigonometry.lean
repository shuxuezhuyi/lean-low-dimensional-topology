/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Hyperbolic.Triangle.TriangleAltitude

/-! # Actual finite triangle data and the hyperbolic Pythagorean identity -/

@[expose] public section
open Set InnerProductGeometry
open scoped UpperHalfPlane Complex.UnitDisc
namespace LowDimensionalTopology.Geometry.Hyperbolic
noncomputable section

def HTriangle.lengthA (T : HTriangle) : ℝ := dist T.b T.c
def HTriangle.lengthB (T : HTriangle) : ℝ := dist T.c T.a
def HTriangle.lengthC (T : HTriangle) : ℝ := dist T.a T.b
def HTriangle.alpha (T : HTriangle) : ℝ := hInteriorAngleMeasure T.rayAB T.rayAC
def HTriangle.beta (T : HTriangle) : ℝ := hInteriorAngleMeasure T.rayBA T.rayBC
def HTriangle.gamma (T : HTriangle) : ℝ := hInteriorAngleMeasure T.rayCA T.rayCB

theorem HTriangle.lengths_pos (T : HTriangle) :
    0 < T.lengthA ∧ 0 < T.lengthB ∧ 0 < T.lengthC :=
  ⟨dist_pos.mpr T.b_ne_c,dist_pos.mpr T.c_ne_a,dist_pos.mpr T.a_ne_b⟩

theorem HTriangle.angles_mem_Ioo (T : HTriangle) :
    T.alpha ∈ Ioo (0 : ℝ) Real.pi ∧ T.beta ∈ Ioo (0 : ℝ) Real.pi ∧
      T.gamma ∈ Ioo (0 : ℝ) Real.pi :=
  ⟨⟨hInteriorAngleMeasure_pos _ _ T.proper_angleA,
      hInteriorAngleMeasure_lt_pi _ _ T.proper_angleA⟩,
    ⟨hInteriorAngleMeasure_pos _ _ T.proper_angleB,
      hInteriorAngleMeasure_lt_pi _ _ T.proper_angleB⟩,
    ⟨hInteriorAngleMeasure_pos _ _ T.proper_angleC,
      hInteriorAngleMeasure_lt_pi _ _ T.proper_angleC⟩⟩

theorem HTriangle.angle_measurements (T : HTriangle) :
    T.angleA.interiorMeasure = some T.alpha ∧
      T.angleB.interiorMeasure = some T.beta ∧
        T.angleC.interiorMeasure = some T.gamma :=
  ⟨hAngleInteriorMeasurePair_proper _ _ T.proper_angleA,
    hAngleInteriorMeasurePair_proper _ _ T.proper_angleB,
    hAngleInteriorMeasurePair_proper _ _ T.proper_angleC⟩

/-- A right measured angle is equivalent to actual tangent orthogonality of its supports. -/
theorem hInteriorAngleMeasure_eq_pi_div_two_iff {z : ℍ} (R S : HRayAt z) :
    hInteriorAngleMeasure R S = Real.pi / 2 ↔ R.supportLine.OrthogonalAt S.supportLine z := by
  rw [hInteriorAngleMeasure,← inner_eq_zero_iff_angle_eq_pi_div_two]
  change inner ℝ (R.tangentSign • R.supportLine.tangentAt z)
    (S.tangentSign • S.supportLine.tangentAt z) = 0 ↔ _
  rw [real_inner_smul_left,real_inner_smul_right]
  simp only [mul_eq_zero,R.tangentSign_ne_zero,S.tangentSign_ne_zero,false_or]
  exact ⟨fun h => ⟨R.start_mem_support,S.start_mem_support,h⟩,fun h => h.2.2⟩

theorem HTriangle.gamma_eq_pi_div_two_iff (T : HTriangle) :
    T.gamma = Real.pi / 2 ↔ T.sideLineB.OrthogonalAt T.sideLineA T.c := by
  rw [HTriangle.gamma,hInteriorAngleMeasure_eq_pi_div_two_iff,T.support_CB_eq]
  rfl

/-- For an actual triangle and its actual interior angle. -/
theorem HTriangle.cosh_hypotenuse_eq_cosh_mul_cosh (T : HTriangle) (hγ : T.gamma = Real.pi / 2) :
    Real.cosh T.lengthC = Real.cosh T.lengthA * Real.cosh T.lengthB := by
  have h := T.sideLineB.orthogonal_cosh_dist T.sideLineA T.c T.b T.a
    ((T.gamma_eq_pi_div_two_iff).mp hγ)
    T.rayBC.start_mem_support
    (T.rayCA.subset_support T.a_mem_rayCA)
  change Real.cosh (dist T.a T.b) =
    Real.cosh (dist T.b T.c) * Real.cosh (dist T.c T.a)
  simpa only [dist_comm] using h

def DiscTriangle.lengthA (T : DiscTriangle) : ℝ := discPathDist T.b T.c
def DiscTriangle.lengthB (T : DiscTriangle) : ℝ := discPathDist T.c T.a
def DiscTriangle.lengthC (T : DiscTriangle) : ℝ := discPathDist T.a T.b
def DiscTriangle.alpha (T : DiscTriangle) : ℝ := discInteriorAngleMeasure T.rayAB T.rayAC
def DiscTriangle.beta (T : DiscTriangle) : ℝ := discInteriorAngleMeasure T.rayBA T.rayBC
def DiscTriangle.gamma (T : DiscTriangle) : ℝ := discInteriorAngleMeasure T.rayCA T.rayCB

theorem DiscTriangle.lengths_eq_halfPlane (T : DiscTriangle) :
    T.lengthA = T.toHalfPlane.lengthA ∧ T.lengthB = T.toHalfPlane.lengthB ∧
      T.lengthC = T.toHalfPlane.lengthC :=
  ⟨discPathDist_eq_halfPlane _ _,discPathDist_eq_halfPlane _ _,discPathDist_eq_halfPlane _ _⟩

theorem DiscTriangle.angles_eq_halfPlane (T : DiscTriangle) :
    T.alpha = T.toHalfPlane.alpha ∧ T.beta = T.toHalfPlane.beta ∧
      T.gamma = T.toHalfPlane.gamma := by
  dsimp only [DiscTriangle.alpha,DiscTriangle.beta,DiscTriangle.gamma,
    HTriangle.alpha,HTriangle.beta,HTriangle.gamma]
  simp only [discInteriorAngleMeasure_eq_halfPlane,DiscTriangle.rayAB,DiscTriangle.rayAC,
    DiscTriangle.rayBA,DiscTriangle.rayBC,DiscTriangle.rayCA,DiscTriangle.rayCB,
    discRayThrough_toHalfPlane,HTriangle.rayAB,HTriangle.rayAC,HTriangle.rayBA,
    HTriangle.rayBC,HTriangle.rayCA,HTriangle.rayCB]
  exact ⟨rfl,rfl,rfl⟩

theorem DiscTriangle.lengths_pos (T : DiscTriangle) :
    0 < T.lengthA ∧ 0 < T.lengthB ∧ 0 < T.lengthC := by
  rw [T.lengths_eq_halfPlane.1,T.lengths_eq_halfPlane.2.1,T.lengths_eq_halfPlane.2.2]
  exact T.toHalfPlane.lengths_pos

theorem DiscTriangle.angles_mem_Ioo (T : DiscTriangle) :
    T.alpha ∈ Ioo (0 : ℝ) Real.pi ∧ T.beta ∈ Ioo (0 : ℝ) Real.pi ∧
      T.gamma ∈ Ioo (0 : ℝ) Real.pi := by
  rw [T.angles_eq_halfPlane.1,T.angles_eq_halfPlane.2.1,T.angles_eq_halfPlane.2.2]
  exact T.toHalfPlane.angles_mem_Ioo

theorem DiscTriangle.angle_measurements (T : DiscTriangle) :
    T.angleA.interiorMeasure = some T.alpha ∧
      T.angleB.interiorMeasure = some T.beta ∧
        T.angleC.interiorMeasure = some T.gamma :=
  ⟨discAngleInteriorMeasurePair_proper _ _ T.proper_angleA,
    discAngleInteriorMeasurePair_proper _ _ T.proper_angleB,
    discAngleInteriorMeasurePair_proper _ _ T.proper_angleC⟩

/-- The same identity in the native disc, using its actual density path distance and angles. -/
theorem DiscTriangle.cosh_hypotenuse_eq_cosh_mul_cosh (T : DiscTriangle) (hγ : T.gamma = Real.pi / 2) :
    Real.cosh T.lengthC = Real.cosh T.lengthA * Real.cosh T.lengthB := by
  rw [T.lengths_eq_halfPlane.1,T.lengths_eq_halfPlane.2.1,T.lengths_eq_halfPlane.2.2]
  apply T.toHalfPlane.cosh_hypotenuse_eq_cosh_mul_cosh
  rwa [← T.angles_eq_halfPlane.2.2]

end
end LowDimensionalTopology.Geometry.Hyperbolic
