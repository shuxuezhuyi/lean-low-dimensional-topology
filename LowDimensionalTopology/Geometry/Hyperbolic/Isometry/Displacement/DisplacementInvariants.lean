/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Hyperbolic.Isometry.Displacement.DisplacementGeometry
public import Mathlib.Analysis.SpecialFunctions.Arsinh
@[expose] public section
noncomputable section
open Set
open scoped UpperHalfPlane
namespace LowDimensionalTopology.Geometry.Hyperbolic
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- The infimum of the larger actual half-displacement sinh. -/
def displacementM (g h : ℍ ≃ᵢ ℍ) : ℝ :=
  ⨅ z : ℍ, max (hSinhDisplacement g z) (hSinhDisplacement h z)

/-- The infimum of the product of actual half-displacement sinhs. -/
def displacementP (g h : ℍ ≃ᵢ ℍ) : ℝ :=
  ⨅ z : ℍ, hSinhDisplacement g z*hSinhDisplacement h z

theorem displacementM_nonneg (g h : ℍ ≃ᵢ ℍ) : 0≤displacementM g h :=
  le_ciInf fun z => le_max_of_le_left (hSinhDisplacement_nonneg g z)

theorem displacementP_nonneg (g h : ℍ ≃ᵢ ℍ) : 0≤displacementP g h :=
  le_ciInf fun z => mul_nonneg (hSinhDisplacement_nonneg g z) (hSinhDisplacement_nonneg h z)

theorem displacementM_le (g h : ℍ ≃ᵢ ℍ) (z : ℍ) :
    displacementM g h≤max (hSinhDisplacement g z) (hSinhDisplacement h z) := by
  apply ciInf_le _ z
  exact ⟨0,by rintro _ ⟨w,rfl⟩;exact le_max_of_le_left (hSinhDisplacement_nonneg g w)⟩

theorem displacementP_le (g h : ℍ ≃ᵢ ℍ) (z : ℍ) :
    displacementP g h≤hSinhDisplacement g z*hSinhDisplacement h z := by
  apply ciInf_le _ z
  refine ⟨0,?_⟩
  rintro _ ⟨w,rfl⟩
  exact mul_nonneg (hSinhDisplacement_nonneg g w) (hSinhDisplacement_nonneg h w)

theorem displacementM_lower_bound (g h : ℍ ≃ᵢ ℍ) (m : ℝ) :
    m≤displacementM g h ↔ ∀ z : ℍ, m≤max (hSinhDisplacement g z) (hSinhDisplacement h z) :=
  ⟨fun hm z => hm.trans (displacementM_le g h z),fun hm => le_ciInf hm⟩

theorem displacementP_lower_bound (g h : ℍ ≃ᵢ ℍ) (p : ℝ) :
    p≤displacementP g h ↔ ∀ z : ℍ, p≤hSinhDisplacement g z*hSinhDisplacement h z :=
  ⟨fun hp z => hp.trans (displacementP_le g h z),fun hp => le_ciInf hp⟩

/-- The two actual displacement invariants satisfy the source square inequality. -/
theorem displacementP_le_M_sq (g h : ℍ ≃ᵢ ℍ) : displacementP g h≤(displacementM g h)^2 := by
  have hs : Real.sqrt (displacementP g h)≤displacementM g h := by
    apply (displacementM_lower_bound g h _).mpr
    intro z
    apply Real.sqrt_le_iff.mpr
    have hg := hSinhDisplacement_nonneg g z
    have hh := hSinhDisplacement_nonneg h z
    have hm : 0≤max (hSinhDisplacement g z) (hSinhDisplacement h z) := le_max_of_le_left hg
    refine ⟨hm,(displacementP_le g h z).trans ?_⟩
    nlinarith [mul_le_mul (le_max_left (hSinhDisplacement g z) (hSinhDisplacement h z))
      (le_max_right (hSinhDisplacement g z) (hSinhDisplacement h z)) hh hm]
  exact (Real.sqrt_le_iff.mp hs).2

theorem displacementM_comm (g h : ℍ ≃ᵢ ℍ) : displacementM g h=displacementM h g := by
  simp only [displacementM,max_comm]

theorem displacementP_comm (g h : ℍ ≃ᵢ ℍ) : displacementP g h=displacementP h g := by
  simp only [displacementP,mul_comm]

/-- A genuine fixed point forces the actual product infimum to vanish. -/
theorem displacementP_eq_zero_of_fixed (g h : ℍ ≃ᵢ ℍ) (z : ℍ) (hz : g z=z) :
    displacementP g h=0 := by
  apply le_antisymm _ (displacementP_nonneg g h)
  have hp := displacementP_le g h z
  simpa only [hSinhDisplacement,hDisplacement,hz,dist_self,zero_div,Real.sinh_zero,zero_mul] using hp

theorem displacementP_eq_zero_of_fixed_right (g h : ℍ ≃ᵢ ℍ) (z : ℍ) (hz : h z=z) :
    displacementP g h=0 := by
  rw [displacementP_comm]
  exact displacementP_eq_zero_of_fixed h g z hz

/-- Every actual elliptic real-matrix isometry has product invariant zero. -/
theorem displacementP_eq_zero_of_elliptic_left
    (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hA : Mobius.MobiusElliptic (realSLMobius A))
    (h : ℍ ≃ᵢ ℍ) : displacementP (hSLIsometry A) h=0 := by
  let ht := (realSLMobius_elliptic_iff A hA.1).mp hA
  exact displacementP_eq_zero_of_fixed (hSLIsometry A) h (hEllipticCenter A ht)
    ((hSL_elliptic_fixed_iff A ht _).mpr rfl)

theorem displacementP_eq_zero_of_elliptic_right
    (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hA : Mobius.MobiusElliptic (realSLMobius A))
    (g : ℍ ≃ᵢ ℍ) : displacementP g (hSLIsometry A)=0 := by
  rw [displacementP_comm]
  exact displacementP_eq_zero_of_elliptic_left A hA g

theorem displacementM_inverse_left (g h : ℍ ≃ᵢ ℍ) :
    displacementM g.symm h=displacementM g h := by
  simp only [displacementM,hSinhDisplacement_inverse]

theorem displacementP_inverse_left (g h : ℍ ≃ᵢ ℍ) :
    displacementP g.symm h=displacementP g h := by
  simp only [displacementP,hSinhDisplacement_inverse]

/-- Simultaneous actual isometric conjugacy leaves the maximum invariant unchanged. -/
theorem displacementM_conjugation (g h q : ℍ ≃ᵢ ℍ) :
    displacementM ((q.symm.trans g).trans q) ((q.symm.trans h).trans q)=
      displacementM g h := by
  apply le_antisymm
  · apply (displacementM_lower_bound g h _).mpr
    intro z
    have he := displacementM_le ((q.symm.trans g).trans q) ((q.symm.trans h).trans q) (q z)
    simpa only [hSinhDisplacement_conjugation] using he
  · apply (displacementM_lower_bound _ _ _).mpr
    intro z
    have he := displacementM_le g h (q.symm z)
    have hg := hSinhDisplacement_conjugation g q (q.symm z)
    have hh := hSinhDisplacement_conjugation h q (q.symm z)
    rw [q.apply_symm_apply] at hg hh
    rwa [hg,hh]

theorem displacementP_conjugation (g h q : ℍ ≃ᵢ ℍ) :
    displacementP ((q.symm.trans g).trans q) ((q.symm.trans h).trans q)=
      displacementP g h := by
  apply le_antisymm
  · apply (displacementP_lower_bound g h _).mpr
    intro z
    have he := displacementP_le ((q.symm.trans g).trans q) ((q.symm.trans h).trans q) (q z)
    simpa only [hSinhDisplacement_conjugation] using he
  · apply (displacementP_lower_bound _ _ _).mpr
    intro z
    have he := displacementP_le g h (q.symm z)
    have hg := hSinhDisplacement_conjugation g q (q.symm z)
    have hh := hSinhDisplacement_conjugation h q (q.symm z)
    rw [q.apply_symm_apply] at hg hh
    rwa [hg,hh]

/-- The invariant bound is exactly the original pointwise distance-displacement alternative. -/
theorem displacementM_lower_bound_distance (g h : ℍ ≃ᵢ ℍ) (m : ℝ) :
    m≤displacementM g h ↔ ∀ z : ℍ,
      2*Real.arsinh m≤dist z (g z) ∨ 2*Real.arsinh m≤dist z (h z) := by
  rw [displacementM_lower_bound]
  apply forall_congr'
  intro z
  rw [le_max_iff]
  have ht (k : ℍ ≃ᵢ ℍ) : m≤hSinhDisplacement k z ↔ 2*Real.arsinh m≤dist z (k z) := by
    rw [←Real.arsinh_le_arsinh]
    change Real.arsinh m≤Real.arsinh (Real.sinh (dist z (k z)/2)) ↔ _
    rw [Real.arsinh_sinh]
    constructor <;> intro he <;> linarith
  rw [ht g,ht h]

end LowDimensionalTopology.Geometry.Hyperbolic
