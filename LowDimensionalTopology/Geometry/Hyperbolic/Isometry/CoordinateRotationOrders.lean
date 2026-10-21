/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Hyperbolic.Isometry.Displacement.EllipticRotationAngles
public import LowDimensionalTopology.Geometry.Euclidean.Reflection.FiniteRotationSectors
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace LowDimensionalTopology.Geometry.Hyperbolic

/-- A genuine scalar coordinate intertwining also intertwines every actual positive power. -/
theorem coordinate_rotation_power {X : Type*} [PseudoEMetricSpace X]
    (f : X≃ᵢX) (φ : X→ℂ) (u : ℂ) (hφ : ∀z,φ (f z)=u*φ z)
    (m : ℕ) (z : X) : φ ((f^m) z)=u^m*φ z := by
  induction m generalizing z with
  | zero => change φ z=1*φ z;rw [one_mul]
  | succ m ih =>
    change φ ((f^m) (f z))=u^(m+1)*φ z
    rw [ih,hφ,pow_succ,mul_assoc]

/-- Faithful scalar coordinates and a genuine primitive multiplier determine the actual
isometry order, rather than assuming that order from a chosen angle label. -/
theorem orderOf_isometry_of_primitive_coordinate {X : Type*} [PseudoEMetricSpace X]
    (f : X≃ᵢX) (φ : X→ℂ) (hinj : Function.Injective φ)
    (hne : ∃z,φ z≠0) (u : ℂ) (n : ℕ) (hn : 0<n)
    (hu : IsPrimitiveRoot u n) (hφ : ∀z,φ (f z)=u*φ z) : orderOf f=n := by
  have hiff (m : ℕ) : f^m=1 ↔ u^m=1 := by
    constructor
    · intro hm
      obtain ⟨z,hz⟩:=hne
      have h:=coordinate_rotation_power f φ u hφ m z
      rw [hm] at h
      change φ z=u^m*φ z at h
      exact ((mul_right_cancel₀ hz) ((one_mul (φ z)).trans h)).symm
    · intro hm
      apply IsometryEquiv.ext
      intro z
      apply hinj
      change φ ((f^m) z)=φ z
      rw [coordinate_rotation_power f φ u hφ m z,hm,one_mul]
  apply (orderOf_eq_iff hn).mpr
  refine ⟨(hiff n).mpr hu.pow_eq_one,?_⟩
  intro m hmn hm hpow
  have hdiv:=hu.dvd_of_pow_eq_one m ((hiff m).mp hpow)
  exact (not_le_of_gt hmn) (Nat.le_of_dvd hm hdiv)

end LowDimensionalTopology.Geometry.Hyperbolic
