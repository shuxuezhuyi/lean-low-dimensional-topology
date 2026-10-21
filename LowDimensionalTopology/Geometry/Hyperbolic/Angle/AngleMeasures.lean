/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Hyperbolic.Angle.RayTangents
public import LowDimensionalTopology.Geometry.Hyperbolic.Angle.DiscAngles
public import Mathlib.Analysis.Complex.Angle

/-!
# Actual forward-tangent angle measurements
-/

@[expose] public section
open Set InnerProductGeometry
open scoped UpperHalfPlane OnePoint Topology Complex.UnitDisc
namespace LowDimensionalTopology.Geometry.Hyperbolic
noncomputable section

/-- The usual Euclidean angle between the actual forward tangent vectors of the rays. -/
def hInteriorAngleMeasure {z : ℍ} (R S : HRayAt z) : ℝ := angle R.tangentVector S.tangentVector

def hExteriorAngleMeasure {z : ℍ} (R S : HRayAt z) : ℝ := 2 * Real.pi - hInteriorAngleMeasure R S

theorem hInteriorAngleMeasure_comm {z : ℍ} (R S : HRayAt z) :
    hInteriorAngleMeasure R S = hInteriorAngleMeasure S R := angle_comm _ _

theorem hInteriorAngleMeasure_self {z : ℍ} (R : HRayAt z) : hInteriorAngleMeasure R R = 0 :=
  angle_self R.tangentVector_ne_zero

theorem hInteriorAngleMeasure_pos {z : ℍ} (R S : HRayAt z)
    (hne : R.supportLine ≠ S.supportLine) : 0 < hInteriorAngleMeasure R S := by
  apply lt_of_le_of_ne (angle_nonneg _ _)
  intro he
  obtain ⟨_,r,_,hr⟩ := angle_eq_zero_iff.mp he.symm
  exact hne (R.support_eq_of_tangent_smul S r hr)

theorem hInteriorAngleMeasure_lt_pi {z : ℍ} (R S : HRayAt z)
    (hne : R.supportLine ≠ S.supportLine) : hInteriorAngleMeasure R S < Real.pi := by
  apply lt_of_le_of_ne (angle_le_pi _ _)
  intro he
  obtain ⟨_,r,_,hr⟩ := angle_eq_pi_iff.mp he
  exact hne (R.support_eq_of_tangent_smul S r hr)

theorem hInteriorAngleMeasure_mem_Ico {z : ℍ} (R S : HRayAt z)
    (hne : R.supportLine ≠ S.supportLine) : hInteriorAngleMeasure R S ∈ Ico (0 : ℝ) Real.pi :=
  ⟨angle_nonneg _ _,hInteriorAngleMeasure_lt_pi R S hne⟩

theorem hExteriorAngleMeasure_mem_Ioc {z : ℍ} (R S : HRayAt z)
    (hne : R.supportLine ≠ S.supportLine) : hExteriorAngleMeasure R S ∈ Ioc Real.pi (2 * Real.pi) := by
  have hθ := hInteriorAngleMeasure_mem_Ico R S hne
  constructor <;> dsimp only [hExteriorAngleMeasure] <;> linarith [hθ.1,hθ.2]

/-- Opposite rays have no canonical angle region or canonical measurement. -/
def hAngleInteriorMeasurePair {z : ℍ} (R S : HRayAt z) : Option ℝ := by
  classical
  exact if R = S then some 0 else if R.supportLine = S.supportLine then none
    else some (hInteriorAngleMeasure R S)

def hAngleExteriorMeasurePair {z : ℍ} (R S : HRayAt z) : Option ℝ :=
  (hAngleInteriorMeasurePair R S).map (fun θ => 2 * Real.pi - θ)

theorem hAngleInteriorMeasurePair_comm {z : ℍ} (R S : HRayAt z) :
    hAngleInteriorMeasurePair R S = hAngleInteriorMeasurePair S R := by
  classical
  by_cases hRS : R = S
  · subst S
    rfl
  · simp only [hAngleInteriorMeasurePair,ite_eq_right hRS,ite_eq_right (Ne.symm hRS)]
    by_cases hL : R.supportLine = S.supportLine
    · simp only [hL,ite_true]
    · simp only [ite_eq_right hL,ite_eq_right (Ne.symm hL),hInteriorAngleMeasure_comm R S]

theorem hAngleExteriorMeasurePair_comm {z : ℍ} (R S : HRayAt z) :
    hAngleExteriorMeasurePair R S = hAngleExteriorMeasurePair S R := by
  rw [hAngleExteriorMeasurePair,hAngleExteriorMeasurePair,hAngleInteriorMeasurePair_comm]

def HAngle.interiorMeasure {z : ℍ} (A : HAngle z) : Option ℝ :=
  Sym2.lift ⟨hAngleInteriorMeasurePair,hAngleInteriorMeasurePair_comm⟩ A

def HAngle.exteriorMeasure {z : ℍ} (A : HAngle z) : Option ℝ :=
  Sym2.lift ⟨hAngleExteriorMeasurePair,hAngleExteriorMeasurePair_comm⟩ A

theorem hAngleInteriorMeasurePair_proper {z : ℍ} (R S : HRayAt z)
    (hne : R.supportLine ≠ S.supportLine) :
    hAngleInteriorMeasurePair R S = some (hInteriorAngleMeasure R S) := by
  have hRS : R ≠ S := fun he => hne (congrArg HRayAt.supportLine he)
  simp only [hAngleInteriorMeasurePair,ite_eq_right hRS,ite_eq_right hne]

theorem hAngleExteriorMeasurePair_proper {z : ℍ} (R S : HRayAt z)
    (hne : R.supportLine ≠ S.supportLine) :
    hAngleExteriorMeasurePair R S = some (hExteriorAngleMeasure R S) := by
  rw [hAngleExteriorMeasurePair,hAngleInteriorMeasurePair_proper R S hne,Option.map_some]
  rfl

theorem hAngleInteriorMeasurePair_self {z : ℍ} (R : HRayAt z) : hAngleInteriorMeasurePair R R = some 0 := by
  simp [hAngleInteriorMeasurePair]

theorem hAngleExteriorMeasurePair_self {z : ℍ} (R : HRayAt z) :
    hAngleExteriorMeasurePair R R = some (2 * Real.pi) := by
  rw [hAngleExteriorMeasurePair,hAngleInteriorMeasurePair_self,Option.map_some,sub_zero]

theorem hAngleInteriorMeasurePair_some_mem_Ico {z : ℍ} (R S : HRayAt z) {θ : ℝ}
    (hθ : hAngleInteriorMeasurePair R S = some θ) : θ ∈ Ico (0 : ℝ) Real.pi := by
  classical
  by_cases hRS : R = S
  · subst S
    rw [hAngleInteriorMeasurePair_self,Option.some.injEq] at hθ
    rw [← hθ]
    exact ⟨le_rfl,Real.pi_pos⟩
  · by_cases hL : R.supportLine = S.supportLine
    · simp only [hAngleInteriorMeasurePair,ite_eq_right hRS,ite_eq_left hL] at hθ
      cases hθ
    · rw [hAngleInteriorMeasurePair_proper R S hL,Option.some.injEq] at hθ
      rw [← hθ]
      exact hInteriorAngleMeasure_mem_Ico R S hL

theorem hAngleExteriorMeasurePair_some_mem_Ioc {z : ℍ} (R S : HRayAt z) {θ : ℝ}
    (hθ : hAngleExteriorMeasurePair R S = some θ) : θ ∈ Ioc Real.pi (2 * Real.pi) := by
  cases hI : hAngleInteriorMeasurePair R S with
  | none => simp only [hAngleExteriorMeasurePair,hI,Option.map_none] at hθ; cases hθ
  | some η =>
    rw [hAngleExteriorMeasurePair,hI,Option.map_some,Option.some.injEq] at hθ
    have hη := hAngleInteriorMeasurePair_some_mem_Ico R S hI
    constructor <;> linarith [hη.1,hη.2]

theorem HAngle.interiorMeasure_mem_Ico {z : ℍ} (A : HAngle z) {θ : ℝ}
    (hθ : A.interiorMeasure = some θ) : θ ∈ Ico (0 : ℝ) Real.pi := by
  induction A using Sym2.inductionOn with
  | hf R S => exact hAngleInteriorMeasurePair_some_mem_Ico R S hθ

theorem HAngle.exteriorMeasure_mem_Ioc {z : ℍ} (A : HAngle z) {θ : ℝ}
    (hθ : A.exteriorMeasure = some θ) : θ ∈ Ioc Real.pi (2 * Real.pi) := by
  induction A using Sym2.inductionOn with
  | hf R S => exact hAngleExteriorMeasurePair_some_mem_Ioc R S hθ

/-- The same ordinary Euclidean forward-germ criterion in the actual native disc. -/
def IsForwardDiscRayTangent (R : Set 𝔻) (z : 𝔻) (v : ℂ) : Prop :=
  v ≠ 0 ∧ ∃ c : ℝ → ℂ, HasDerivAt c v 0 ∧ c 0 = (z : ℂ) ∧
    ∃ ε : ℝ, 0 < ε ∧ ∀ t ∈ Ioo (0 : ℝ) ε,
      ∃ w : 𝔻, w ∈ R \ {z} ∧ (w : ℂ) = c t

def cayleyTangentFactor (z : ℍ) : ℂ := (2 * Complex.I) / ((z : ℂ) + Complex.I) ^ 2

theorem cayleyTangentFactor_ne_zero (z : ℍ) : cayleyTangentFactor z ≠ 0 :=
  div_ne_zero (mul_ne_zero (by norm_num) Complex.I_ne_zero) (pow_ne_zero 2 (cayley_denom_ne_zero z))

/-- The actual Cayley differential carries a genuine forward ray tangent to a
forward tangent of the actual native disc ray point set. -/
def DiscRayAt.tangentVector {z : 𝔻} (R : DiscRayAt z) : ℂ :=
  cayleyTangentFactor (discToHalfPlane z) * R.toHalfPlane.tangentVector

theorem DiscRayAt.tangentVector_ne_zero {z : 𝔻} (R : DiscRayAt z) : R.tangentVector ≠ 0 :=
  mul_ne_zero (cayleyTangentFactor_ne_zero _) R.toHalfPlane.tangentVector_ne_zero

theorem DiscRayAt.tangentVector_isForward {z : 𝔻} (R : DiscRayAt z) :
    IsForwardDiscRayTangent R.val z R.tangentVector := by
  obtain ⟨_,c,hc,hc0,ε,hε,hgerm⟩ := R.toHalfPlane.tangentVector_isForward
  have hf := hasDerivAt_cayleyFormula (discToHalfPlane z)
  rw [← hc0] at hf
  have hcomp : HasDerivAt (cayleyFormula ∘ c) R.tangentVector 0 := by
    have he := hf.scomp 0 hc
    rw [hc0] at he
    simpa only [DiscRayAt.tangentVector,cayleyTangentFactor,smul_eq_mul,mul_comm] using he
  refine ⟨R.tangentVector_ne_zero,cayleyFormula ∘ c,hcomp,?_,ε,hε,?_⟩
  · change cayleyFormula (c 0) = (z : ℂ)
    rw [hc0]
    exact congrArg (fun w : 𝔻 => (w : ℂ)) (halfPlaneToDisc_discToHalfPlane z)
  · intro t ht
    obtain ⟨w,hw,hwc⟩ := hgerm t ht
    refine ⟨halfPlaneToDisc w,⟨?_,?_⟩,?_⟩
    · rw [R.carrier_eq_cayley]
      exact mem_image_of_mem halfPlaneToDisc hw.1
    · intro he
      have hz' := congrArg discToHalfPlane he
      rw [discToHalfPlane_halfPlaneToDisc] at hz'
      exact hw.2 hz'
    · change cayleyFormula (w : ℂ) = cayleyFormula (c t)
      rw [hwc]

def discInteriorAngleMeasure {z : 𝔻} (R S : DiscRayAt z) : ℝ := angle R.tangentVector S.tangentVector

def discExteriorAngleMeasure {z : 𝔻} (R S : DiscRayAt z) : ℝ := 2 * Real.pi - discInteriorAngleMeasure R S

/-- This is genuine Euclidean conformality of the actual differential, not a
new measure defined by pulling back a number. -/
theorem discInteriorAngleMeasure_eq_halfPlane {z : 𝔻} (R S : DiscRayAt z) :
    discInteriorAngleMeasure R S = hInteriorAngleMeasure R.toHalfPlane S.toHalfPlane :=
  Complex.angle_mul_left (cayleyTangentFactor_ne_zero _) _ _

theorem discInteriorAngleMeasure_mem_Ico {z : 𝔻} (R S : DiscRayAt z)
    (hne : R.supportLine ≠ S.supportLine) : discInteriorAngleMeasure R S ∈ Ico (0 : ℝ) Real.pi := by
  rw [discInteriorAngleMeasure_eq_halfPlane]
  exact hInteriorAngleMeasure_mem_Ico R.toHalfPlane S.toHalfPlane ((R.different_supports_iff S).mp hne)

theorem discExteriorAngleMeasure_mem_Ioc {z : 𝔻} (R S : DiscRayAt z)
    (hne : R.supportLine ≠ S.supportLine) : discExteriorAngleMeasure R S ∈ Ioc Real.pi (2 * Real.pi) := by
  change 2 * Real.pi - discInteriorAngleMeasure R S ∈ _
  rw [discInteriorAngleMeasure_eq_halfPlane]
  exact hExteriorAngleMeasure_mem_Ioc R.toHalfPlane S.toHalfPlane ((R.different_supports_iff S).mp hne)

def discAngleInteriorMeasurePair {z : 𝔻} (R S : DiscRayAt z) : Option ℝ :=
  hAngleInteriorMeasurePair R.toHalfPlane S.toHalfPlane

def discAngleExteriorMeasurePair {z : 𝔻} (R S : DiscRayAt z) : Option ℝ :=
  hAngleExteriorMeasurePair R.toHalfPlane S.toHalfPlane

theorem discAngleInteriorMeasurePair_comm {z : 𝔻} (R S : DiscRayAt z) :
    discAngleInteriorMeasurePair R S = discAngleInteriorMeasurePair S R :=
  hAngleInteriorMeasurePair_comm _ _

theorem discAngleExteriorMeasurePair_comm {z : 𝔻} (R S : DiscRayAt z) :
    discAngleExteriorMeasurePair R S = discAngleExteriorMeasurePair S R :=
  hAngleExteriorMeasurePair_comm _ _

def DiscAngle.interiorMeasure {z : 𝔻} (A : DiscAngle z) : Option ℝ :=
  Sym2.lift ⟨discAngleInteriorMeasurePair,discAngleInteriorMeasurePair_comm⟩ A

def DiscAngle.exteriorMeasure {z : 𝔻} (A : DiscAngle z) : Option ℝ :=
  Sym2.lift ⟨discAngleExteriorMeasurePair,discAngleExteriorMeasurePair_comm⟩ A

theorem discAngleInteriorMeasurePair_proper {z : 𝔻} (R S : DiscRayAt z)
    (hne : R.supportLine ≠ S.supportLine) :
    discAngleInteriorMeasurePair R S = some (discInteriorAngleMeasure R S) := by
  rw [discAngleInteriorMeasurePair,hAngleInteriorMeasurePair_proper R.toHalfPlane S.toHalfPlane
    ((R.different_supports_iff S).mp hne),discInteriorAngleMeasure_eq_halfPlane]

theorem discAngleExteriorMeasurePair_proper {z : 𝔻} (R S : DiscRayAt z)
    (hne : R.supportLine ≠ S.supportLine) :
    discAngleExteriorMeasurePair R S = some (discExteriorAngleMeasure R S) := by
  rw [discAngleExteriorMeasurePair,hAngleExteriorMeasurePair_proper R.toHalfPlane S.toHalfPlane
    ((R.different_supports_iff S).mp hne)]
  change some (2 * Real.pi - hInteriorAngleMeasure R.toHalfPlane S.toHalfPlane) =
    some (2 * Real.pi - discInteriorAngleMeasure R S)
  rw [discInteriorAngleMeasure_eq_halfPlane]

theorem DiscAngle.interiorMeasure_mem_Ico {z : 𝔻} (A : DiscAngle z) {θ : ℝ}
    (hθ : A.interiorMeasure = some θ) : θ ∈ Ico (0 : ℝ) Real.pi := by
  induction A using Sym2.inductionOn with
  | hf R S => exact hAngleInteriorMeasurePair_some_mem_Ico R.toHalfPlane S.toHalfPlane hθ

theorem DiscAngle.exteriorMeasure_mem_Ioc {z : 𝔻} (A : DiscAngle z) {θ : ℝ}
    (hθ : A.exteriorMeasure = some θ) : θ ∈ Ioc Real.pi (2 * Real.pi) := by
  induction A using Sym2.inductionOn with
  | hf R S => exact hAngleExteriorMeasurePair_some_mem_Ioc R.toHalfPlane S.toHalfPlane hθ

/-- Measurements are defined exactly for the same canonical source angles as their regions. -/
theorem hAngleInteriorMeasurePair_defined {z : ℍ} (R S : HRayAt z) :
    (hAngleInteriorMeasurePair R S).isSome = (hAngleInteriorPair R S).isSome := by
  classical
  simp only [hAngleInteriorMeasurePair,hAngleInteriorPair]
  split_ifs <;> rfl

theorem HAngle.interiorMeasure_defined {z : ℍ} (A : HAngle z) :
    A.interiorMeasure.isSome = A.interior.isSome := by
  induction A using Sym2.inductionOn with
  | hf R S => exact hAngleInteriorMeasurePair_defined R S

theorem discAngleInteriorMeasurePair_defined {z : 𝔻} (R S : DiscRayAt z) :
    (discAngleInteriorMeasurePair R S).isSome = (discAngleInteriorPair R S).isSome := by
  rw [discAngleInteriorMeasurePair,discAngleInteriorPair,Option.isSome_map]
  exact hAngleInteriorMeasurePair_defined R.toHalfPlane S.toHalfPlane

theorem DiscAngle.interiorMeasure_defined {z : 𝔻} (A : DiscAngle z) :
    A.interiorMeasure.isSome = A.interior.isSome := by
  induction A using Sym2.inductionOn with
  | hf R S => exact discAngleInteriorMeasurePair_defined R S

theorem discAngleInteriorMeasurePair_self {z : 𝔻} (R : DiscRayAt z) :
    discAngleInteriorMeasurePair R R = some 0 := hAngleInteriorMeasurePair_self _

theorem discAngleExteriorMeasurePair_self {z : 𝔻} (R : DiscRayAt z) :
    discAngleExteriorMeasurePair R R = some (2 * Real.pi) := hAngleExteriorMeasurePair_self _

theorem hAngleInteriorMeasurePair_opposite {z : ℍ} (R S : HRayAt z)
    (hL : R.supportLine = S.supportLine) (hRS : R ≠ S) : hAngleInteriorMeasurePair R S = none := by
  simp only [hAngleInteriorMeasurePair,ite_eq_right hRS,ite_eq_left hL]

theorem hAngleExteriorMeasurePair_opposite {z : ℍ} (R S : HRayAt z)
    (hL : R.supportLine = S.supportLine) (hRS : R ≠ S) : hAngleExteriorMeasurePair R S = none := by
  rw [hAngleExteriorMeasurePair,hAngleInteriorMeasurePair_opposite R S hL hRS,Option.map_none]

theorem discAngleInteriorMeasurePair_opposite {z : 𝔻} (R S : DiscRayAt z)
    (hL : R.supportLine = S.supportLine) (hRS : R ≠ S) : discAngleInteriorMeasurePair R S = none :=
  hAngleInteriorMeasurePair_opposite _ _ ((R.support_eq_iff S).mp hL)
    ((discRayHalfPlaneEquiv z).injective.ne hRS)

theorem discAngleExteriorMeasurePair_opposite {z : 𝔻} (R S : DiscRayAt z)
    (hL : R.supportLine = S.supportLine) (hRS : R ≠ S) : discAngleExteriorMeasurePair R S = none :=
  hAngleExteriorMeasurePair_opposite _ _ ((R.support_eq_iff S).mp hL)
    ((discRayHalfPlaneEquiv z).injective.ne hRS)

end
end LowDimensionalTopology.Geometry.Hyperbolic
