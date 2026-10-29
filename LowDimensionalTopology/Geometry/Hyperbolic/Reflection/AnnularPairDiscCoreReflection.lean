module

public import LowDimensionalTopology.Geometry.Hyperbolic.Reflection.AnnularPairQuotientAnticonformal
public import LowDimensionalTopology.Geometry.Hyperbolic.Reflection.AnnularPairCoreReflectionOrder
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.GroupTheory.OrderOfElement

/-! The same concrete disc-quotient involution preserves the existing
three-boundary Nielsen core. Its actual restriction is conjugate to the
proved native core restriction and therefore has exact order two. -/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set
open scoped UpperHalfPlane

namespace LowDimensionalTopology.Geometry.Hyperbolic
open LowDimensionalTopology.Geometry.DiscreteGroups.Action
open LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Surfaces

/-- The same concrete disc-quotient reflection preserves the existing open
Nielsen core in the unchanged original Cayley quotient. -/
theorem annularPairDiscQuotientReflection_preserves_originalCore
    (E r x : ℝ) (hE : 1 < E) (hr : 0 < r)
    (hin : 1 + r < x) (hout : x + r < E) :
    let P := annularPairReflectionHalfPlaneData E r x hE hr hin hout
    let hNE := annularPairReflectionDiscGroup_nonElementary E r x hE hr hin
    annularPairDiscQuotientReflection E r x hE hr hin hout ''
        threeBoundaryOpenCore P.cayleyData hNE = threeBoundaryOpenCore P.cayleyData hNE := by
  let P := annularPairReflectionHalfPlaneData E r x hE hr hin hout
  have hNE := annularPairReflectionDiscGroup_nonElementary E r x hE hr hin
  let G := annularPairReflectionGroup E r x (zero_lt_one.trans hE) hr
  let K := P.cayleyCoordinate ⁻¹' fuchsianNielsenCore P.cayleyData hNE
  let C := orbitProjection G ℍ '' K
  let Cd := threeBoundaryOpenCore P.cayleyData hNE
  let Φ := annularPairCayleyOrbitHomeomorph E r x hE hr hin hout
  let Jn := annularPairQuotientReflection E r x (zero_lt_one.trans hE) hr
  let Jd := annularPairDiscQuotientReflection E r x hE hr hin hout
  have hΦ : Φ '' C = Cd :=
    annularPairCayleyOrbitHomeomorph_coreImage E r x hE hr hin hout
  have hJn : Jn '' C = C :=
    annularPairQuotientReflection_preserves_originalCoreImage E r x hE hr hin hout
  have hsquare : (fun q : orbitQuotient G ℍ => Jd (Φ q)) = fun q => Φ (Jn q) := by
    funext q
    change Φ (Jn (Φ.symm (Φ q))) = Φ (Jn q)
    rw [Φ.symm_apply_apply]
  change Jd '' Cd = Cd
  calc
    Jd '' Cd = Jd '' (Φ '' C) := congrArg (fun T => Jd '' T) hΦ.symm
    _ = Φ '' (Jn '' C) := by
      calc
        Jd '' (Φ '' C) = (fun q => Jd (Φ q)) '' C := image_image Jd Φ C
        _ = (fun q => Φ (Jn q)) '' C :=
          congrArg (fun f : orbitQuotient G ℍ → MobiusDomainQuotient P.cayleyData.domain =>
            f '' C) hsquare
        _ = Φ '' (Jn '' C) := (image_image Φ Jn C).symm
    _ = Cd := by rw [hJn, hΦ]

/-- The actual Cayley orbit homeomorphism restricted to the literal native
core image and the existing threeBoundaryOpenCore of the same original disc model. -/
def annularPairCayleyCoreHomeomorph
    (E r x : ℝ) (hE : 1 < E) (hr : 0 < r)
    (hin : 1 + r < x) (hout : x + r < E) :
    let P := annularPairReflectionHalfPlaneData E r x hE hr hin hout
    let hNE := annularPairReflectionDiscGroup_nonElementary E r x hE hr hin
    let G := annularPairReflectionGroup E r x (zero_lt_one.trans hE) hr
    let K := P.cayleyCoordinate ⁻¹' fuchsianNielsenCore P.cayleyData hNE
    (orbitProjection G ℍ '' K) ≃ₜ threeBoundaryOpenCore P.cayleyData hNE := by
  let P := annularPairReflectionHalfPlaneData E r x hE hr hin hout
  have hNE := annularPairReflectionDiscGroup_nonElementary E r x hE hr hin
  let G := annularPairReflectionGroup E r x (zero_lt_one.trans hE) hr
  let K := P.cayleyCoordinate ⁻¹' fuchsianNielsenCore P.cayleyData hNE
  let C := orbitProjection G ℍ '' K
  let Φ := annularPairCayleyOrbitHomeomorph E r x hE hr hin hout
  exact (Φ.image C).trans (Homeomorph.setCongr
    (annularPairCayleyOrbitHomeomorph_coreImage E r x hE hr hin hout))

/-- The same disc-quotient involution restricted to the existing actual
three-boundary Nielsen core, using the proved preservation of that very set. -/
def annularPairDiscCoreReflection
    (E r x : ℝ) (hE : 1 < E) (hr : 0 < r)
    (hin : 1 + r < x) (hout : x + r < E) :
    let P := annularPairReflectionHalfPlaneData E r x hE hr hin hout
    let hNE := annularPairReflectionDiscGroup_nonElementary E r x hE hr hin
    threeBoundaryOpenCore P.cayleyData hNE ≃ₜ threeBoundaryOpenCore P.cayleyData hNE := by
  let P := annularPairReflectionHalfPlaneData E r x hE hr hin hout
  have hNE := annularPairReflectionDiscGroup_nonElementary E r x hE hr hin
  let Cd := threeBoundaryOpenCore P.cayleyData hNE
  let Jd := annularPairDiscQuotientReflection E r x hE hr hin hout
  exact (Jd.image Cd).trans (Homeomorph.setCongr
    (annularPairDiscQuotientReflection_preserves_originalCore E r x hE hr hin hout))

/-- The literal restriction of the same disc involution is conjugate to
the existing native core reflection through the actual restricted Cayley map. -/
theorem annularPairDiscCoreReflection_eq_conjugate
    (E r x : ℝ) (hE : 1 < E) (hr : 0 < r)
    (hin : 1 + r < x) (hout : x + r < E) :
    annularPairDiscCoreReflection E r x hE hr hin hout =
      (annularPairCayleyCoreHomeomorph E r x hE hr hin hout).symm.trans
        ((annularPairCoreReflection E r x hE hr hin hout).trans
          (annularPairCayleyCoreHomeomorph E r x hE hr hin hout)) := by
  apply Homeomorph.ext
  intro q
  apply Subtype.ext
  rfl

/-- The same concrete reflection on the existing original disc core has
exact order two, as does its proved native-core conjugate. -/
theorem annularPairDiscCoreReflection_orderOf
    (E r x : ℝ) (hE : 1 < E) (hr : 0 < r)
    (hin : 1 + r < x) (hout : x + r < E) :
    orderOf (annularPairDiscCoreReflection E r x hE hr hin hout) = 2 := by
  let P := annularPairReflectionHalfPlaneData E r x hE hr hin hout
  have hNE := annularPairReflectionDiscGroup_nonElementary E r x hE hr hin
  let G := annularPairReflectionGroup E r x (zero_lt_one.trans hE) hr
  let K := P.cayleyCoordinate ⁻¹' fuchsianNielsenCore P.cayleyData hNE
  let C := orbitProjection G ℍ '' K
  let Cd := threeBoundaryOpenCore P.cayleyData hNE
  let H : C ≃ₜ Cd := annularPairCayleyCoreHomeomorph E r x hE hr hin hout
  let Rn : C ≃ₜ C := annularPairCoreReflection E r x hE hr hin hout
  let Rd : Cd ≃ₜ Cd := annularPairDiscCoreReflection E r x hE hr hin hout
  let Jd := annularPairDiscQuotientReflection E r x hE hr hin hout
  have hconj : Rd = H.symm.trans (Rn.trans H) :=
    annularPairDiscCoreReflection_eq_conjugate E r x hE hr hin hout
  change orderOf Rd = 2
  apply orderOf_eq_prime
  · apply Homeomorph.ext
    intro q
    apply Subtype.ext
    change Jd (Jd q.val) = q.val
    exact annularPairDiscQuotientReflection_involutive E r x hE hr hin hout q.val
  · intro h
    have hn : Rn = 1 := by
      apply Homeomorph.ext
      intro q
      apply H.injective
      have hp := congrArg (fun f : Cd ≃ₜ Cd => f (H q)) h
      change Rd (H q) = H q at hp
      rw [hconj] at hp
      change H (Rn (H.symm (H q))) = H q at hp
      rw [H.symm_apply_apply] at hp
      exact hp
    have ho₂ : orderOf Rn = 2 := annularPairCoreReflection_orderOf E r x hE hr hin hout
    have ho₁ : orderOf Rn = 1 := by rw [hn, orderOf_one]
    exact (by decide : (1 : ℕ) ≠ 2) (ho₁.symm.trans ho₂)

end LowDimensionalTopology.Geometry.Hyperbolic
