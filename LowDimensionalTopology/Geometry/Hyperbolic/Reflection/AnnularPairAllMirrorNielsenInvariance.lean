module

public import LowDimensionalTopology.Geometry.Hyperbolic.Reflection.AnnularPairNielsenCoreReflection
public import LowDimensionalTopology.Geometry.Hyperbolic.Reflection.AnnularPairCayleyOrbitTransport
public import LowDimensionalTopology.Geometry.Fuchsian.Nielsen.FiniteNielsenCoreGeometry
public import Mathlib.Tactic.FinCases

/-! All three original annular mirrors preserve the literal Cayley pullback
of the source-defined Nielsen core. Its openness, nonemptiness, and genuine
hyperbolic convexity are derived from that same original core. -/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set
open scoped UpperHalfPlane

namespace LowDimensionalTopology.Geometry.Hyperbolic
open LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Mobius
open LowDimensionalTopology.Geometry.Surfaces

/-- The literal original Nielsen lift is open, nonempty, and genuinely
hyperbolically convex; these properties are not extra annular hypotheses. -/
theorem annularPairOriginalNielsenLift_properties
    (E r x : ℝ) (hE : 1 < E) (hr : 0 < r)
    (hin : 1 + r < x) (hout : x + r < E) :
    let P := annularPairReflectionHalfPlaneData E r x hE hr hin hout
    let hNE := annularPairReflectionDiscGroup_nonElementary E r x hE hr hin
    let K := P.cayleyCoordinate ⁻¹' fuchsianNielsenCore P.cayleyData hNE
    IsOpen K ∧ K.Nonempty ∧ HConvex K := by
  let P := annularPairReflectionHalfPlaneData E r x hE hr hin hout
  have hNE := annularPairReflectionDiscGroup_nonElementary E r x hE hr hin
  let N := fuchsianNielsenCore P.cayleyData hNE
  let K := P.cayleyCoordinate ⁻¹' N
  change IsOpen K ∧ K.Nonempty ∧ HConvex K
  have hnN : N.Nonempty := by
    obtain ⟨z, hz⟩ := (P.cayleyData.asFuchsianDisc.nielsenRegion_properties hNE).2.1
    exact ⟨⟨z, (P.cayleyData.asFuchsianDisc.nielsenRegion_properties hNE).1 hz⟩, hz⟩
  have hfinite : halfPlaneToDisc '' K = P.cayleyData.finiteCoordinate '' N := by
    apply subset_antisymm
    · rintro _ ⟨z, hz, rfl⟩
      exact ⟨P.cayleyCoordinate z, hz, P.cayleyCoordinate_finite z⟩
    · rintro _ ⟨z, hz, rfl⟩
      refine ⟨P.cayleyCoordinate.symm z, ?_, ?_⟩
      · change P.cayleyCoordinate (P.cayleyCoordinate.symm z) ∈ N
        simpa only [P.cayleyCoordinate.apply_symm_apply] using hz
      · simpa only [P.cayleyCoordinate.apply_symm_apply] using
          (P.cayleyCoordinate_finite (P.cayleyCoordinate.symm z)).symm
  refine ⟨(fuchsianNielsenCore_isOpen P.cayleyData hNE).preimage
      P.cayleyCoordinate.continuous,
    P.cayleyCoordinate.surjective.nonempty_preimage.mpr hnN, ?_⟩
  apply (hConvex_iff_cayley_discHConvex K).mpr
  rw [hfinite]
  exact fuchsianNielsenCore_convex P.cayleyData hNE

/-- The genuine original native group preserves the same literal Nielsen
lift, via its faithful Cayley action on the actual disc Nielsen core. -/
theorem annularPairNativeGroup_preserves_originalNielsenLift
    (E r x : ℝ) (hE : 1 < E) (hr : 0 < r)
    (hin : 1 + r < x) (hout : x + r < E)
    (g : annularPairReflectionGroup E r x (zero_lt_one.trans hE) hr) (z : ℍ) :
    let P := annularPairReflectionHalfPlaneData E r x hE hr hin hout
    let hNE := annularPairReflectionDiscGroup_nonElementary E r x hE hr hin
    z ∈ P.cayleyCoordinate ⁻¹' fuchsianNielsenCore P.cayleyData hNE →
      g • z ∈ P.cayleyCoordinate ⁻¹' fuchsianNielsenCore P.cayleyData hNE := by
  let P := annularPairReflectionHalfPlaneData E r x hE hr hin hout
  have hNE := annularPairReflectionDiscGroup_nonElementary E r x hE hr hin
  let : MulAction (annularPairReflectionDiscGroup E r x (zero_lt_one.trans hE) hr)
      P.cayleyData.domain.carrier := mobiusDomainAction P.cayleyData.domain
  change P.cayleyCoordinate z ∈ fuchsianNielsenCore P.cayleyData hNE →
    P.cayleyCoordinate (g • z) ∈ fuchsianNielsenCore P.cayleyData hNE
  intro hz
  have hact := annularPairCayleyGroupEquiv_action E r x hE hr hin hout g z
  rw [hact]
  exact fuchsianNielsenCore_invariant P.cayleyData hNE
    (annularPairCayleyGroupEquiv E r x (zero_lt_one.trans hE) hr g)
    (P.cayleyCoordinate z) hz

/-- Every original mirror preserves the literal original Nielsen lift.
The mirror indexing remains S0, S1, S2, with no cuff-order permutation. -/
theorem annularPairMirrors_preserve_originalNielsenLift
    (E r x : ℝ) (hE : 1 < E) (hr : 0 < r)
    (hin : 1 + r < x) (hout : x + r < E) (i : Fin 3) :
    let P := annularPairReflectionHalfPlaneData E r x hE hr hin hout
    let hNE := annularPairReflectionDiscGroup_nonElementary E r x hE hr hin
    let K := P.cayleyCoordinate ⁻¹' fuchsianNielsenCore P.cayleyData hNE
    (annularPairReflectionMirrors E r x (zero_lt_one.trans hE) hr i).reflection '' K = K := by
  let P := annularPairReflectionHalfPlaneData E r x hE hr hin hout
  have hNE := annularPairReflectionDiscGroup_nonElementary E r x hE hr hin
  let K := P.cayleyCoordinate ⁻¹' fuchsianNielsenCore P.cayleyData hNE
  let G := annularPairReflectionGroup E r x (zero_lt_one.trans hE) hr
  let S := annularPairReflectionMirrors E r x (zero_lt_one.trans hE) hr
  let σ : Fin 3 → (ℍ ≃ᵢ ℍ) := fun j => halfPlaneLineReflectionIsometry (S j)
  have hsq (j : Fin 3) : σ j * σ j = 1 := by
    simpa only [pow_two] using nativeLineReflection_square (S j)
  have hgen0 : σ 0 * σ 1 ∈ G := by
    change σ 0 * σ 1 ∈ Subgroup.closure ({σ 0 * σ 1, σ 2 * σ 0} : Set (ℍ ≃ᵢ ℍ))
    exact Subgroup.subset_closure (by simp)
  have hgen1 : σ 2 * σ 0 ∈ G := by
    change σ 2 * σ 0 ∈ Subgroup.closure ({σ 0 * σ 1, σ 2 * σ 0} : Set (ℍ ≃ᵢ ℍ))
    exact Subgroup.subset_closure (by simp)
  have hG (g : G) (z : ℍ) (hz : z ∈ K) : g • z ∈ K :=
    annularPairNativeGroup_preserves_originalNielsenLift E r x hE hr hin hout g z hz
  have hfirst : σ 0 '' K = K :=
    annularPairFirstMirror_preserves_originalNielsenLift E r x hE hr hin hout
  have hzero (z : ℍ) (hz : z ∈ K) : σ 0 • z ∈ K := by
    rw [← hfirst]
    exact ⟨z, hz, rfl⟩
  have hmaps (j : Fin 3) : ∀ z ∈ K, σ j • z ∈ K := by
    fin_cases j
    · exact hzero
    · intro z hz
      change σ 1 • z ∈ K
      have hdeck := hG ⟨σ 0 * σ 1, hgen0⟩ z hz
      change (σ 0 * σ 1) • z ∈ K at hdeck
      have hh := hzero ((σ 0 * σ 1) • z) hdeck
      simpa only [← mul_smul, ← mul_assoc, hsq 0, one_mul] using hh
    · intro z hz
      change σ 2 • z ∈ K
      have hh := hG ⟨σ 2 * σ 0, hgen1⟩ (σ 0 • z) (hzero z hz)
      change (σ 2 * σ 0) • (σ 0 • z) ∈ K at hh
      simpa only [← mul_smul, mul_assoc, hsq 0, mul_one] using hh
  change (fun z : ℍ => σ i • z) '' K = K
  apply subset_antisymm
  · rintro _ ⟨z, hz, rfl⟩
    exact hmaps i z hz
  · intro z hz
    refine ⟨σ i • z, hmaps i z hz, ?_⟩
    change σ i • (σ i • z) = z
    rw [← mul_smul, hsq i, one_smul]

end LowDimensionalTopology.Geometry.Hyperbolic
