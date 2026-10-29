module

public import LowDimensionalTopology.Geometry.Hyperbolic.Reflection.AnnularPairQuotientReflection
public import LowDimensionalTopology.Geometry.Hyperbolic.Reflection.AnnularPairNonElementary
public import LowDimensionalTopology.Geometry.Fuchsian.Nielsen.NielsenCoreConjugation
public import LowDimensionalTopology.Geometry.Fuchsian.Nielsen.NielsenCoreArea
public import LowDimensionalTopology.Geometry.Fuchsian.TriangleGroup.NativeTriangleProperness

/-! The first original mirror preserves the literal Cayley pullback of the
source-defined Nielsen core. Its accepted quotient involution therefore
preserves that same core's native orbit image. -/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set Topology
open scoped UpperHalfPlane OnePoint

namespace LowDimensionalTopology.Geometry.Hyperbolic
open LowDimensionalTopology.Geometry.DiscreteGroups
open LowDimensionalTopology.Geometry.DiscreteGroups.Action
open LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Mobius
open LowDimensionalTopology.Geometry.Surfaces

/-- The first actual mirror preserves the literal pullback of the same
annular model's original disc Nielsen core along its actual Cayley coordinate. -/
theorem annularPairFirstMirror_preserves_originalNielsenLift
    (E r x : ℝ) (hE : 1 < E) (hr : 0 < r)
    (hin : 1 + r < x) (hout : x + r < E) :
    let P := annularPairReflectionHalfPlaneData E r x hE hr hin hout
    let hNE := annularPairReflectionDiscGroup_nonElementary E r x hE hr hin
    let σ := halfPlaneLineReflectionIsometry
      (annularPairReflectionMirrors E r x (zero_lt_one.trans hE) hr 0)
    σ '' (P.cayleyCoordinate ⁻¹' fuchsianNielsenCore P.cayleyData hNE) =
      P.cayleyCoordinate ⁻¹' fuchsianNielsenCore P.cayleyData hNE := by
  let G := annularPairReflectionGroup E r x (zero_lt_one.trans hE) hr
  let hG := annularPairReflectionGroup_le_conformal E r x (zero_lt_one.trans hE) hr
  let F := nativeConformalSubgroupMobiusHom G hG
  let P := annularPairReflectionHalfPlaneData E r x hE hr hin hout
  let D := P.asFuchsianDisc
  have hNEΔ := annularPairReflectionDiscGroup_nonElementary E r x hE hr hin
  have hNE₀ : IsNonElementary F.range := by
    intro he
    apply hNEΔ
    exact (Mobius.invariantDisc_finiteOrbit_conjugation F.range cayleyMobius).mpr he
  let b : ℍ → Mobius.ExtendedComplex := extendedHalfPlanePoint
  let N := D.nielsenRegion hNE₀
  let K := b ⁻¹' N
  let σ := halfPlaneLineReflectionIsometry
    (annularPairReflectionMirrors E r x (zero_lt_one.trans hE) hr 0)
  have hb : IsOpenEmbedding b := nielsen_halfPlanePoint_isOpenEmbedding
  have hbRange : range b = openHalfPlaneSet := nielsen_halfPlanePoint_range
  obtain ⟨hNsub, hNne, hNo, hNc, hNi⟩ := D.nielsenRegion_properties hNE₀
  have hbK : b '' K = N := by
    change b '' (b ⁻¹' N) = N
    rw [image_preimage_eq_inter_range, hbRange]
    exact inter_eq_left.mpr hNsub
  have hKn : K.Nonempty := by
    have hh : (b '' K).Nonempty := by
      rw [hbK]
      exact hNne
    exact hh.of_image
  have hKo : IsOpen K := hNo.preimage hb.continuous
  have hKc : HConvex K := by
    apply (D.hyperbolicallyConvex_halfPlane rfl K).mp
    change D.HyperbolicallyConvex (b '' K)
    rw [hbK]
    exact hNc
  have hact (g : G) (z : ℍ) : (F g).val (b z) = b (g • z) :=
    nativeConformalSubgroupMobiusHom_action G hG g z
  have hKi : ∀ g : G, ∀ z ∈ K, g • z ∈ K := by
    intro g z hz
    have hn := hNi (F.rangeRestrict g) (b z) hz
    change (F g).val (b z) ∈ N at hn
    rw [hact] at hn
    exact hn
  have hmin (T : Set ℍ) (hn : T.Nonempty) (ho : IsOpen T) (hc : HConvex T)
      (hi : ∀ g : G, ∀ z ∈ T, g • z ∈ T) : K ⊆ T := by
    have hSsub : b '' T ⊆ D.carrier := by
      change b '' T ⊆ openHalfPlaneSet
      rw [← hbRange]
      exact image_subset_range b T
    have hSi : ∀ g : F.range, ∀ p ∈ b '' T, g • p ∈ b '' T := by
      intro g p hp
      obtain ⟨z, hz, rfl⟩ := hp
      obtain ⟨f, hfg⟩ := g.property
      refine ⟨f • z, hi f z hz, ?_⟩
      change b (f • z) = g.val.val (b z)
      rw [← hfg]
      exact (hact f z).symm
    have hNS : N ⊆ b '' T :=
      (D.nielsenRegion_isLeast_nonempty_open_invariant_convex hNE₀).2
        ⟨hSsub, hn.image b, hb.isOpenMap T ho,
          (D.hyperbolicallyConvex_halfPlane rfl T).mpr hc, hSi⟩
    intro z hz
    obtain ⟨w, hw, hew⟩ := hNS hz
    exact hb.injective hew ▸ hw
  have hnorm : σ ∈ Subgroup.normalizer (G : Set (ℍ ≃ᵢ ℍ)) :=
    annularPairReflectionGroup_firstMirror_normalizes E r x (zero_lt_one.trans hE) hr
  have hTi : ∀ g : G, ∀ z ∈ σ '' K, g • z ∈ σ '' K := by
    intro g z hz
    obtain ⟨w, hw, rfl⟩ := hz
    let f : G := ⟨σ⁻¹ * g.val * σ,
      (Subgroup.mem_normalizer_iff''.mp hnorm g.val).mp g.property⟩
    refine ⟨f • w, hKi f w hw, ?_⟩
    change σ • ((σ⁻¹ * g.val * σ) • w) = g.val • (σ • w)
    simp only [mul_smul, smul_inv_smul]
  have hKT : K ⊆ σ '' K :=
    hmin (σ '' K) (hKn.image σ) (σ.toHomeomorph.isOpenMap K hKo)
      (hKc.isometry_image σ.isometry) hTi
  have hσinvol : Function.Involutive (σ : ℍ → ℍ) :=
    (annularPairReflectionMirrors E r x (zero_lt_one.trans hE) hr 0).reflection_involutive
  have hσK : σ '' K = K := by
    refine subset_antisymm ?_ hKT
    have hh := image_mono hKT (f := (σ : ℍ → ℍ))
    rw [image_image] at hh
    have he : (fun z : ℍ => σ (σ z)) = id := funext hσinvol
    simpa only [he, image_id] using hh
  have hdisc : P.cayleyData.asFuchsianDisc = D.nielsenConjugate cayleyMobius := by
    apply fuchsianDisc_eq_of_carrier_eq
    exact cayleyMobius_image_openHalfPlane.symm
  have hNdisc : cayleyMobius.val '' N =
      P.cayleyData.asFuchsianDisc.nielsenRegion hNEΔ := by
    rw [hdisc]
    exact nielsenRegion_conjugation_image D hNE₀ cayleyMobius
  have hpoint (z : ℍ) : (P.cayleyCoordinate z).val = cayleyMobius.val (b z) := by
    have he := discFiniteHomeomorph_symm_coe (halfPlaneToDisc z)
    change _ = cayleyMobius.val (((z : ℂ) : Mobius.ExtendedComplex))
    rw [cayleyMobius_apply, extendedCayley_halfPlane]
    exact he
  have hKeq : P.cayleyCoordinate ⁻¹' fuchsianNielsenCore P.cayleyData hNEΔ = K := by
    ext z
    change (P.cayleyCoordinate z).val ∈
      P.cayleyData.asFuchsianDisc.nielsenRegion hNEΔ ↔ b z ∈ N
    rw [hpoint, ← hNdisc]
    exact cayleyMobius.val.injective.mem_set_image
  change σ '' (P.cayleyCoordinate ⁻¹' fuchsianNielsenCore P.cayleyData hNEΔ) =
    P.cayleyCoordinate ⁻¹' fuchsianNielsenCore P.cayleyData hNEΔ
  rw [hKeq]
  exact hσK

/-- The accepted original native quotient involution preserves the orbit
image of the literal Cayley pullback of the same source-defined Nielsen core. -/
theorem annularPairQuotientReflection_preserves_originalCoreImage
    (E r x : ℝ) (hE : 1 < E) (hr : 0 < r)
    (hin : 1 + r < x) (hout : x + r < E) :
    let P := annularPairReflectionHalfPlaneData E r x hE hr hin hout
    let hNE := annularPairReflectionDiscGroup_nonElementary E r x hE hr hin
    let G := annularPairReflectionGroup E r x (zero_lt_one.trans hE) hr
    let K := P.cayleyCoordinate ⁻¹' fuchsianNielsenCore P.cayleyData hNE
    annularPairQuotientReflection E r x (zero_lt_one.trans hE) hr ''
        (orbitProjection G ℍ '' K) = orbitProjection G ℍ '' K := by
  let P := annularPairReflectionHalfPlaneData E r x hE hr hin hout
  have hNE := annularPairReflectionDiscGroup_nonElementary E r x hE hr hin
  let G := annularPairReflectionGroup E r x (zero_lt_one.trans hE) hr
  let K := P.cayleyCoordinate ⁻¹' fuchsianNielsenCore P.cayleyData hNE
  let σ := halfPlaneLineReflectionIsometry
    (annularPairReflectionMirrors E r x (zero_lt_one.trans hE) hr 0)
  let Q := orbitQuotient G ℍ
  let J : Q ≃ₜ Q := annularPairQuotientReflection E r x (zero_lt_one.trans hE) hr
  let π : ℍ → Q := orbitProjection G ℍ
  have hK : σ '' K = K :=
    annularPairFirstMirror_preserves_originalNielsenLift E r x hE hr hin hout
  have hsquare : (J : Q → Q) ∘ π = π ∘ (σ : ℍ → ℍ) := by
    funext z
    exact annularPairQuotientReflection_projection E r x (zero_lt_one.trans hE) hr z
  change J '' (π '' K) = π '' K
  calc
    J '' (π '' K) = π '' (σ '' K) := by
      rw [image_image, image_image]
      exact congrArg (fun f : ℍ → Q => f '' K) hsquare
    _ = π '' K := congrArg (fun T => π '' T) hK

end LowDimensionalTopology.Geometry.Hyperbolic
