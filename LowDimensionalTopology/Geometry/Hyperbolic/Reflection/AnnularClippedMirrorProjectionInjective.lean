module

public import LowDimensionalTopology.Geometry.Hyperbolic.Reflection.AnnularPairCayleyOrbitTransport
public import LowDimensionalTopology.Geometry.Hyperbolic.Reflection.AnnularPairAllMirrorNielsenInvariance
public import LowDimensionalTopology.Geometry.Hyperbolic.Reflection.AnnularPairQuotientReflection
public import LowDimensionalTopology.Geometry.Hyperbolic.Reflection.AnnularPairFreeGroup
public import LowDimensionalTopology.Geometry.Hyperbolic.Geodesic.NativeSegmentEndpoints
public import Mathlib.Topology.Covering.Basic
public import Mathlib.Algebra.Group.Torsion

/-!
# Injectivity on an actual finite annular mirror clip

The genuine orbit covering makes lifts of the quotient reflection unique.
An orbit identification on one original mirror therefore preserves that
mirror and its actual finite Nielsen clip. The endpoint permutation and the
original pair-product group's torsion-freeness exclude every nontrivial
identification on the closed clip.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set
open scoped UpperHalfPlane

namespace LowDimensionalTopology.Geometry.Hyperbolic
open LowDimensionalTopology.Geometry.DiscreteGroups.Action
open LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Surfaces

/-- The original native annular orbit projection is an actual covering map,
through its unchanged Cayley quotient and its absence of elliptic elements. -/
theorem annularPairOrbitProjection_isCoveringMap
    (E r x : ℝ) (hE : 1 < E) (hr : 0 < r)
    (hin : 1 + r < x) (hout : x + r < E) :
    IsCoveringMap
      (orbitProjection (annularPairReflectionGroup E r x (zero_lt_one.trans hE) hr) ℍ) := by
  let P := annularPairReflectionHalfPlaneData E r x hE hr hin hout
  let Φ := annularPairCayleyOrbitHomeomorph E r x hE hr hin hout
  have hC : IsCoveringMap
      (mobiusDomainProjection P.cayleyData.domain ∘ P.cayleyCoordinate) :=
    (mobiusDomain_noElliptic_covering P.cayleyData.domain P.cayleyData.discontinuous
      (annularPairReflectionDiscGroup_noElliptic E r x hE hr hin hout)).isCoveringMap.comp_homeomorph
        P.cayleyCoordinate
  have hcover := hC.homeomorph_comp Φ.symm
  have he : Φ.symm ∘ (mobiusDomainProjection P.cayleyData.domain ∘ P.cayleyCoordinate) =
      orbitProjection (annularPairReflectionGroup E r x (zero_lt_one.trans hE) hr) ℍ := by
    funext z
    change Φ.symm (mobiusDomainProjection P.cayleyData.domain (P.cayleyCoordinate z)) = _
    rw [← annularPairCayleyOrbitHomeomorph_projection E r x hE hr hin hout z]
    exact Φ.symm_apply_apply _
  rw [he] at hcover
  exact hcover

variable (E r x : ℝ) (hE : 1 < E) (hr : 0 < r)
  (hin : 1 + r < x) (hout : x + r < E)

local notation "G" => annularPairReflectionGroup E r x (zero_lt_one.trans hE) hr
local notation "S" => annularPairReflectionMirrors E r x (zero_lt_one.trans hE) hr
local notation "J" => annularPairQuotientReflection E r x (zero_lt_one.trans hE) hr
local notation "π" => orbitProjection G ℍ
local notation "P" => annularPairReflectionHalfPlaneData E r x hE hr hin hout
local notation "hNE" => annularPairReflectionDiscGroup_nonElementary E r x hE hr hin
local notation "K" => HalfPlaneFuchsianGroup.cayleyCoordinate P ⁻¹'
  fuchsianNielsenCore (HalfPlaneFuchsianGroup.cayleyData P) hNE

/-- Once the actual native Nielsen slice is the finite segment between two
distinct feet, the original orbit projection is injective on its entire closed
segment, including both actual cuff endpoints. -/
theorem annularPairOrbitProjection_injOn_closed_mirror_clip
    (i : Fin 3) (p q : ℍ) (hpq : p ≠ q)
    (hclip : K ∩ (S i).carrier = openHSegment p q) :
    InjOn π (closedHSegment p q) := by
  classical
  let L := S i
  let σ := halfPlaneLineReflectionIsometry L
  have hclipL : K ∩ L.carrier = openHSegment p q := hclip
  have hσprojection (z : ℍ) : J (π z) = π (σ z) :=
    annularPairQuotientReflection_mirror_projection E r x
      (zero_lt_one.trans hE) hr i z
  have hcover := annularPairOrbitProjection_isCoveringMap E r x hE hr hin hout
  let : IsMulTorsionFree G :=
    annularPairReflectionGroup_isMulTorsionFree E r x hE hr hin hout
  have hdeck (g : G) (z : ℍ) : π (g.val z) = π z := orbitProjection_smul G ℍ g z
  have hfree (g : G) (z : ℍ) (hfix : g • z = z) : g = 1 := by
    have he : (g.val : ℍ → ℍ) = id := hcover.eq_of_comp_eq
      g.val.continuous continuous_id (by
        funext w
        exact hdeck g w) z hfix
    apply Subtype.ext
    apply IsometryEquiv.ext
    intro w
    exact congrFun he w
  have hK (g : G) (z : ℍ) (hz : z ∈ K) : g • z ∈ K :=
    annularPairNativeGroup_preserves_originalNielsenLift E r x hE hr hin hout g z hz
  have hclosedL : IsClosed L.carrier := by
    have he : L.carrier = {z : ℍ | σ z = z} := by
      ext z
      exact (L.reflection_fixed_iff z).symm
    rw [he]
    exact isClosed_eq σ.continuous continuous_id
  have hsegmentL : closedHSegment p q ⊆ L.carrier := by
    rw [← closure_openHSegment hpq]
    apply closure_minimal _ hclosedL
    exact hclipL.symm.subset.trans inter_subset_right
  intro u hu v hv huv
  obtain ⟨g, hg⟩ := (Quotient.exact huv.symm : MulAction.orbitRel G ℍ v u)
  have hgu : g • u = v := hg
  have hguNative : g.val u = v := hgu
  have hσu : σ u = u := (L.reflection_fixed_iff u).mpr (hsegmentL hu)
  have hσv : σ v = v := (L.reflection_fixed_iff v).mpr (hsegmentL hv)
  have hcomm : σ ∘ g.val = g.val ∘ σ := hcover.eq_of_comp_eq
      (σ.continuous.comp g.val.continuous) (g.val.continuous.comp σ.continuous) (by
        funext z
        change π (σ (g.val z)) = π (g.val (σ z))
        calc
          π (σ (g.val z)) = J (π (g.val z)) := (hσprojection (g.val z)).symm
          _ = J (π z) := congrArg J (hdeck g z)
          _ = π (σ z) := hσprojection z
          _ = π (g.val (σ z)) := (hdeck g (σ z)).symm) u (by
        change σ (g.val u) = g.val (σ u)
        simp only [hguNative, hσv, hσu])
  have hcommPoint (z : ℍ) : σ (g.val z) = g.val (σ z) := congrFun hcomm z
  have hLiff (z : ℍ) : g.val z ∈ L.carrier ↔ z ∈ L.carrier := by
    constructor
    · intro hz
      apply (L.reflection_fixed_iff z).mp
      apply g.val.injective
      change g.val (σ z) = g.val z
      rw [← hcommPoint]
      exact (L.reflection_fixed_iff (g.val z)).mpr hz
    · intro hz
      apply (L.reflection_fixed_iff (g.val z)).mp
      change σ (g.val z) = g.val z
      have hzσ : σ z = z := (L.reflection_fixed_iff z).mpr hz
      exact (hcommPoint z).trans (congrArg g.val hzσ)
  have hslice : g.val '' (K ∩ L.carrier) = K ∩ L.carrier := by
    apply subset_antisymm
    · rintro _ ⟨z, hz, rfl⟩
      exact ⟨hK g z hz.1, (hLiff z).mpr hz.2⟩
    · intro z hz
      refine ⟨g.val.symm z, ⟨?_, ?_⟩, g.val.apply_symm_apply z⟩
      · change g⁻¹ • z ∈ K
        exact hK g⁻¹ z hz.1
      · apply (hLiff (g.val.symm z)).mp
        simpa only [g.val.apply_symm_apply] using hz.2
  have hopen : g.val '' openHSegment p q = openHSegment p q := by
    calc
      g.val '' openHSegment p q = g.val '' (K ∩ L.carrier) :=
        congrArg (fun A : Set ℍ => g.val '' A) hclipL.symm
      _ = K ∩ L.carrier := hslice
      _ = openHSegment p q := hclipL
  have hclosed : g.val '' closedHSegment p q = closedHSegment p q := by
    calc
      g.val '' closedHSegment p q = g.val '' closure (openHSegment p q) :=
        congrArg (fun A : Set ℍ => g.val '' A) (closure_openHSegment hpq).symm
      _ = closure (g.val '' openHSegment p q) := g.val.toHomeomorph.image_closure _
      _ = closure (openHSegment p q) := congrArg closure hopen
      _ = closedHSegment p q := closure_openHSegment hpq
  have hpair : ({g.val p, g.val q} : Set ℍ) = {p, q} :=
    native_closedHSegment_image_endpoints g.val p q p q hclosed
  have hgp : g.val p = p ∨ g.val p = q := by
    have hm : g.val p ∈ ({p, q} : Set ℍ) := hpair ▸ (by simp)
    simpa only [mem_insert_iff, mem_singleton_iff] using hm
  have hsquare : (g ^ 2) • p = p := by
    rw [pow_two, mul_smul]
    change g.val (g.val p) = p
    rcases hgp with hgp | hgp
    · rw [hgp, hgp]
    · have hgq : g.val q = p := by
        have hm : p ∈ ({g.val p, g.val q} : Set ℍ) := hpair.symm ▸ (by simp)
        simp only [mem_insert_iff, mem_singleton_iff] at hm
        rcases hm with hm | hm
        · exact False.elim (hpq (hm.trans hgp))
        · exact hm.symm
      rw [hgp, hgq]
  have hg2 : g ^ 2 = 1 := hfree (g ^ 2) p hsquare
  have hg1 : g = 1 := (sq_eq_one (a := g)).mp hg2
  simpa only [hg1, one_smul] using hgu

end LowDimensionalTopology.Geometry.Hyperbolic
