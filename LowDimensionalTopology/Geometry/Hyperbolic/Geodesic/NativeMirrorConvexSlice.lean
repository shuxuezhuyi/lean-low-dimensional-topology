module

public import LowDimensionalTopology.Geometry.Hyperbolic.Geodesic.ClosedGeodesicRays
public import LowDimensionalTopology.Geometry.Hyperbolic.Triangle.TriangleCoordinates
public import LowDimensionalTopology.Geometry.Polygon.Quadrilateral.SaccheriQuadrilaterals
public import Mathlib.Analysis.Convex.Topology

/-!
# A symmetric open convex region has an exact native mirror clip

Two distinct frontier points on a genuine mirror determine its entire open
intersection with a nonempty reflection-invariant hyperbolically convex region.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set
open scoped UpperHalfPlane

namespace LowDimensionalTopology.Geometry.Hyperbolic

private theorem complex_open_convex_lineMap_preimage (U : Set ℂ)
    (hU : Convex ℝ U) (hoU : IsOpen U) (a b : ℂ)
    (ha : a ∈ frontier U) (hb : b ∈ frontier U)
    (hn : ((AffineMap.lineMap a b : ℝ →ᵃ[ℝ] ℂ) ⁻¹' U).Nonempty) :
    (AffineMap.lineMap a b : ℝ →ᵃ[ℝ] ℂ) ⁻¹' U = Ioo 0 1 := by
  let A : ℝ →ᵃ[ℝ] ℂ := AffineMap.lineMap a b
  rw [hoU.frontier_eq] at ha hb
  ext t
  change A t ∈ U ↔ 0 < t ∧ t < 1
  constructor
  · intro ht
    have htI : A t ∈ interior U := hoU.interior_eq.symm ▸ ht
    constructor
    · by_contra hpos
      rcases lt_or_eq_of_le (not_lt.mp hpos : t ≤ 0) with hlt | heq
      · have hzero : a ∈ openSegment ℝ (A t) b := by
          have hh : A 0 ∈ A '' openSegment ℝ t 1 :=
            ⟨0, Ioo_subset_openSegment ⟨hlt, zero_lt_one⟩, rfl⟩
          simpa only [image_openSegment, A, AffineMap.lineMap_apply_zero,
            AffineMap.lineMap_apply_one] using hh
        exact ha.2 (interior_subset
          (hU.openSegment_interior_closure_subset_interior htI hb.1 hzero))
      · subst t
        exact ha.2 (by simpa only [A, AffineMap.lineMap_apply_zero] using ht)
    · by_contra hlt
      rcases lt_or_eq_of_le (not_lt.mp hlt : 1 ≤ t) with hgt | heq
      · have hone : b ∈ openSegment ℝ a (A t) := by
          have hh : A 1 ∈ A '' openSegment ℝ 0 t :=
            ⟨1, Ioo_subset_openSegment ⟨zero_lt_one, hgt⟩, rfl⟩
          simpa only [image_openSegment, A, AffineMap.lineMap_apply_zero,
            AffineMap.lineMap_apply_one] using hh
        exact hb.2 (interior_subset
          (hU.openSegment_closure_interior_subset_interior ha.1 htI hone))
      · subst t
        exact hb.2 (by simpa only [A, AffineMap.lineMap_apply_one] using ht)
  · intro ht
    obtain ⟨u, hu⟩ := hn
    change A u ∈ U at hu
    have huI : A u ∈ interior U := hoU.interior_eq.symm ▸ hu
    have hsplit := openSegment_subset_union (𝕜 := ℝ) a b
      (z := A u) ⟨u, rfl⟩ (lineMap_mem_openSegment ℝ a b ht)
    rcases hsplit with heq | hrest
    · exact heq.symm ▸ hu
    · rcases hrest with hleft | hright
      · exact interior_subset
          (hU.openSegment_closure_interior_subset_interior ha.1 huI hleft)
      · exact interior_subset
          (hU.openSegment_interior_closure_subset_interior huI hb.1 hright)

private theorem hConvex_inter_mirror_nonempty {K : Set ℍ} (hK : HConvex K)
    (hn : K.Nonempty) (L : HalfPlaneLine) (hsym : L.reflection '' K = K) :
    (K ∩ L.carrier).Nonempty := by
  obtain ⟨z, hz⟩ := hn
  by_cases hzL : z ∈ L.carrier
  · exact ⟨z, hz, hzL⟩
  obtain ⟨M, ⟨hzM, ⟨p, hp⟩⟩, _⟩ := L.existsUnique_perpendicular z
  have hzp : z ≠ p := fun heq => hzL (heq.symm ▸ hp.1)
  have hzR : L.reflection z ∈ K := hsym ▸ mem_image_of_mem L.reflection hz
  exact ⟨p, hK z hz (L.reflection z) hzR
    (L.reflection_perpendicular_midpoint M p z hp hzM hzp).1, hp.1⟩

private theorem klein_mem_openHSegment_iff {p q z : ℍ} (hpq : p ≠ q) :
    halfPlaneKleinCoordinate z ∈ openSegment ℝ
      (halfPlaneKleinCoordinate p) (halfPlaneKleinCoordinate q) ↔
      z ∈ openHSegment p q := by
  rw [mem_openHSegment_iff hpq]
  constructor
  · intro hz
    refine ⟨?_, ?_, ?_⟩
    · have hc := openSegment_subset_segment ℝ _ _ hz
      rw [← halfPlaneKlein_image_closedHSegment] at hc
      obtain ⟨w, hw, heq⟩ := hc
      exact halfPlaneKleinCoordinate_injective heq ▸ hw
    · intro heq
      subst z
      exact hpq (halfPlaneKleinCoordinate_injective (left_mem_openSegment_iff.mp hz))
    · intro heq
      subst z
      exact hpq (halfPlaneKleinCoordinate_injective (right_mem_openSegment_iff.mp hz))
  · rintro ⟨hz, hzp, hzq⟩
    apply mem_openSegment_of_ne_left_right
      (halfPlaneKleinCoordinate_injective.ne hzp.symm)
      (halfPlaneKleinCoordinate_injective.ne hzq.symm)
    rw [← halfPlaneKlein_image_closedHSegment]
    exact mem_image_of_mem halfPlaneKleinCoordinate hz

/-- The exact mirror slice between two actual distinct frontier points. -/
theorem HConvex.inter_mirror_eq_openHSegment {K : Set ℍ} (hK : HConvex K)
    (hoK : IsOpen K) (hnK : K.Nonempty) (L : HalfPlaneLine)
    (hsym : L.reflection '' K = K) (p q : ℍ)
    (hpL : p ∈ L.carrier) (hqL : q ∈ L.carrier)
    (hpF : p ∈ frontier K) (hqF : q ∈ frontier K) (hpq : p ≠ q) :
    K ∩ L.carrier = openHSegment p q := by
  let k : ℍ → ℂ := halfPlaneKleinCoordinate
  let U : Set ℂ := k '' K
  let A : ℝ →ᵃ[ℝ] ℂ := AffineMap.lineMap (k p) (k q)
  have hk : Topology.IsOpenEmbedding k := isOpenEmbedding_halfPlaneKleinCoordinate
  have hoU : IsOpen U := hk.isOpenMap K hoK
  have hcU : Convex ℝ U := by
    have hc := (discHConvex_iff_klein_convex _).mp
      ((hConvex_iff_cayley_discHConvex K).mp hK)
    rw [image_image] at hc
    exact hc
  have hfront (z : ℍ) (hz : z ∈ frontier K) : k z ∈ frontier U := by
    rw [hoK.frontier_eq] at hz
    rw [hoU.frontier_eq]
    refine ⟨image_closure_subset_closure_image hk.continuous ⟨z, hz.1, rfl⟩, ?_⟩
    rintro ⟨w, hw, heq⟩
    exact hz.2 (hk.injective heq ▸ hw)
  obtain ⟨m, c, hm, hline⟩ := L.klein_affine_equation
  have hparam (z : ℍ) (hz : z ∈ L.carrier) : ∃ t : ℝ, A t = k z := by
    let t := inner ℝ (k q - k p) (k z - k p) / ‖k q - k p‖ ^ 2
    refine ⟨t, ?_⟩
    have heq := affine_line_projection_identity hm (hk.injective.ne hpq)
      ((hline p).mp hpL) ((hline q).mp hqL) ((hline z).mp hz)
    simpa only [A, t, AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add,
      add_comm] using heq.symm
  obtain ⟨w, hwK, hwL⟩ := hConvex_inter_mirror_nonempty hK hnK L hsym
  obtain ⟨t, ht⟩ := hparam w hwL
  have hn : (A ⁻¹' U).Nonempty :=
    ⟨t, by
      change A t ∈ U
      rw [ht]
      exact mem_image_of_mem k hwK⟩
  have hA : A ⁻¹' U = Ioo 0 1 :=
    complex_open_convex_lineMap_preimage U hcU hoU (k p) (k q)
      (hfront p hpF) (hfront q hqF) hn
  ext z
  constructor
  · rintro ⟨hzK, hzL⟩
    obtain ⟨t, ht⟩ := hparam z hzL
    have htU : t ∈ A ⁻¹' U := by
      change A t ∈ U
      rw [ht]
      exact mem_image_of_mem k hzK
    rw [hA] at htU
    have hzOpen : k z ∈ openSegment ℝ (k p) (k q) :=
      ht ▸ lineMap_mem_openSegment ℝ (k p) (k q) htU
    exact (klein_mem_openHSegment_iff hpq).mp hzOpen
  · intro hz
    have hzOpen : k z ∈ openSegment ℝ (k p) (k q) :=
      (klein_mem_openHSegment_iff hpq).mpr hz
    obtain ⟨t, ht, heq⟩ : k z ∈ A '' Ioo 0 1 := by
      simpa only [A, openSegment_eq_image_lineMap] using hzOpen
    have htU : A t ∈ U := by
      change t ∈ A ⁻¹' U
      rwa [hA]
    obtain ⟨w, hwK, hwA⟩ := htU
    refine ⟨hk.injective (hwA.trans heq) ▸ hwK, ?_⟩
    exact L.hConvex p hpL q hqL ((mem_openHSegment_iff hpq).mp hz).1

end LowDimensionalTopology.Geometry.Hyperbolic
