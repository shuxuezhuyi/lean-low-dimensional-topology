/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Topology.EMetricSpace.VariationOnFromTo
public import Mathlib.Topology.MetricSpace.Lipschitz
public import Mathlib.Topology.Order.IntermediateValue

/-!
# Arclength factorization of continuous rectifiable curves

The parameter is the actual cumulative variation. It preserves traversal,
including repeated arcs and pauses. The factor is globally 1-Lipschitz, and its
variation on each subinterval of the length interval is that interval's length.
The construction also covers constant curves and singleton parameter intervals.
-/

public section

open Set
open scoped ENNReal

namespace LowDimensionalTopology.Geometry

variable {E : Type*} [MetricSpace E]

/-- The variation clock controls distance, even when the original curve has
pauses and is not absolutely continuous in its original parameter. -/
theorem dist_le_dist_variationOnFromTo {f : ℝ → E} {S : Set ℝ}
    (hBV : BoundedVariationOn f S) {a x y : ℝ}
    (ha : a ∈ S) (hx : x ∈ S) (hy : y ∈ S) :
    dist (f x) (f y) ≤
      dist (variationOnFromTo f S a x) (variationOnFromTo f S a y) := by
  have hord : ∀ {u v : ℝ}, u ∈ S → v ∈ S → u ≤ v →
      dist (f u) (f v) ≤
        dist (variationOnFromTo f S a u) (variationOnFromTo f S a v) := by
    intro u v hu hv huv
    calc
      dist (f u) (f v) ≤ (eVariationOn f (S ∩ Icc u v)).toReal :=
        (hBV.mono inter_subset_left).dist_le ⟨hu, le_rfl, huv⟩ ⟨hv, huv, le_rfl⟩
      _ = variationOnFromTo f S a v - variationOnFromTo f S a u := by
        rw [variationOnFromTo.sub_right hBV.locallyBoundedVariationOn ha hv hu,
          variationOnFromTo.eq_of_le f S huv]
      _ = dist (variationOnFromTo f S a u) (variationOnFromTo f S a v) := by
        rw [Real.dist_eq, abs_sub_comm, abs_of_nonneg]
        exact sub_nonneg.mpr (variationOnFromTo.monotoneOn
          hBV.locallyBoundedVariationOn ha hu hv huv)
  rcases le_total x y with hxy | hyx
  · exact hord hx hy hxy
  · calc
      dist (f x) (f y) = dist (f y) (f x) := dist_comm _ _
      _ ≤ dist (variationOnFromTo f S a y) (variationOnFromTo f S a x) :=
        hord hy hx hyx
      _ = dist (variationOnFromTo f S a x) (variationOnFromTo f S a y) := dist_comm _ _

/-- Every continuous bounded-variation curve factors through its actual arclength
clock. The factor extends to the entire real line by interval projection.
No injectivity, positive length, or absolute continuity of the original curve is
assumed. Both total variation and variation on each length subinterval are exact. -/
theorem exists_arclength_factorization {f : ℝ → E} {a b : ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Icc a b)) (hBV : BoundedVariationOn f (Icc a b)) :
    let s := variationOnFromTo f (Icc a b) a
    let L := s b
    0 ≤ L ∧ ContinuousOn s (Icc a b) ∧ MonotoneOn s (Icc a b) ∧
      s a = 0 ∧ s '' Icc a b = Icc 0 L ∧
      ∃ γ : ℝ → E, LipschitzWith 1 γ ∧ EqOn f (γ ∘ s) (Icc a b) ∧
        γ 0 = f a ∧ γ L = f b ∧ γ '' Icc 0 L = f '' Icc a b ∧
        eVariationOn γ (Icc 0 L) = eVariationOn f (Icc a b) ∧
        ∀ u v : ℝ, u ∈ Icc 0 L → v ∈ Icc 0 L → u ≤ v →
          eVariationOn γ (Icc u v) = ENNReal.ofReal (v - u) := by
  classical
  let s := variationOnFromTo f (Icc a b) a
  let L := s b
  have ha : a ∈ Icc a b := ⟨le_rfl, hab⟩
  have hb : b ∈ Icc a b := ⟨hab, le_rfl⟩
  have hs0 : s a = 0 := variationOnFromTo.self f (Icc a b) a
  have hL : 0 ≤ L := variationOnFromTo.nonneg_of_le f (Icc a b) hab
  have hscont : ContinuousOn s (Icc a b) := fun t ht =>
    (hBV.continuousWithinAt_variationOnFromTo_iff ha ht).mpr (hf t ht)
  have hsmono : MonotoneOn s (Icc a b) :=
    variationOnFromTo.monotoneOn hBV.locallyBoundedVariationOn ha
  have hsimage : s '' Icc a b = Icc 0 L := by
    simpa only [hs0] using hscont.image_Icc_of_monotoneOn hab hsmono
  have hsurj : SurjOn s (Icc a b) (Icc 0 L) := by
    intro r hr
    rw [← hsimage] at hr
    exact hr
  let τ (r : Icc (0 : ℝ) L) : ℝ := Classical.choose (hsurj r.property)
  have hτ (r : Icc (0 : ℝ) L) : τ r ∈ Icc a b ∧ s (τ r) = r :=
    Classical.choose_spec (hsurj r.property)
  have hτmono : Monotone τ := by
    intro u v huv
    by_contra h
    have hvu := hsmono (hτ v).1 (hτ u).1 (lt_of_not_ge h).le
    rw [(hτ v).2, (hτ u).2] at hvu
    have heq : u = v := Subtype.ext (le_antisymm huv hvu)
    exact h (le_of_eq (congrArg τ heq))
  let γ₀ : Icc (0 : ℝ) L → E := fun r => f (τ r)
  have hγ₀ : LipschitzWith 1 γ₀ := by
    apply LipschitzWith.mk_one
    intro u v
    calc
      dist (γ₀ u) (γ₀ v) ≤ dist (s (τ u)) (s (τ v)) :=
        dist_le_dist_variationOnFromTo hBV ha (hτ u).1 (hτ v).1
      _ = dist u v := by simp only [(hτ u).2, (hτ v).2, Subtype.dist_eq]
  let γ : ℝ → E := γ₀ ∘ Set.projIcc 0 L hL
  have hγ : LipschitzWith 1 γ := by
    simpa only [one_mul] using hγ₀.comp (LipschitzWith.projIcc hL)
  have hfactor : EqOn f (γ ∘ s) (Icc a b) := by
    intro t ht
    have hst : s t ∈ Icc 0 L := by
      rw [← hsimage]
      exact mem_image_of_mem s ht
    change f t = f (τ (Set.projIcc 0 L hL (s t)))
    rw [Set.projIcc_of_mem hL hst]
    apply dist_le_zero.mp
    calc
      dist (f t) (f (τ ⟨s t, hst⟩)) ≤ dist (s t) (s (τ ⟨s t, hst⟩)) :=
        dist_le_dist_variationOnFromTo hBV ha ht (hτ ⟨s t, hst⟩).1
      _ = 0 := by rw [(hτ ⟨s t, hst⟩).2, dist_self]
  have hγ0 : γ 0 = f a := by simpa only [Function.comp_apply, hs0] using (hfactor ha).symm
  have hγL : γ L = f b := (hfactor hb).symm
  have himage : γ '' Icc 0 L = f '' Icc a b := by
    calc
      γ '' Icc 0 L = (γ ∘ s) '' Icc a b := by
        rw [← hsimage]
        simpa only [Function.comp_def] using Set.image_image γ s (Icc a b)
      _ = f '' Icc a b := hfactor.symm.image_eq
  have hvar : eVariationOn γ (Icc 0 L) = eVariationOn f (Icc a b) := by
    calc
      eVariationOn γ (Icc 0 L) = eVariationOn (γ ∘ s) (Icc a b) := by
        rw [eVariationOn.comp_eq_of_monotoneOn γ s hsmono, hsimage]
      _ = eVariationOn f (Icc a b) := (eVariationOn.congr hfactor).symm
  refine ⟨hL, hscont, hsmono, hs0, hsimage, γ, hγ, hfactor, hγ0, hγL, himage, hvar, ?_⟩
  intro u v hu hv huv
  let t := τ ⟨u, hu⟩
  let q := τ ⟨v, hv⟩
  have ht : t ∈ Icc a b := (hτ ⟨u, hu⟩).1
  have hq : q ∈ Icc a b := (hτ ⟨v, hv⟩).1
  have hst : s t = u := (hτ ⟨u, hu⟩).2
  have hsq : s q = v := (hτ ⟨v, hv⟩).2
  have htq : t ≤ q := hτmono huv
  calc
    eVariationOn γ (Icc u v) =
        eVariationOn γ (Icc 0 L ∩ Icc (s t) (s q)) := by
      rw [hst, hsq, inter_eq_right.mpr (Icc_subset_Icc hu.1 hv.2)]
    _ = eVariationOn (γ ∘ s) (Icc a b ∩ Icc t q) := by
      rw [eVariationOn.comp_inter_Icc_eq_of_monotoneOn γ s hsmono ht hq, hsimage]
    _ = eVariationOn f (Icc a b ∩ Icc t q) :=
      (eVariationOn.congr (hfactor.mono inter_subset_left)).symm
    _ = ENNReal.ofReal (s q - s t) := by
      change eVariationOn f (Icc a b ∩ Icc t q) =
        ENNReal.ofReal (variationOnFromTo f (Icc a b) a q -
          variationOnFromTo f (Icc a b) a t)
      rw [variationOnFromTo.sub_right hBV.locallyBoundedVariationOn ha hq ht,
        variationOnFromTo.eq_of_le f (Icc a b) htq,
        ENNReal.ofReal_toReal (hBV.mono inter_subset_left)]
    _ = ENNReal.ofReal (v - u) := by rw [hst, hsq]

end LowDimensionalTopology.Geometry
