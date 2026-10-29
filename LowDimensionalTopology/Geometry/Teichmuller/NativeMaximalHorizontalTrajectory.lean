/-
Copyright (c) 2026 Wu Xiaobin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LowDimensionalTopology.Geometry.Surfaces.Riemann.HolomorphicQuadraticDifferential
public import LowDimensionalTopology.External.LiZhongQC.Ch07.S26_TeichmullerUniqueness
public import Mathlib.Analysis.Convex.Topology

/-!
# Maximal natural-parameter horizontal trajectories

The maximal interval retains the direction of one actual local germ. A curve
may be periodic, and its finite ends approach zeros of the same differential.

The admissible-interval gluing construction is adapted from Wu Xiaobin's
Li-Zhong-QC-formalization, LiZhongQC/Ch07/S26_TeichmullerUniqueness.lean,
s26v_mem_critArc, fixed commit 1c0d5473c020b66ed5106331a38a61536760b9b2
(Apache-2.0). The finite-end result reuses its s26v_a_right_end theorem.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set Filter
open scoped Topology

namespace LowDimensionalTopology.Geometry.Teichmuller
open Surfaces LiZhongQC

/-- The maximal continuation of a normalized horizontal germ through p.
Only values on the open interval J enter; no injectivity is required. -/
def IsMaximalHorizontalTrajectory
    {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas)
    (p : X) (J : Set ℝ) (c : ℝ → X) : Prop :=
  letI := R.toRiemannAtlas.toChartedSpace
  IsOpen J ∧ Convex ℝ J ∧ (0 : ℝ) ∈ J ∧ c 0 = p ∧
    (∀ t ∈ J, s26v_IsTrajAt (q : X → ℂ → ℂ) c t) ∧
    ∀ (J' : Set ℝ) (c' : ℝ → X),
      IsOpen J' → Convex ℝ J' → (0 : ℝ) ∈ J' →
      (∀ t ∈ J', s26v_IsTrajAt (q : X → ℂ → ℂ) c' t) →
      c' =ᶠ[𝓝 (0 : ℝ)] c → J' ⊆ J

/-- Every regular original point has a maximal unit horizontal trajectory. -/
theorem exists_maximalHorizontalTrajectory
    {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas) (_hq : q ≠ 0)
    (p : X) :
    letI := R.toRiemannAtlas.toChartedSpace
    (q : X → ℂ → ℂ) p (chartAt ℂ p p) ≠ 0 →
      ∃ (J : Set ℝ) (c : ℝ → X), IsMaximalHorizontalTrajectory R q p J c := by
  classical
  let := R.t2Space
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  intro hreg
  let q₀ : X → ℂ → ℂ := q
  have hhol : IsHolQuadDiff q₀ := q.property
  -- the reference local trajectory `c₀` through `p`
  obtain ⟨B, Z, hpB, -, hB⟩ := s26v_exists_flowBox hhol hreg (univ_mem : univ ∈ 𝓝 p)
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hB.2.2.2.1 (Z p) ⟨p, hpB, rfl⟩
  obtain ⟨c₀, hc₀0, hc₀⟩ := s26v_flowBox_line hhol hB hpB (a := -r) (b := r) (by linarith) hr fun s hs => hball (by
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs]
    exact abs_lt.2 hs)
  -- admissible trajectories through `p`: those agreeing with `c₀` near `0`
  set Adm : (ℝ → X) → ℝ → ℝ → Prop := fun c a b =>
    a < 0 ∧ 0 < b ∧ (∀ t ∈ Ioo a b, s26v_IsTrajAt q₀ c t) ∧ c =ᶠ[𝓝 0] c₀ with hAdm
  have hAdm₀ : Adm c₀ (-r) r := ⟨by linarith, hr, fun t ht => (hc₀ t ht).2.2, EventuallyEq.rfl⟩
  have huniq : ∀ (c : ℝ → X) (a b : ℝ) (c' : ℝ → X) (a' b' : ℝ), Adm c a b → Adm c' a' b' →
      ∀ t ∈ Ioo (max a a') (min b b'), c t = c' t := by
    intro c a b c' a' b' h h' t ht
    exact s26v_a_eqOn_of_eventuallyEq hhol isOpen_Ioo isPreconnected_Ioo
      (fun s hs => h.2.2.1 s ⟨lt_of_le_of_lt (le_max_left _ _) hs.1, lt_of_lt_of_le hs.2 (min_le_left _ _)⟩)
      (fun s hs => h'.2.2.1 s ⟨lt_of_le_of_lt (le_max_right _ _) hs.1, lt_of_lt_of_le hs.2 (min_le_right _ _)⟩)
      (⟨max_lt h.1 h'.1, lt_min h.2.1 h'.2.1⟩ : (0 : ℝ) ∈ Ioo (max a a') (min b b'))
      (h.2.2.2.trans h'.2.2.2.symm) t ht
  -- the glued maximal trajectory
  set cs : ℝ → X := fun t => if h : ∃ x : (ℝ → X) × ℝ × ℝ, Adm x.1 x.2.1 x.2.2 ∧ t ∈ Ioo x.2.1 x.2.2 then
    (Classical.choose h).1 t else p with hcsdef
  have hcs : ∀ (c : ℝ → X) (a b : ℝ), Adm c a b → ∀ t ∈ Ioo a b, cs t = c t := by
    intro c a b h t ht
    have hex : ∃ x : (ℝ → X) × ℝ × ℝ, Adm x.1 x.2.1 x.2.2 ∧ t ∈ Ioo x.2.1 x.2.2 := ⟨(c, a, b), h, ht⟩
    have hspec := Classical.choose_spec hex
    have hval : cs t = (Classical.choose hex).1 t := by
      simp only [hcsdef, hex, ↓reduceDIte]
    rw [hval]
    exact huniq _ _ _ c a b hspec.1 h t ⟨max_lt hspec.2.1 ht.1, lt_min hspec.2.2 ht.2⟩
  have hcsT : ∀ (c : ℝ → X) (a b : ℝ), Adm c a b → ∀ t ∈ Ioo a b, s26v_IsTrajAt q₀ cs t := by
    intro c a b h t ht
    refine s26v_a_trajAt_congr (h.2.2.1 t ht) ?_
    filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs using (hcs c a b h s hs).symm
  have h0r : (0 : ℝ) ∈ Ioo (-r) r := ⟨by linarith, hr⟩
  have hcs0 : cs =ᶠ[𝓝 0] c₀ := by
    filter_upwards [isOpen_Ioo.mem_nhds h0r] with s hs using hcs c₀ (-r) r hAdm₀ s hs
  have hcsp : cs 0 = p := by rw [hcs c₀ (-r) r hAdm₀ 0 h0r, hc₀0]
  let A := {x : (ℝ → X) × ℝ × ℝ // Adm x.1 x.2.1 x.2.2}
  let J : Set ℝ := ⋃ x : A, Ioo x.val.2.1 x.val.2.2
  have hinc : ∀ (d : ℝ → X) (a b : ℝ), Adm d a b → Ioo a b ⊆ J := by
    intro d a b hd t ht
    exact mem_iUnion.mpr ⟨⟨(d, a, b), hd⟩, ht⟩
  have hJo : IsOpen J := isOpen_iUnion fun _ => isOpen_Ioo
  have hJc : Convex ℝ J := by
    apply IsPreconnected.convex
    exact isPreconnected_iUnion
      ⟨0, mem_iInter.mpr fun x => ⟨x.property.1, x.property.2.1⟩⟩
      (fun _ => isPreconnected_Ioo)
  have hJ0 : (0 : ℝ) ∈ J := hinc c₀ (-r) r hAdm₀ h0r
  have hJT : ∀ t ∈ J, s26v_IsTrajAt q₀ cs t := by
    intro t ht
    obtain ⟨x, hx⟩ := mem_iUnion.mp ht
    exact hcsT x.val.1 x.val.2.1 x.val.2.2 x.property t hx
  refine ⟨J, cs, hJo, hJc, hJ0, hcsp, hJT, ?_⟩
  intro J' c' hJo' hJc' hJ0' hc' heq t ht
  have hmin : min (0 : ℝ) t ∈ J' := by
    rcases le_total (0 : ℝ) t with h | h
    · simpa only [min_eq_left h] using hJ0'
    · simpa only [min_eq_right h] using ht
  have hmax : max (0 : ℝ) t ∈ J' := by
    rcases le_total (0 : ℝ) t with h | h
    · simpa only [max_eq_right h] using ht
    · simpa only [max_eq_left h] using hJ0'
  obtain ⟨l, u, hminI, hminSub⟩ :=
    mem_nhds_iff_exists_Ioo_subset.mp (hJo'.mem_nhds hmin)
  obtain ⟨l', u', hmaxI, hmaxSub⟩ :=
    mem_nhds_iff_exists_Ioo_subset.mp (hJo'.mem_nhds hmax)
  let a : ℝ := (l + min 0 t) / 2
  let b : ℝ := (max 0 t + u') / 2
  have ha : a < min 0 t := by dsimp only [a]; linarith [hminI.1]
  have hb : max 0 t < b := by dsimp only [b]; linarith [hmaxI.2]
  have haJ : a ∈ J' := hminSub (by
    dsimp only [a]
    constructor <;> linarith [hminI.1, hminI.2])
  have hbJ : b ∈ J' := hmaxSub (by
    dsimp only [b]
    constructor <;> linarith [hmaxI.1, hmaxI.2])
  have ha0 : a < 0 := ha.trans_le (min_le_left 0 t)
  have hb0 : 0 < b := (le_max_left 0 t).trans_lt hb
  have hAdm' : Adm c' a b :=
    ⟨ha0, hb0, fun s hs => hc' s
      (hJc'.ordConnected.out haJ hbJ ⟨le_of_lt hs.1, le_of_lt hs.2⟩),
      heq.trans hcs0⟩
  exact hinc c' a b hAdm'
    ⟨ha.trans_le (min_le_right 0 t), (le_max_right 0 t).trans_lt hb⟩

/-- Every finite maximal right end converges to an actual zero of the same q. -/
theorem IsMaximalHorizontalTrajectory.right_end_zero
    {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas) (hq : q ≠ 0)
    {p : X} {J : Set ℝ} {c : ℝ → X}
    (h : IsMaximalHorizontalTrajectory R q p J c) (hJ : BddAbove J) :
    letI := R.toRiemannAtlas.toChartedSpace
    ∃ z : X, (q : X → ℂ → ℂ) z (chartAt ℂ z z) = 0 ∧
      Tendsto c (𝓝[<] (sSup J)) (𝓝 z) := by
  let := R.t2Space
  let := R.connectedSpace
  let := R.compactSpace
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  obtain ⟨hJo, hJc, hJ0, _, hc, hmax⟩ := h
  obtain ⟨a₀, b₀, h0, hsub⟩ :=
    mem_nhds_iff_exists_Ioo_subset.mp (hJo.mem_nhds hJ0)
  let a : ℝ := a₀ / 2
  have ha0 : a < 0 := by dsimp only [a]; linarith [h0.1]
  have haJ : a ∈ J := hsub (by
    dsimp only [a]
    constructor <;> linarith [h0.1, h0.2])
  have hbJ : b₀ / 2 ∈ J := hsub (by
    constructor <;> linarith [h0.1, h0.2])
  have hb0 : 0 < sSup J :=
    lt_of_lt_of_le (by linarith [h0.2] : 0 < b₀ / 2) (le_csSup hJ hbJ)
  have hab : a < sSup J := ha0.trans hb0
  have hI : Ioo a (sSup J) ⊆ J := by
    intro t ht
    obtain ⟨u, hu, htu⟩ := exists_lt_of_lt_csSup ⟨0, hJ0⟩ ht.2
    exact hJc.ordConnected.out haJ hu ⟨le_of_lt ht.1, le_of_lt htu⟩
  have hT : ∀ t ∈ Ioo a (sSup J), s26v_IsTrajAt (q : X → ℂ → ℂ) c t :=
    fun t ht => hc t (hI ht)
  have hNE : ∀ (c' : ℝ → X) (b' : ℝ), sSup J < b' →
      (∀ t ∈ Ioo a b', s26v_IsTrajAt (q : X → ℂ → ℂ) c' t) →
      ∀ t₀ ∈ Ioo a (sSup J), c' =ᶠ[𝓝 t₀] c → False := by
    intro c' b' hb' hc' t₀ ht₀ heq
    have heqI := s26v_a_eqOn_of_eventuallyEq q.property isOpen_Ioo isPreconnected_Ioo
      (fun s hs => hc' s ⟨hs.1, hs.2.trans hb'⟩) hT ht₀ heq
    have heq0 : c' =ᶠ[𝓝 (0 : ℝ)] c := by
      filter_upwards [isOpen_Ioo.mem_nhds (⟨ha0, hb0⟩ : (0 : ℝ) ∈ Ioo a (sSup J))]
        with s hs using heqI s hs
    have hsub' : Ioo a b' ⊆ J :=
      hmax (Ioo a b') c' isOpen_Ioo (convex_Ioo a b') ⟨ha0, hb0.trans hb'⟩ hc' heq0
    obtain ⟨v, hbv, hvb'⟩ := exists_between hb'
    have hvJ : v ∈ J := hsub' ⟨hab.trans hbv, hvb'⟩
    exact (not_lt_of_ge (le_csSup hJ hvJ)) hbv
  have hqne : (q : X → ℂ → ℂ) ≠ 0 := by
    intro hzero
    exact hq (Subtype.ext hzero)
  exact s26v_a_right_end q.property hqne hab hT hNE

end LowDimensionalTopology.Geometry.Teichmuller
