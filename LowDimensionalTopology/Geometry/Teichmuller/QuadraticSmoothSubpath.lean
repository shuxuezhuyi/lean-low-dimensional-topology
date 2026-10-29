module

public import LowDimensionalTopology.Geometry.Teichmuller.QuadraticPiecewiseSmoothPath
public import Mathlib.Data.Finset.Sort
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! Smooth finite chart subdivisions restricted to increasing affine subpaths. -/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set
open scoped ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller
open Surfaces

universe u
variable {X : Type u} [TopologicalSpace X]

/-- A proper increasing subpath retains a finite smooth subdivision in the
same original atlas. No condition is imposed on its endpoint velocities. -/
theorem HasPiecewiseSmoothChartSubdivision.subpath_of_lt
    {R : RiemannSurface X} {a b : X} {γ : Path a b}
    (hγ : HasPiecewiseSmoothChartSubdivision R γ)
    (s t : unitInterval) (hst : s < t) :
    HasPiecewiseSmoothChartSubdivision R (γ.subpath s t) := by
  classical
  let := R.toRiemannAtlas.toChartedSpace
  obtain ⟨n, τ, x, h0, hn, _hτ, hsrc, hsm⟩ := hγ
  have hstR : (s : ℝ) < t := hst
  let S : Finset ℝ := {(s : ℝ), (t : ℝ)} ∪
    ((Finset.univ.image τ).filter fun v => (s : ℝ) < v ∧ v < t)
  have hsS : (s : ℝ) ∈ S := by simp [S]
  have htS : (t : ℝ) ∈ S := by simp [S]
  have hbounds {v : ℝ} (hv : v ∈ S) : v ∈ Icc (s : ℝ) t := by
    rcases Finset.mem_union.mp hv with hp | hp
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl
      · exact ⟨le_rfl, hstR.le⟩
      · exact ⟨hstR.le, le_rfl⟩
    · exact ⟨(Finset.mem_filter.mp hp).2.1.le, (Finset.mem_filter.mp hp).2.2.le⟩
  have hcard2 : 2 ≤ S.card := by
    have h := Finset.card_le_card
      (show ({(s : ℝ), (t : ℝ)} : Finset ℝ) ⊆ S from Finset.subset_union_left)
    simpa only [Finset.card_pair hstR.ne] using h
  let k : ℕ := S.card - 1
  have hcard : S.card = k + 1 := by dsimp only [k]; omega
  let ρ : Fin (k + 1) ↪o ℝ := S.orderEmbOfFin hcard
  have hρmem (i : Fin (k + 1)) : ρ i ∈ S := Finset.orderEmbOfFin_mem S hcard i
  have hρrange : Set.range (ρ : Fin (k + 1) → ℝ) = (S : Set ℝ) :=
    Finset.range_orderEmbOfFin S hcard
  have honto {v : ℝ} (hv : v ∈ S) : ∃ i, ρ i = v := by
    have : v ∈ Set.range (ρ : Fin (k + 1) → ℝ) := by rw [hρrange]; exact hv
    exact this
  have hρ0 : ρ 0 = (s : ℝ) := by
    obtain ⟨i, hi⟩ := honto hsS
    apply le_antisymm
    · simpa only [hi] using ρ.strictMono.monotone (Fin.zero_le i)
    · exact (hbounds (hρmem 0)).1
  have hρ1 : ρ (Fin.last k) = (t : ℝ) := by
    obtain ⟨i, hi⟩ := honto htS
    apply le_antisymm
    · exact (hbounds (hρmem (Fin.last k))).2
    · simpa only [hi] using ρ.strictMono.monotone (Fin.le_last i)
  have hno (i : Fin k) (j : Fin (n + 1)) :
      ¬ (ρ i.castSucc < τ j ∧ τ j < ρ i.succ) := by
    intro h
    have hjS : τ j ∈ S := Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr
      ⟨Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩,
        (hbounds (hρmem i.castSucc)).1.trans_lt h.1,
        h.2.trans_le (hbounds (hρmem i.succ)).2⟩))
    obtain ⟨a, ha⟩ := honto hjS
    have hia : i.castSucc < a := ρ.strictMono.lt_iff_lt.mp (by simpa only [ha] using h.1)
    have hai : a < i.succ := ρ.strictMono.lt_iff_lt.mp (by simpa only [ha] using h.2)
    rw [Fin.lt_def, Fin.val_castSucc] at hia
    rw [Fin.lt_def, Fin.val_succ] at hai
    omega
  have hcover (v : ℝ) (hv0 : 0 ≤ v) (hv1 : v < 1) :
      ∃ j : Fin n, τ j.castSucc ≤ v ∧ v < τ j.succ := by
    let J : Finset (Fin (n + 1)) := Finset.univ.filter fun j => v < τ j
    have hJ : J.Nonempty := ⟨Fin.last n, Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, by simpa only [hn] using hv1⟩⟩
    let j : Fin (n + 1) := J.min' hJ
    have hj : v < τ j := (Finset.mem_filter.mp (Finset.min'_mem J hJ)).2
    have hjpos : 0 < j.val := by
      by_contra h
      have hj0 : j = 0 := by
        apply Fin.ext
        rw [Fin.val_zero]
        omega
      rw [hj0, h0] at hj
      exact (not_lt_of_ge hv0) hj
    let i : Fin n := ⟨j.val - 1, by have hjlt := j.is_lt; omega⟩
    have hiSucc : i.succ = j := by
      apply Fin.ext
      rw [Fin.val_succ]
      dsimp only [i]
      omega
    have hiLt : i.castSucc < j := by change i.val < j.val; dsimp only [i]; omega
    have hprev : τ i.castSucc ≤ v := by
      by_contra h
      have hiJ : i.castSucc ∈ J := Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, lt_of_not_ge h⟩
      have hmin : j ≤ i.castSucc := Finset.min'_le J _ hiJ
      exact (not_lt_of_ge hmin) hiLt
    exact ⟨i, hprev, by simpa only [hiSucc] using hj⟩
  have hfit (i : Fin k) : ∃ j : Fin n,
      τ j.castSucc ≤ ρ i.castSucc ∧ ρ i.succ ≤ τ j.succ := by
    have hab : ρ i.castSucc < ρ i.succ := ρ.strictMono (by change i.val < i.val + 1; omega)
    let v : ℝ := (ρ i.castSucc + ρ i.succ) / 2
    have hva : ρ i.castSucc < v := by dsimp only [v]; linarith
    have hvb : v < ρ i.succ := by dsimp only [v]; linarith
    have hv0 : 0 ≤ v := s.property.1.trans ((hbounds (hρmem i.castSucc)).1.trans hva.le)
    have hv1 : v < 1 := hvb.trans_le ((hbounds (hρmem i.succ)).2.trans t.property.2)
    obtain ⟨j, hjl, hjr⟩ := hcover v hv0 hv1
    refine ⟨j, ?_, ?_⟩
    · by_contra h
      exact hno i j.castSucc ⟨lt_of_not_ge h, hjl.trans_lt hvb⟩
    · by_contra h
      exact hno i j.succ ⟨hva.trans hjr, lt_of_not_ge h⟩
  choose j hjl hjr using hfit
  let L : ℝ := (t : ℝ) - s
  have hL : 0 < L := sub_pos.mpr hstR
  let σ : Fin (k + 1) → ℝ := fun i => (ρ i - s) / L
  let A : ℝ → ℝ := fun v => v * L + s
  have hAσ (i : Fin (k + 1)) : A (σ i) = ρ i := by
    dsimp only [A, σ]
    rw [div_mul_cancel₀ _ hL.ne', sub_add_cancel]
  have hσ0 : σ 0 = 0 := by dsimp only [σ]; rw [hρ0, sub_self, zero_div]
  have hσ1 : σ (Fin.last k) = 1 := by
    dsimp only [σ, L]
    rw [hρ1, div_self (sub_pos.mpr hstR).ne']
  have hσ : StrictMono σ := by
    intro i j hij
    exact div_lt_div_of_pos_right (sub_lt_sub_right (ρ.strictMono hij) _) hL
  have hunit (i : Fin k) (v : ℝ) (hv : v ∈ Icc (σ i.castSucc) (σ i.succ)) :
      v ∈ Icc (0 : ℝ) 1 := by
    have hlo : 0 ≤ σ i.castSucc := by
      simpa only [hσ0] using hσ.monotone (Fin.zero_le i.castSucc)
    have hhi : σ i.succ ≤ 1 := by
      simpa only [hσ1] using hσ.monotone (Fin.le_last i.succ)
    exact ⟨hlo.trans hv.1, hv.2.trans hhi⟩
  have hAm : Monotone A := by
    intro u v huv
    dsimp only [A]
    exact add_le_add (mul_le_mul_of_nonneg_right huv hL.le) le_rfl
  have hmapA (i : Fin k) : MapsTo A (Icc (σ i.castSucc) (σ i.succ))
      (Icc (τ (j i).castSucc) (τ (j i).succ)) := by
    intro v hv
    have hlo : ρ i.castSucc ≤ A v := by simpa only [hAσ] using hAm hv.1
    have hhi : A v ≤ ρ i.succ := by simpa only [hAσ] using hAm hv.2
    exact ⟨(hjl i).trans hlo, hhi.trans (hjr i)⟩
  have hcomb (v : ℝ) (hv : v ∈ Icc (0 : ℝ) 1) :
      (Icc.convexComb s t ⟨v, hv⟩ : ℝ) = A v := by
    rw [Icc.coe_convexComb]
    dsimp only [A, L]
    ring
  have hA01 (v : ℝ) (hv : v ∈ Icc (0 : ℝ) 1) : A v ∈ Icc (0 : ℝ) 1 := by
    rw [← hcomb v hv]
    exact (Icc.convexComb s t ⟨v, hv⟩).property
  have hext (v : ℝ) (hv : v ∈ Icc (0 : ℝ) 1) :
      (γ.subpath s t).extend v = γ.extend (A v) := by
    rw [Path.extend_apply _ hv]
    change γ (Icc.convexComb s t ⟨v, hv⟩) = γ.extend (A v)
    rw [Path.extend_apply γ (hA01 v hv)]
    exact congrArg γ (Subtype.ext (hcomb v hv))
  have hAc : ContDiff ℝ ∞ A := by dsimp only [A]; fun_prop
  refine ⟨k, σ, fun i => x (j i), hσ0, hσ1, hσ, ?_, ?_⟩
  · intro i
    rintro _ ⟨v, hv, rfl⟩
    rw [hext v (hunit i v hv)]
    exact hsrc (j i) ⟨A v, hmapA i hv, rfl⟩
  · intro i
    have hc : ContDiffOn ℝ ∞ (fun v : ℝ => chartAt ℂ (x (j i)) (γ.extend (A v)))
        (Icc (σ i.castSucc) (σ i.succ)) := (hsm (j i)).comp hAc.contDiffOn (hmapA i)
    refine hc.congr ?_
    intro v hv
    change chartAt ℂ (x (j i)) ((γ.subpath s t).extend v) =
      chartAt ℂ (x (j i)) (γ.extend (A v))
    rw [hext v (hunit i v hv)]

end LowDimensionalTopology.Geometry.Teichmuller
