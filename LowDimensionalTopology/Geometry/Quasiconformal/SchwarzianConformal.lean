/- Released under Apache 2.0 license as described in the file LICENSE. -/
module

public import LowDimensionalTopology.External.LiZhongQC.Ch05.S19_Schwarzian
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum

/-!
# Schwarzian composition and rigidity on conformal plane domains

The rigidity statement is about genuine holomorphic conformal maps. Its
fractional-linear representative has no pole anywhere in the original domain;
this is proved from continuity, rather than supplied as an additional premise.

The proof reuses Wu Xiaobin's LiZhongQC Schwarzian theorems, fixed upstream
commit 1c0d5473c020b66ed5106331a38a61536760b9b2, under Apache-2.0. The original
source and provenance are retained in the project's External source tree.
-/

@[expose] public section

noncomputable section

open Set Filter Topology

namespace LowDimensionalTopology.Geometry.Quasiconformal

/-- Composition of conformal maps satisfies the Schwarzian chain rule at every
point of the actual source domain. Derivative nonvanishing follows from
holomorphy and injectivity, without any extra derivative hypotheses. -/
theorem schwarzian_conformal_comp {D U V : Set ℂ} {f g : ℂ → ℂ}
    (hD : IsOpen D) (hf : LiZhongQC.IsConformalOnto f D U)
    (hg : LiZhongQC.IsConformalOnto g U V) :
    ∀ z ∈ D, LiZhongQC.schwarzian (g ∘ f) z =
      LiZhongQC.schwarzian g (f z) * deriv f z ^ 2 + LiZhongQC.schwarzian f z := by
  have hU : IsOpen U := LiZhongQC.IsConformalOnto.isOpen hD hf
  intro z hz
  have hfz : f z ∈ U := by
    rw [← hf.2.2]
    exact mem_image_of_mem f hz
  exact LiZhongQC.eq19_1_chain_rule (hf.1.analyticAt (hD.mem_nhds hz))
    (LiZhongQC.deriv_ne_zero_of_injOn hD hf.1 hf.2.1 hz)
    (hg.1.analyticAt (hU.mem_nhds hfz))
    (LiZhongQC.deriv_ne_zero_of_injOn hU hg.1 hg.2.1 hfz)

private theorem schwarzian_identity (z : ℂ) : LiZhongQC.schwarzian id z = 0 := by
  have h : (id : ℂ → ℂ) = fun w => (1 * w + 0) / (0 * w + 1) := by
    funext w
    simp
  rw [h]
  exact LiZhongQC.schwarzian_mobius (by norm_num) z

/-- A conformal map on a connected open plane domain has zero Schwarzian
exactly when it is the restriction of a nondegenerate fractional-linear map.
The representative is proved to have no pole anywhere on that domain. -/
theorem schwarzian_conformal_eq_zero_iff {D V : Set ℂ} {f : ℂ → ℂ}
    (hD : IsOpen D) (hDc : IsConnected D) (hf : LiZhongQC.IsConformalOnto f D V) :
    (∀ z ∈ D, LiZhongQC.schwarzian f z = 0) ↔
      ∃ a b c d : ℂ, a * d - b * c ≠ 0 ∧
        (∀ z ∈ D, c * z + d ≠ 0) ∧
        EqOn f (fun z => (a * z + b) / (c * z + d)) D := by
  constructor
  · intro hzero
    have hid : LiZhongQC.IsConformalOnto (id : ℂ → ℂ) D D :=
      ⟨differentiableOn_id, fun _ _ _ _ h => h, by simp⟩
    obtain ⟨a, b, c, d, hdet, hrep⟩ := LiZhongQC.thm19_1_unique hD hDc
      (LiZhongQC.isLocUnivMero_of_isConformalOnto hD hf)
      (LiZhongQC.isLocUnivMero_of_isConformalOnto hD hid)
      (fun z hz => (hzero z hz).trans (schwarzian_identity z).symm)
    have hformula : ∀ z ∈ D, c * z + d ≠ 0 →
        f z = (a * z + b) / (c * z + d) := by
      intro z hz hden
      exact hrep z hz (hf.1.analyticAt (hD.mem_nhds hz)) analyticAt_id hden
    have hnonpole : ∀ z ∈ D, c * z + d ≠ 0 := by
      intro z hz hpole
      have hc : c ≠ 0 := by
        intro hc0
        have hd : d = 0 := by simpa only [hc0, zero_mul, zero_add] using hpole
        exact hdet (by simp [hc0, hd])
      have hab : a * z + b ≠ 0 := by
        intro hab0
        apply hdet
        linear_combination a * hpole - c * hab0
      have hnear : f =ᶠ[𝓝[≠] z] fun w => (a * w + b) / (c * w + d) := by
        have hDnear : ∀ᶠ w in 𝓝[≠] z, w ∈ D :=
          nhdsWithin_le_nhds (hD.mem_nhds hz)
        filter_upwards [hDnear, self_mem_nhdsWithin] with w hw hwz
        apply hformula w hw
        intro hwden
        apply hwz
        apply sub_eq_zero.mp
        have hmul : c * (w - z) = 0 := by
          linear_combination hwden - hpole
        exact (mul_eq_zero.mp hmul).resolve_left hc
      exact LiZhongQC.not_continuousAt_mobius_pole hc hpole hab hnear
        (hf.1.analyticAt (hD.mem_nhds hz)).continuousAt
    exact ⟨a, b, c, d, hdet, hnonpole, fun z hz => hformula z hz (hnonpole z hz)⟩
  · rintro ⟨a, b, c, d, hdet, _hnonpole, hformula⟩ z hz
    have hnear : f =ᶠ[𝓝[≠] z] fun w => (a * w + b) / (c * w + d) := by
      filter_upwards [nhdsWithin_le_nhds (hD.mem_nhds hz)] with w hw
      exact hformula hw
    exact (LiZhongQC.schwarzian_congr hnear).trans (LiZhongQC.schwarzian_mobius hdet z)

end LowDimensionalTopology.Geometry.Quasiconformal
