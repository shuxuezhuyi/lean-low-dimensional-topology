module
public import LowDimensionalTopology.Geometry.Hyperbolic.ModelMaps.CayleyHalfPlaneDisk
public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
@[expose] public section
noncomputable section
open Set Topology
open scoped UpperHalfPlane
namespace LowDimensionalTopology.Geometry.Hyperbolic

/-- A genuine global plane coordinate on the native hyperbolic half-plane. -/
def nativeLogPlaneHomeomorph : ℍ≃ₜℂ where
  toFun z:=⟨z.re,Real.log z.im⟩
  invFun w:=⟨⟨w.re,Real.exp w.im⟩,Real.exp_pos _⟩
  left_inv z:=by
    apply UpperHalfPlane.ext
    apply Complex.ext
    · rfl
    · exact Real.exp_log z.im_pos
  right_inv w:=by
    apply Complex.ext
    · rfl
    · exact Real.log_exp w.im
  continuous_toFun:=by
    exact Complex.equivRealProdCLM.symm.continuous.comp
      (UpperHalfPlane.continuous_re.prodMk
        (UpperHalfPlane.continuous_im.log (fun z=>z.im_ne_zero)))
  continuous_invFun:=by
    apply UpperHalfPlane.isEmbedding_coe.continuous_iff.mpr
    exact Complex.equivRealProdCLM.symm.continuous.comp
      (Complex.continuous_re.prodMk (Real.continuous_exp.comp Complex.continuous_im))

/-- Removing any countable actual set of native points leaves a path-connected plane. -/
theorem nativeHalfPlane_countable_complement_pathConnected {V : Set ℍ} (hV : V.Countable) :
    IsPathConnected Vᶜ := by
  have hc:=(hV.image nativeLogPlaneHomeomorph).isPathConnected_compl_of_one_lt_rank
    (by simp [Complex.rank_real_complex])
  have hh:=nativeLogPlaneHomeomorph.isPathConnected_preimage.mpr hc
  simpa only [preimage_compl,preimage_image_eq _ nativeLogPlaneHomeomorph.injective] using hh

end LowDimensionalTopology.Geometry.Hyperbolic
