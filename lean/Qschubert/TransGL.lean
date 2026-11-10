import Qschubert.SpecCommute
import Qschubert.PoincareP1
import Qschubert.FC0

/-!
# Horizontal translations and `e^{-αΛ}`

Stage X of the plan for Proposition `ev:mod` (`lean/BLUEPRINT.md`). `transGL s = [[1, s], [0, 1]]` acts on `ℍ` by
`z ↦ z + s` (`coe_transGL_smul`), and `e^{-αΛ}` commutes with it (`expCut_J_glU`: the symbol `e^{-α√|s|}` of
`expCut α` is continuous and vanishes at infinity, so `fc_glU` applies).
-/

namespace Qschubert

open MeasureTheory Filter Topology UpperHalfPlane Physicslib4.Spectral Physicslib4.Spectral.Unbounded
open scoped MatrixGroups

local notation "L2H" => Lp ℂ 2 (volume : Measure ℍ)

/-- `[[1, s], [0, 1]]`. -/
noncomputable def transGL (s : ℝ) : GL (Fin 2) ℝ := toPointGL ⟨⟨s, 1⟩, one_pos⟩

/-- `[[1, s], [0, 1]] • z = z + s`. -/
lemma coe_transGL_smul (s : ℝ) (z : ℍ) : ((transGL s • z : ℍ) : ℂ) = (z : ℂ) + s := by
  have hdet : ((transGL s).det : ℝ) = 1 := toPointGL_det _
  rw [coe_smul_of_det_pos (by rw [hdet]; exact one_pos)]
  have h00 : ((transGL s : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 0 = 1 := rfl
  have h01 : ((transGL s : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 1 = s := rfl
  have h10 : ((transGL s : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 1 0 = 0 := rfl
  have h11 : ((transGL s : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 1 1 = 1 := rfl
  simp only [num, denom, h00, h01, h10, h11]
  simp

lemma continuous_expCut_g {α : ℝ} (hα : 0 < α) : Continuous (expCut α hα).g := by
  unfold Cutoff.g expCut
  fun_prop

lemma tendsto_expCut_g {α : ℝ} (hα : 0 < α) : Tendsto (expCut α hα).g (cocompact ℝ) (𝓝 0) := by
  have h1 : Tendsto (fun s : ℝ => α * Real.sqrt |s|) (cocompact ℝ) atTop := by
    have h2 : Tendsto (fun s : ℝ => |s|) (cocompact ℝ) atTop := tendsto_norm_cocompact_atTop (E := ℝ)
    exact (Real.tendsto_sqrt_atTop.comp h2).const_mul_atTop hα
  have h3 : Tendsto (fun s : ℝ => Real.exp (-(α * Real.sqrt |s|))) (cocompact ℝ) (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp h1
  have h4 : Tendsto (fun s : ℝ => ((Real.exp (-(α * Real.sqrt |s|)) : ℝ) : ℂ)) (cocompact ℝ) (𝓝 0) := by
    have h5 := (Complex.continuous_ofReal.tendsto 0).comp h3
    rwa [Complex.ofReal_zero] at h5
  exact h4

/-- **`e^{-αΛ}` commutes with the isometries of `ℍ`.** -/
theorem expCut_J_glU {α : ℝ} (hα : 0 < α) (g : GL (Fin 2) ℝ) (η : L2H) :
    (expCut α hα).J (glU g η) = glU g ((expCut α hα).J η) :=
  fc_glU (continuous_expCut_g hα) (tendsto_expCut_g hα) g η

end Qschubert
