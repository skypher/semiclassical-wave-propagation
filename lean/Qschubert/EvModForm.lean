import Qschubert.Setting

/-!
# The explicit form of the leading approximation for `b = ∞`

Stage E of the plan for Proposition `ev:mod` (`lean/BLUEPRINT.md`), part E5 (preparation). For `g = 1` and `K = 0`:

`u^{(0)}(t)[a](z) = e^{-it/(2ħ)} · e^{-t/2} a(x + i e^t y) · y^{-i/ħ}` (`approxSolB_one_zero`),

and the initial state is `a(z) y^{-i/ħ}` (`initState_one`).
-/

namespace Qschubert

open UpperHalfPlane
open scoped MatrixGroups

lemma approxSolB_one_zero (ħ t : ℝ) (a : ℍ → ℂ) (z : ℍ) :
    approxSolB 1 0 ħ t a z
      = Complex.exp (-(Complex.I * (t : ℂ) / (2 * (ħ : ℂ)))) * ((Real.exp (-t / 2) : ℂ) * a (dilate t z))
        * Complex.exp (Complex.I * ((-Real.log z.im : ℝ) : ℂ) / (ħ : ℂ)) := by
  simp [approxSolB, approxSol, transportS, approxAmp, dysonP, phaseInf]

lemma initState_one (ħ : ℝ) (a : ℍ → ℂ) (z : ℍ) :
    initState 1 ħ a z = a z * Complex.exp (Complex.I * ((-Real.log z.im : ℝ) : ℂ) / (ħ : ℂ)) := by
  simp [initState, phaseB, phaseInf]

end Qschubert
