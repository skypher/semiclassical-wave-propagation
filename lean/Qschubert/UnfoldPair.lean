import Qschubert.Periodize
import Qschubert.FundDomain

/-!
# Unfolding a pairing with a periodization

Stage E of the plan for Proposition `ev:mod` (`lean/BLUEPRINT.md`), part E4. For a Fuchsian group `Γ`, a function `w`
on `M = Γ\ℍ` and a function `u` on `ℍ` with `(w ∘ π) u` integrable on `ℍ`:

`∫_ℍ w(π z) u(z) dν = ∫_M w · u_Γ dμ` (`integral_lift_mul_eq`),

where `u_Γ = perio Γ u`. Used twice for the pairing of a periodization with an incomplete Eisenstein series.
-/

namespace Qschubert

open MeasureTheory UpperHalfPlane
open scoped MatrixGroups

variable (Γ : Subgroup PGL(2, ℝ)) [ProperlyDiscontinuousSMul Γ ℍ]

omit [ProperlyDiscontinuousSMul Γ ℍ] in
/-- `((w ∘ π) u)_Γ = w · u_Γ`. -/
lemma perio_lift_mul (w : Surf Γ → ℂ) (u : ℍ → ℂ) :
    perio Γ (fun z => w (surfMk Γ z) * u z) = fun x => w x * perio Γ u x := by
  have h := MulAction.automorphize_smul_left (α := Γ) (β := ℍ) u w
  exact h

/-- **Unfolding a pairing.** -/
theorem integral_lift_mul_eq {w : Surf Γ → ℂ} {u : ℍ → ℂ}
    (hint : Integrable fun z : ℍ => w (surfMk Γ z) * u z)
    (hm : AEStronglyMeasurable (fun x : Surf Γ => w x * perio Γ u x) (surfMeasure Γ)) :
    ∫ z : ℍ, w (surfMk Γ z) * u z = ∫ x, w x * perio Γ u x ∂surfMeasure Γ := by
  have := countable_of_properlyDiscontinuous Γ
  have hF := isFundamentalDomain_fdSet Γ
  have h := integral_eq_integral_automorphize Γ hF hint (by
    have e : (MulAction.automorphize (fun z : ℍ => w (surfMk Γ z) * u z) : Surf Γ → ℂ)
        = fun x => w x * perio Γ u x := perio_lift_mul Γ w u
    rw [e]
    exact hm)
  rw [h]
  congr 1
  exact perio_lift_mul Γ w u

end Qschubert
