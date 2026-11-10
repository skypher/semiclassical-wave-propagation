import Mathlib.Analysis.Complex.UpperHalfPlane.Measure
import Mathlib.Analysis.Complex.UpperHalfPlane.Metric
import Qschubert.OrbitCount

/-!
# The unfolding step of Lemma G4.3 on the upper half-plane

Instances for a subgroup `Γ ≤ SL(2, ℝ)` acting on `ℍ` (Mathlib's model, with the hyperbolic
metric and the invariant measure `dx dy / y²`), and Lemma G4.3, Step 2, for such `Γ`.

Scope of this file: a subgroup of `SL(2, ℝ)` that has a fundamental domain in Mathlib's sense
(translates a.e. disjoint) cannot contain `-1`, since `-1` acts trivially. So
`fuchsian_setLIntegral_ball_le` covers exactly the Fuchsian groups that lift isomorphically to a
subgroup of `SL(2, ℝ)`. A group with an elliptic element of even order does not (the lifts of
such an element have `-1` among their powers). The abstract `setLIntegral_ball_le_orbitMult_mul`
applies to every Fuchsian group through a `PSL(2, ℝ)` action on `ℍ` with isometry and
measure-invariance instances.
-/

namespace Qschubert

open MeasureTheory Metric UpperHalfPlane
open scoped MatrixGroups ENNReal

/-- `SL(2, ℝ)` preserves the hyperbolic measure on `ℍ` (it acts through `GL(2, ℝ)`). -/
instance : SMulInvariantMeasure SL(2, ℝ) ℍ volume :=
  ⟨fun g _ hs => SMulInvariantMeasure.measure_preimage_smul (μ := (volume : Measure ℍ))
    (Matrix.SpecialLinearGroup.mapGL ℝ g) hs⟩

instance (Γ : Subgroup SL(2, ℝ)) : SMulInvariantMeasure Γ ℍ volume :=
  ⟨fun γ _ hs => SMulInvariantMeasure.measure_preimage_smul (μ := (volume : Measure ℍ))
    (γ : SL(2, ℝ)) hs⟩

instance (Γ : Subgroup SL(2, ℝ)) : IsIsometricSMul Γ ℍ :=
  ⟨fun γ => isometry_smul ℍ (γ : SL(2, ℝ))⟩

/-- Lemma G4.3, Step 2, on `ℍ`: for a countable `Γ ≤ SL(2, ℝ)` with fundamental domain `F` and a
`Γ`-invariant measurable `f ≥ 0`, `∫_{B(z,1)} f dν ≤ m(z) ∫_F f dν`, where
`m(z) = #{γ ∈ Γ : d(z, γ z) < 2}` and `ν = dx dy / y²`. -/
theorem fuchsian_setLIntegral_ball_le (Γ : Subgroup SL(2, ℝ)) [Countable Γ] {F : Set ℍ}
    (hF : IsFundamentalDomain Γ F volume) {f : ℍ → ℝ≥0∞} (hf : Measurable f)
    (hinv : ∀ (γ : Γ) (z : ℍ), f (γ • z) = f z) (z : ℍ) :
    ∫⁻ x in ball z 1, f x ≤ (orbitMult Γ z : ℝ≥0∞) * ∫⁻ x in F, f x :=
  setLIntegral_ball_le_orbitMult_mul hF hf hinv z

end Qschubert
