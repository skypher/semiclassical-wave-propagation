import Mathlib.MeasureTheory.Group.FundamentalDomain
import Mathlib.Topology.MetricSpace.IsometricSMul
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Data.Set.Card

/-!
# The unfolding step of Lemma G4.3

Manuscript `paper/sec_printed.tex`, the local Sobolev inequality on a Fuchsian
quotient (Lemma G4.3), Step 2.

* `encard_ball_le_orbitMult`: for a group `Γ` acting isometrically on a pseudo-metric space and
  points `z, w`, the number of `γ` with `γ • w ∈ B(z, 1)` is at most
  `m(z) = #{γ : d(z, γ • z) < 2}`.
* `setLIntegral_ball_le_orbitMult_mul`: for a countable `Γ`, an invariant measure, a fundamental
  domain `F` and a `Γ`-invariant measurable `f ≥ 0`,
  `∫_{B(z,1)} f ≤ m(z) ∫_F f`. With `f = |ũ|²` for the lift `ũ` of `u ∈ L²(Γ\ℍ)` this is
  `∫_{B(z̃,1)} |ũ|² ≤ m(z) ‖u‖²_{L²(M)}`.

The manuscript uses this with `Γ` Fuchsian acting on `ℍ`; nothing here needs discreteness,
torsion-freeness or an injectivity-radius bound.
-/

namespace Qschubert

open Metric MeasureTheory
open scoped ENNReal Pointwise

variable {Γ X : Type*} [Group Γ] [PseudoMetricSpace X] [MulAction Γ X] [IsIsometricSMul Γ X]

variable (Γ) in
/-- `m(z) := #{γ ∈ Γ : d(z, γ z) < 2}`, as an element of `ℕ∞`. -/
noncomputable def orbitMult (z : X) : ℕ∞ := {γ : Γ | dist z (γ • z) < 2}.encard

/-- Step 2 of Lemma G4.3: `n(w) := #{γ : γ • w ∈ B(z, 1)} ≤ m(z)`. -/
theorem encard_ball_le_orbitMult (z w : X) :
    {γ : Γ | dist (γ • w) z < 1}.encard ≤ orbitMult Γ z := by
  by_cases h : ∃ γ₀ : Γ, dist (γ₀ • w) z < 1
  · obtain ⟨γ₀, h₀⟩ := h
    refine Set.encard_le_encard_of_injOn (f := fun γ => γ * γ₀⁻¹) ?_ ?_
    · intro γ hγ
      simp only [Set.mem_ofPred_eq] at hγ ⊢
      have e : dist (γ • w) ((γ * γ₀⁻¹) • z) = dist (γ₀ • w) z := by
        rw [mul_smul, dist_smul, ← dist_smul γ₀, smul_inv_smul]
      calc dist z ((γ * γ₀⁻¹) • z) ≤ dist z (γ • w) + dist (γ • w) ((γ * γ₀⁻¹) • z) :=
            dist_triangle _ _ _
        _ = dist (γ • w) z + dist (γ₀ • w) z := by rw [dist_comm z, e]
        _ < 1 + 1 := add_lt_add hγ h₀
        _ = 2 := by norm_num
    · intro a _ b _ hab
      simpa using hab
  · push Not at h
    have : {γ : Γ | dist (γ • w) z < 1} = ∅ := by
      ext γ; simp [not_lt.mpr (h γ)]
    simp [this]

/-- Pointwise count: `∑_γ 1_{γ • B(z,1)}(x) · c ≤ m(z) · c`. -/
lemma tsum_indicator_smul_ball_le (z x : X) (c : ℝ≥0∞) :
    ∑' γ : Γ, (γ • ball z 1).indicator (fun _ => c) x ≤ (orbitMult Γ z : ℝ≥0∞) * c := by
  classical
  have h1 : ∀ γ : Γ, (γ • ball z 1).indicator (fun _ => c) x
      = {γ : Γ | dist (γ • x) z < 1}.indicator (fun _ => c) γ⁻¹ := by
    intro γ
    have hm : x ∈ γ • ball z 1 ↔ dist (γ⁻¹ • x) z < 1 := by
      rw [Set.mem_smul_set_iff_inv_smul_mem, mem_ball]
    simp only [Set.indicator_apply, Set.mem_ofPred_eq, hm]
  simp_rw [h1]
  have h2 := (Equiv.inv Γ).tsum_eq (fun γ => {γ : Γ | dist (γ • x) z < 1}.indicator (fun _ => c) γ)
  simp only [Equiv.inv_apply] at h2
  rw [h2, ← tsum_subtype, ENNReal.tsum_set_const]
  gcongr
  exact encard_ball_le_orbitMult z x

/-- Step 2 of Lemma G4.3, integrated: `∫_{B(z,1)} f ≤ m(z) ∫_F f` for `Γ`-invariant `f ≥ 0` and a
fundamental domain `F` of a countable group acting isometrically and preserving `μ`. -/
theorem setLIntegral_ball_le_orbitMult_mul [MeasurableSpace X] [OpensMeasurableSpace X]
    [Countable Γ] [MeasurableConstSMul Γ X] {μ : Measure X} [SMulInvariantMeasure Γ X μ]
    {F : Set X} (hF : IsFundamentalDomain Γ F μ) {f : X → ℝ≥0∞} (hf : Measurable f)
    (hinv : ∀ (γ : Γ) (x : X), f (γ • x) = f x) (z : X) :
    ∫⁻ x in ball z 1, f x ∂μ ≤ (orbitMult Γ z : ℝ≥0∞) * ∫⁻ x in F, f x ∂μ := by
  classical
  have hmeas : ∀ γ : Γ, MeasurableSet (γ • ball z 1) := fun γ => by
    rw [Metric.smul_ball]; exact isOpen_ball.measurableSet
  have hterm : ∀ γ : Γ, ∫⁻ x in γ • ball z 1 ∩ F, f (γ⁻¹ • x) ∂μ
      = ∫⁻ x in F, (γ • ball z 1).indicator f x ∂μ := by
    intro γ
    rw [lintegral_indicator (hmeas γ), Measure.restrict_restrict (hmeas γ)]
    simp only [hinv]
  rw [hF.setLIntegral_eq_tsum' f (ball z 1)]
  simp_rw [hterm]
  rw [← lintegral_tsum (fun γ => (hf.indicator (hmeas γ)).aemeasurable),
    ← lintegral_const_mul _ hf]
  refine lintegral_mono fun x => ?_
  calc ∑' γ : Γ, (γ • ball z 1).indicator f x
      = ∑' γ : Γ, (γ • ball z 1).indicator (fun _ => f x) x := by
        refine tsum_congr fun γ => ?_
        rw [Set.indicator_apply, Set.indicator_apply]
    _ ≤ (orbitMult Γ z : ℝ≥0∞) * f x := tsum_indicator_smul_ball_le z x (f x)

end Qschubert
