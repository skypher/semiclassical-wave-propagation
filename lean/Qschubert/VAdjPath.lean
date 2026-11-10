import Qschubert.VAdj

/-!
# The backward equation along a moving test-function path

For `ħ ≠ 0` and a path `G : ℝ → testFn` whose `L²` image is differentiable at `t` with derivative
`g'`: `d/ds [V(s)* G(s)]|_{s=t} = V(t)* g' - (iħ/2) V(t)* Δ(t) G(t)` (`hasDerivAt_dispVadj_path`).
The proof splits the difference quotient into the moving-input part `V(t+h)*((G(t+h) - G(t))/h)`
(joint strong continuity, `tendsto_dispVadj`) and the fixed-input part (`hasDerivAt_dispVadj`).
The integrated form (`dispVadj_path_sub_eq_integral`):
`V(t)* G(t) - G(0) = ∫₀ᵗ V(s)* (G'(s) - (iħ/2) Δ(s) G(s)) ds`, for paths with a continuous
derivative and `s ↦ Δ(s)G(s)` continuous.

This is the product rule R60 asked for. Step 3 of Theorem 1.3R applies it to `G(s) = V_ε(s)w`
with `G' = (iħ/2) Δ_ε(s) G`, giving
`V(t)* V_ε(t) w - w = -(iħ/2) ∫₀ᵗ V(s)* (Δ(s) - Δ_ε(s)) V_ε(s) w ds`; that path is not
test-valued, so its use there still needs the domain extension (open).
-/

namespace Qschubert

open MeasureTheory UpperHalfPlane Filter Topology

local notation "L2H" => Lp ℂ 2 (volume : Measure ℍ)

lemma dispVadj_sub (hb s : ℝ) (x y : L2H) :
    dispVadj hb s (x - y) = dispVadj hb s x - dispVadj hb s y := by
  simp only [dispVadj, map_sub, smul_sub]

lemma dispVadj_real_smul (hb s r : ℝ) (x : L2H) : dispVadj hb s (r • x) = r • dispVadj hb s x := by
  have h : r • x = (r : ℂ) • x := (RCLike.real_smul_eq_coe_smul (K := ℂ) r x)
  have h' : r • dispVadj hb s x = (r : ℂ) • dispVadj hb s x := RCLike.real_smul_eq_coe_smul (K := ℂ) r _
  rw [h, h']
  simp only [dispVadj, map_smul]
  exact smul_comm _ _ _

/-- **The product rule along a moving test-function path.** -/
theorem hasDerivAt_dispVadj_path {hb : ℝ} (hb0 : hb ≠ 0) (G : ℝ → testFn) {g' : L2H} {t : ℝ}
    (hG : HasDerivAt (fun s => toL2 (G s)) g' t) :
    HasDerivAt (fun s => dispVadj hb s (toL2 (G s)))
      (dispVadj hb t g' - (Complex.I * (hb : ℂ) / 2) • dispVadj hb t (lapTL2 t (G t))) t := by
  rw [hasDerivAt_iff_tendsto_slope_zero] at hG ⊢
  have h1 : Tendsto (fun h : ℝ => dispVadj hb (t + h) (h⁻¹ • (toL2 (G (t + h)) - toL2 (G t))))
      (𝓝[≠] 0) (𝓝 (dispVadj hb t g')) := by
    have hφ : Tendsto (fun h : ℝ => t + h) (𝓝[≠] 0) (𝓝 t) := by
      have : Tendsto (fun h : ℝ => t + h) (𝓝 0) (𝓝 (t + 0)) := (continuous_const.add continuous_id).tendsto 0
      rw [add_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    exact tendsto_dispVadj hφ hG
  have h2 := (hasDerivAt_iff_tendsto_slope_zero.1 (hasDerivAt_dispVadj hb0 (G t) t))
  have hsum := h1.add h2
  have e : ∀ h : ℝ, h⁻¹ • (dispVadj hb (t + h) (toL2 (G (t + h))) - dispVadj hb t (toL2 (G t)))
      = dispVadj hb (t + h) (h⁻¹ • (toL2 (G (t + h)) - toL2 (G t)))
        + h⁻¹ • (dispVadj hb (t + h) (toL2 (G t)) - dispVadj hb t (toL2 (G t))) := by
    intro h
    rw [dispVadj_real_smul, dispVadj_sub, ← smul_add]
    congr 1
    abel
  simp_rw [e]
  convert hsum using 2
  rw [sub_eq_add_neg, _root_.neg_smul]

/-- **The integrated form**: `V(t)* G(t) - G(0) = ∫₀ᵗ V(s)* (G'(s) - (iħ/2) Δ(s) G(s)) ds`. -/
theorem dispVadj_path_sub_eq_integral {hb : ℝ} (hb0 : hb ≠ 0) (G : ℝ → testFn) (G' : ℝ → L2H)
    (hG : ∀ s, HasDerivAt (fun r => toL2 (G r)) (G' s) s) (hG'c : Continuous G')
    (hΔc : Continuous fun s => lapTL2 s (G s)) (t : ℝ) :
    dispVadj hb t (toL2 (G t)) - toL2 (G 0)
      = ∫ s in (0 : ℝ)..t, (dispVadj hb s (G' s)
          - (Complex.I * (hb : ℂ) / 2) • dispVadj hb s (lapTL2 s (G s))) := by
  have hcont : Continuous fun s => dispVadj hb s (G' s)
      - (Complex.I * (hb : ℂ) / 2) • dispVadj hb s (lapTL2 s (G s)) := by
    have c1 : Continuous fun s => dispVadj hb s (G' s) := continuous_iff_continuousAt.2 fun s =>
      tendsto_dispVadj (continuous_id.tendsto s) (hG'c.tendsto s)
    have c2 : Continuous fun s => dispVadj hb s (lapTL2 s (G s)) := continuous_iff_continuousAt.2 fun s =>
      tendsto_dispVadj (continuous_id.tendsto s) (hΔc.tendsto s)
    exact c1.sub (c2.const_smul (Complex.I * (hb : ℂ) / 2))
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hasDerivAt_dispVadj_path hb0 G (hG s))
    (hcont.intervalIntegrable 0 t), dispVadj_zero]

end Qschubert
