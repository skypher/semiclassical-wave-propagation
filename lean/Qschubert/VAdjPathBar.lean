import Qschubert.CoreDom
import Qschubert.VAdjPath

/-!
# The backward equation along graph-closure paths

* `hasDerivAt_dispVadj_bar` (fixed input in `graphBar`): `d/dt V(t)* p.1 = -(iħ/2) V(t)* Δ(t) p`,
  `Δ(t)p := lapTbar t p`, from the integrated identity `dispVadj_sub_eq_integral_bar` (continuous
  integrand, fundamental theorem of calculus).
* `hasDerivAt_dispVadj_path_bar` (moving input): for `P : ℝ → graphBar` whose first component has
  `L²` derivative `g'` at `t`: `d/ds [V(s)* P(s).1]|_{s=t} = V(t)* g' - (iħ/2) V(t)* Δ(t) P(t)`.
  Same split as `hasDerivAt_dispVadj_path`: moving-input part by joint strong continuity, fixed-input
  part by `hasDerivAt_dispVadj_bar`.
* `dispVadj_path_bar_sub_eq_integral` (integrated form): for `P` with first-component derivative
  `G'` continuous and `P` continuous into `graphBar`,
  `V(t)* P(t).1 - P(0).1 = ∫₀ᵗ V(s)* (G'(s) - (iħ/2) Δ(s) P(s)) ds`.

With `negLap_closure_eq_negLapH`, every path in the Friedrichs domain that is continuous in the
graph norm is such a `P`.
-/

namespace Qschubert

open MeasureTheory UpperHalfPlane Filter Topology

local notation "L2H" => Lp ℂ 2 (volume : Measure ℍ)

lemma continuous_dispVadj_lapTbar (hb : ℝ) (p : graphBar) :
    Continuous fun s => dispVadj hb s (lapTbar s p) :=
  continuous_iff_continuousAt.2 fun s =>
    tendsto_dispVadj (continuous_id.tendsto s)
      ((continuous_lapTbar_uncurry.comp (continuous_const.prodMk continuous_id)).tendsto s)

/-- **Fixed graph input**: `d/dt V(t)* p.1 = -(iħ/2) V(t)* Δ(t) p`. -/
theorem hasDerivAt_dispVadj_bar {hb : ℝ} (hb0 : hb ≠ 0) (p : graphBar) (t : ℝ) :
    HasDerivAt (fun s => dispVadj hb s (p : L2H × L2H).1)
      (-(Complex.I * (hb : ℂ) / 2) • dispVadj hb t (lapTbar t p)) t := by
  have hI : HasDerivAt (fun u => ∫ s in (0 : ℝ)..u, dispVadj hb s (lapTbar s p))
      (dispVadj hb t (lapTbar t p)) t :=
    intervalIntegral.integral_hasDerivAt_right
      ((continuous_dispVadj_lapTbar hb p).intervalIntegrable 0 t)
      ((continuous_dispVadj_lapTbar hb p).stronglyMeasurableAtFilter _ _)
      ((continuous_dispVadj_lapTbar hb p).continuousAt)
  have e : (fun s => dispVadj hb s (p : L2H × L2H).1)
      = fun s => (p : L2H × L2H).1
        + -(Complex.I * (hb : ℂ) / 2) • ∫ r in (0 : ℝ)..s, dispVadj hb r (lapTbar r p) := by
    funext s
    rw [← dispVadj_sub_eq_integral_bar hb0 s p]; abel
  rw [e]
  exact (hI.const_smul (-(Complex.I * (hb : ℂ) / 2))).const_add _

/-- **The product rule along a graph-closure path.** -/
theorem hasDerivAt_dispVadj_path_bar {hb : ℝ} (hb0 : hb ≠ 0) (P : ℝ → graphBar) {g' : L2H} {t : ℝ}
    (hP : HasDerivAt (fun s => (P s : L2H × L2H).1) g' t) :
    HasDerivAt (fun s => dispVadj hb s (P s : L2H × L2H).1)
      (dispVadj hb t g' - (Complex.I * (hb : ℂ) / 2) • dispVadj hb t (lapTbar t (P t))) t := by
  rw [hasDerivAt_iff_tendsto_slope_zero] at hP ⊢
  have h1 : Tendsto (fun h : ℝ => dispVadj hb (t + h) (h⁻¹ • ((P (t + h) : L2H × L2H).1
      - (P t : L2H × L2H).1))) (𝓝[≠] 0) (𝓝 (dispVadj hb t g')) := by
    have hφ : Tendsto (fun h : ℝ => t + h) (𝓝[≠] 0) (𝓝 t) := by
      have : Tendsto (fun h : ℝ => t + h) (𝓝 0) (𝓝 (t + 0)) :=
        (continuous_const.add continuous_id).tendsto 0
      rw [add_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    exact tendsto_dispVadj hφ hP
  have h2 := hasDerivAt_iff_tendsto_slope_zero.1 (hasDerivAt_dispVadj_bar hb0 (P t) t)
  have hsum := h1.add h2
  have e : ∀ h : ℝ, h⁻¹ • (dispVadj hb (t + h) (P (t + h) : L2H × L2H).1
      - dispVadj hb t (P t : L2H × L2H).1)
      = dispVadj hb (t + h) (h⁻¹ • ((P (t + h) : L2H × L2H).1 - (P t : L2H × L2H).1))
        + h⁻¹ • (dispVadj hb (t + h) (P t : L2H × L2H).1 - dispVadj hb t (P t : L2H × L2H).1) := by
    intro h
    rw [dispVadj_real_smul, dispVadj_sub, ← smul_add]
    congr 1
    abel
  simp_rw [e]
  convert hsum using 2
  rw [sub_eq_add_neg, ← _root_.neg_smul]

/-- **The integrated form along a graph-closure path.** -/
theorem dispVadj_path_bar_sub_eq_integral {hb : ℝ} (hb0 : hb ≠ 0) (P : ℝ → graphBar) (G' : ℝ → L2H)
    (hP : ∀ s, HasDerivAt (fun r => (P r : L2H × L2H).1) (G' s) s) (hG'c : Continuous G')
    (hPc : Continuous P) (t : ℝ) :
    dispVadj hb t (P t : L2H × L2H).1 - (P 0 : L2H × L2H).1
      = ∫ s in (0 : ℝ)..t, (dispVadj hb s (G' s)
          - (Complex.I * (hb : ℂ) / 2) • dispVadj hb s (lapTbar s (P s))) := by
  have hΔc : Continuous fun s => lapTbar s (P s) :=
    continuous_lapTbar_uncurry.comp (hPc.prodMk continuous_id)
  have hcont : Continuous fun s => dispVadj hb s (G' s)
      - (Complex.I * (hb : ℂ) / 2) • dispVadj hb s (lapTbar s (P s)) := by
    have c1 : Continuous fun s => dispVadj hb s (G' s) := continuous_iff_continuousAt.2 fun s =>
      tendsto_dispVadj (continuous_id.tendsto s) (hG'c.tendsto s)
    have c2 : Continuous fun s => dispVadj hb s (lapTbar s (P s)) :=
      continuous_iff_continuousAt.2 fun s =>
        tendsto_dispVadj (continuous_id.tendsto s) (hΔc.tendsto s)
    exact c1.sub (c2.const_smul (Complex.I * (hb : ℂ) / 2))
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s _ => hasDerivAt_dispVadj_path_bar hb0 P (hP s)) (hcont.intervalIntegrable 0 t),
    dispVadj_zero]

end Qschubert
