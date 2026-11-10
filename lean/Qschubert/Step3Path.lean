import Qschubert.VAdjPathBar
import Qschubert.EpsDomain

/-!
# Step 3 of Theorem 1.3R: the Duhamel identity for `V(t)* V_ε(t) w`

For a cutoff with `s² r(s)` bounded (`hS2`), `a ∈ Dom(-Δ)` and `t₀ ∈ ℝ`, the mollified path
`G(s) = V_ε(s) V_ε(t₀)* a` (`pathEps`) has `G(t₀) = a`, `G' = (iħ/2) Δ_ε(s) G`, and

  `G(s) - a = (J + JS) ∫_{t₀}^s (iħ/2) L_ε(r) G(r) dr`  (`pathEps_sub`),

so `G(s) ∈ Dom(-Δ)` (`pathEps_mem`) with `-Δ G(s) = -Δ a + (JS + JSS)(…)` continuous in `s`
(`continuous_negLapH_pathEps`). Hence `s ↦ (G(s), -ΔG(s))` is a continuous path in `graph(Ā)`
(`pathBar`, by `mem_graphBar_negLapH`), and the graph-path rule gives

  `V(t)* G(t) - G(0) = -(iħ/2) ∫₀ᵗ V(s)* (Δ(s) - Δ_ε(s)) G(s) ds`  (`step3_duhamel`),

with `Δ(s)G(s) := lapTbar s (G(s), -ΔG(s))`. At `t₀ = t`, `G(t) = a` and `G(0) = w = V_ε(t)* a`
(`step3_duhamel_paper`): `V(t)* V_ε(t) w - w = -(iħ/2) ∫₀ᵗ V(s)* (Δ(s) - Δ_ε(s)) V_ε(s) w ds`,
the identity of paper Step 3 (Schubert (5.6)-(5.10)), for every `a ∈ Dom(-Δ)`.
-/

namespace Qschubert

open MeasureTheory UpperHalfPlane Filter Topology Physicslib4.Spectral Physicslib4.Spectral.Unbounded

local notation "L2H" => Lp ℂ 2 (volume : Measure ℍ)

namespace Cutoff

variable {χ : Cutoff}

/-- The Step 3 path `G(s) = V_ε(s) V_ε(t₀)* a`. -/
noncomputable def pathEps (χ : Cutoff) (hb t₀ : ℝ) (a : L2H) (s : ℝ) : L2H :=
  χ.flowEps hb s (ContinuousLinearMap.adjoint (χ.flowEps hb t₀) a)

lemma pathEps_self (hb t₀ : ℝ) (a : L2H) : pathEps χ hb t₀ a t₀ = a := by
  rw [pathEps, ← ContinuousLinearMap.mul_apply, (χ.flowEps_unitary hb t₀).2]
  rfl

lemma pathEps_zero (hb t₀ : ℝ) (a : L2H) :
    pathEps χ hb t₀ a 0 = ContinuousLinearMap.adjoint (χ.flowEps hb t₀) a := by
  rw [pathEps, χ.flowEps_zero]; rfl

lemma hasDerivAt_pathEps (hb t₀ : ℝ) (a : L2H) (s : ℝ) :
    HasDerivAt (pathEps χ hb t₀ a) (χ.genEps hb s (pathEps χ hb t₀ a s)) s := by
  have h := ((ContinuousLinearMap.apply ℂ L2H (ContinuousLinearMap.adjoint (χ.flowEps hb t₀) a)).restrictScalars
    ℝ).hasFDerivAt.comp_hasDerivAt s (χ.hasDerivAt_flowEps hb s)
  refine h.congr_deriv ?_
  simp [pathEps]

lemma continuous_pathEps (hb t₀ : ℝ) (a : L2H) : Continuous (pathEps χ hb t₀ a) :=
  continuous_iff_continuousAt.2 fun s => (hasDerivAt_pathEps hb t₀ a s).continuousAt

lemma continuous_genEps_path (hb t₀ : ℝ) (a : L2H) :
    Continuous fun r => χ.genEps hb r (pathEps χ hb t₀ a r) :=
  (χ.continuous_genEps hb).clm_apply (continuous_pathEps hb t₀ a)

/-- The integrand `(iħ/2) L_ε(r) G(r)`. -/
noncomputable def pathInt (χ : Cutoff) (hb t₀ : ℝ) (a : L2H) (r : ℝ) : L2H :=
  ((Complex.I * (hb : ℂ) / 2) • χ.Leps r) (pathEps χ hb t₀ a r)

lemma continuous_pathInt (hb t₀ : ℝ) (a : L2H) : Continuous (pathInt χ hb t₀ a) :=
  ((χ.continuous_Leps.const_smul (Complex.I * (hb : ℂ) / 2))).clm_apply (continuous_pathEps hb t₀ a)

lemma genEps_eq (hb r : ℝ) (v : L2H) :
    χ.genEps hb r v = (χ.J + χ.JS) (((Complex.I * (hb : ℂ) / 2) • χ.Leps r) v) := by
  rw [genEps, ContinuousLinearMap.smul_apply, χ.lapEps_eq r, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smul_apply, map_smul]

/-- **`G(s) - a = (J + JS) ∫_{t₀}^s (iħ/2) L_ε(r) G(r) dr`.** -/
theorem pathEps_sub (hb t₀ : ℝ) (a : L2H) (s : ℝ) :
    pathEps χ hb t₀ a s - a = (χ.J + χ.JS) (∫ r in t₀..s, pathInt χ hb t₀ a r) := by
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun r _ => hasDerivAt_pathEps (χ := χ) hb t₀ a r)
    ((continuous_genEps_path (χ := χ) hb t₀ a).intervalIntegrable t₀ s)
  rw [pathEps_self] at hFTC
  rw [← hFTC, ← ContinuousLinearMap.intervalIntegral_comp_comm _
    ((continuous_pathInt (χ := χ) hb t₀ a).intervalIntegrable t₀ s)]
  congr 1; funext r
  rw [genEps_eq]; rfl

variable (hS2 : χ.gSS ∈ BddMeasurable ℝ)
include hS2

lemma pathEps_eq (hb t₀ : ℝ) (a : L2H) (s : ℝ) :
    pathEps χ hb t₀ a s = a + (χ.J + χ.JS) (∫ r in t₀..s, pathInt χ hb t₀ a r) := by
  rw [← pathEps_sub hb t₀ a s]; abel

lemma pathEps_mem (hb t₀ : ℝ) (a : negLapH.domain) (s : ℝ) :
    pathEps χ hb t₀ (a : L2H) s ∈ negLapH.domain := by
  rw [pathEps_eq hS2]
  exact negLapH.domain.add_mem a.2 (add_mem_dom hS2 _)

/-- `-Δ G(s) = -Δ a + (JS + JSS) ∫_{t₀}^s (iħ/2) L_ε G`. -/
theorem negLapH_pathEps (hb t₀ : ℝ) (a : negLapH.domain) (s : ℝ) :
    negLapH ⟨pathEps χ hb t₀ (a : L2H) s, pathEps_mem hS2 hb t₀ a s⟩
      = negLapH a + (χ.JS + χ.JSS) (∫ r in t₀..s, pathInt χ hb t₀ (a : L2H) r) := by
  have e : (⟨pathEps χ hb t₀ (a : L2H) s, pathEps_mem hS2 hb t₀ a s⟩ : negLapH.domain)
      = a + ⟨(χ.J + χ.JS) (∫ r in t₀..s, pathInt χ hb t₀ (a : L2H) r), add_mem_dom hS2 _⟩ :=
    Subtype.ext (pathEps_eq hS2 hb t₀ a s)
  rw [e, LinearPMap.map_add, negLapH_add hS2]

lemma continuous_negLapH_pathEps (hb t₀ : ℝ) (a : negLapH.domain) :
    Continuous fun s => negLapH ⟨pathEps χ hb t₀ (a : L2H) s, pathEps_mem hS2 hb t₀ a s⟩ := by
  simp_rw [negLapH_pathEps hS2]
  exact continuous_const.add ((χ.JS + χ.JSS).continuous.comp
    (intervalIntegral.continuous_primitive
      (fun _ _ => (continuous_pathInt (χ := χ) hb t₀ (a : L2H)).intervalIntegrable _ _) t₀))

/-- The graph path `s ↦ (G(s), -ΔG(s)) ∈ graph(Ā)`. -/
noncomputable def pathBar (hb t₀ : ℝ) (a : negLapH.domain) (s : ℝ) : graphBar :=
  ⟨(pathEps χ hb t₀ (a : L2H) s, negLapH ⟨pathEps χ hb t₀ (a : L2H) s, pathEps_mem hS2 hb t₀ a s⟩),
    mem_graphBar_negLapH ⟨_, pathEps_mem hS2 hb t₀ a s⟩⟩

lemma continuous_pathBar (hb t₀ : ℝ) (a : negLapH.domain) : Continuous (pathBar hS2 hb t₀ a) :=
  ((continuous_pathEps hb t₀ (a : L2H)).prodMk (continuous_negLapH_pathEps hS2 hb t₀ a)).subtype_mk _

/-- **Step 3**: `V(t)* G(t) - G(0) = -(iħ/2) ∫₀ᵗ V(s)* (Δ(s) - Δ_ε(s)) G(s) ds`. -/
theorem step3_duhamel {hb : ℝ} (hb0 : hb ≠ 0) (t₀ : ℝ) (a : negLapH.domain) (t : ℝ) :
    dispVadj hb t (pathEps χ hb t₀ (a : L2H) t) - pathEps χ hb t₀ (a : L2H) 0
      = -(Complex.I * (hb : ℂ) / 2) • ∫ s in (0 : ℝ)..t,
          dispVadj hb s (lapTbar s (pathBar hS2 hb t₀ a s) - χ.lapEps s (pathEps χ hb t₀ (a : L2H) s)) := by
  have h := dispVadj_path_bar_sub_eq_integral hb0 (pathBar hS2 hb t₀ a)
    (fun s => χ.genEps hb s (pathEps χ hb t₀ (a : L2H) s))
    (fun s => hasDerivAt_pathEps hb t₀ (a : L2H) s) (continuous_genEps_path hb t₀ (a : L2H))
    (continuous_pathBar hS2 hb t₀ a) t
  change dispVadj hb t (pathEps χ hb t₀ (a : L2H) t) - pathEps χ hb t₀ (a : L2H) 0 = _ at h
  rw [h, ← intervalIntegral.integral_smul]
  congr 1; funext s
  have hlin : ∀ (c : ℂ) (x : L2H), dispVadj hb s (c • x) = c • dispVadj hb s x := fun c x => by
    simp only [dispVadj, map_smul]; exact smul_comm _ _ _
  rw [genEps, ContinuousLinearMap.smul_apply, hlin, dispVadj_sub, smul_sub, _root_.neg_smul,
    _root_.neg_smul]
  abel

/-- **Step 3 in the paper's form** (`t₀ = t`, `w = V_ε(t)* a`):
`V(t)* V_ε(t) w - w = -(iħ/2) ∫₀ᵗ V(s)* (Δ(s) - Δ_ε(s)) V_ε(s) w ds`. -/
theorem step3_duhamel_paper {hb : ℝ} (hb0 : hb ≠ 0) (a : negLapH.domain) (t : ℝ) :
    dispVadj hb t (χ.flowEps hb t (ContinuousLinearMap.adjoint (χ.flowEps hb t) a))
        - ContinuousLinearMap.adjoint (χ.flowEps hb t) a
      = -(Complex.I * (hb : ℂ) / 2) • ∫ s in (0 : ℝ)..t,
          dispVadj hb s (lapTbar s (pathBar hS2 hb t a s)
            - χ.lapEps s (χ.flowEps hb s (ContinuousLinearMap.adjoint (χ.flowEps hb t) a))) := by
  have h := step3_duhamel hS2 hb0 t a t
  rw [pathEps_zero] at h
  exact h

end Cutoff

end Qschubert
