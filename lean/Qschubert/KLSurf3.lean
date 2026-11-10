import Qschubert.KLSurf2
import Qschubert.Generator

/-!
# Duhamel on the surface (`lem:surf-lap`, second part, and `lem:surf-duh`)

`surfV hb s` is the surface object `𝒱_s` of `subsec:dd-surf`, in the chart `G = ω g`:
`𝒱_s g = e^{-is/(2ħ)} U_M(-s) [e^{iφ/ħ} S(s) g]_Γ`. It is defined through `U_M`, so `U_M` is never commuted
with periodization.

* `SurfIn`: `g` has two derivatives, with all of them in `L²_ω` (the class `𝒟_ω`);
* `surf_step`: `-Δ_M [e^{iφ/ħ} S(s) g]_Γ = -[e^{iφ/ħ} S(s) Δ_φ(s) g]_Γ`;
* `hasDerivAt_family`: the product rule for a strongly continuous, locally bounded family;
* `surf_duhamel`: `𝒱_b g(b) - 𝒱_a g(a) = ∫_a^b 𝒱_s (g'(s) - c Δ(s) g(s)) ds`, with `c = iħ/2`.
-/

namespace Qschubert

open MeasureTheory UpperHalfPlane Filter Topology Asymptotics
open scoped ENNReal Pointwise MatrixGroups

local notation "L2H'" => Lp ℂ 2 (volume : Measure UpperHalfPlane)

namespace SurfW

variable {Γ : Subgroup PGL(2, ℝ)} [Countable Γ] [ProperlyDiscontinuousSMul Γ ℍ] (W : SurfW Γ)

/-- `G ↦ [e^{iφ/ħ} S(s) (G/ω)]_Γ`. -/
noncomputable def surfL (hb s : ℝ) : L2H' →L[ℂ] Lp ℂ 2 (surfMeasure Γ) := W.perioW.comp (W.TW hb s)

/-- The surface object `𝒱_s`, in the chart `G = ω g`. -/
noncomputable def surfV (hb s : ℝ) : L2H' →L[ℂ] Lp ℂ 2 (surfMeasure Γ) :=
  Complex.exp (-(Complex.I * ((s / (2 * hb) : ℝ) : ℂ))) • (propCLM Γ hb (-s)).comp (W.surfL hb s)

lemma surfV_apply (hb s : ℝ) (x : L2H') :
    W.surfV hb s x = Complex.exp (-(Complex.I * ((s / (2 * hb) : ℝ) : ℂ))) • propCLM Γ hb (-s) (W.surfL hb s x) := rfl

/-- `‖𝒱_s G‖ = ‖[e^{iφ/ħ} S(s) (G/ω)]_Γ‖`. -/
theorem norm_surfV (hb s : ℝ) (x : L2H') : ‖W.surfV hb s x‖ = ‖W.surfL hb s x‖ := by
  rw [surfV_apply, norm_smul, propCLM_eq_evol, norm_evol, mul_comm Complex.I,
    show -(((s / (2 * hb) : ℝ) : ℂ) * Complex.I) = ((-(s / (2 * hb)) : ℝ) : ℂ) * Complex.I by push_cast; ring,
    Complex.norm_exp_ofReal_mul_I, one_mul]

/-- `g ∈ 𝒟_ω`, with charts: `G, GX, GY, GXX, GYY` are `ω g, ω Xg, ω Yg, ω X²g, ω Y²g`. -/
structure SurfIn (g : negLapH.domain) (G GX GY GXX GYY : L2H') : Prop where
  hX : domX g ∈ negLapH.domain
  hY : domY g ∈ negLapH.domain
  cG : W.Chart G (g : L2H')
  cX : W.Chart GX (domX g)
  cY : W.Chart GY (domY g)
  cXX : W.Chart GXX (domX ⟨domX g, hX⟩)
  cYY : W.Chart GYY (domY ⟨domY g, hY⟩)

/-- `Δ(s) g` in the chart. -/
noncomputable def gDel (s : ℝ) (GY GXX GYY : L2H') : L2H' :=
  ((Real.exp (-2 * s) : ℝ) : ℂ) • GXX + GYY - GY

/-- `Δ_φ(s) g` in the chart. -/
noncomputable def gPhi (hb s : ℝ) (G GY GXX GYY : L2H') : L2H' :=
  gDel s GY GXX GYY - (2 * Complex.I / hb) • GY + ((-1 + Complex.I * hb) / (hb : ℂ) ^ 2) • G

variable {W}

theorem SurfIn.chart_phi {g : negLapH.domain} {G GX GY GXX GYY : L2H'} (h : W.SurfIn g G GX GY GXX GYY) (hb s : ℝ) :
    W.Chart (gPhi hb s G GY GXX GYY) (phaseDelta hb s g h.hX h.hY) :=
  (((((h.cXX.smul _).add h.cYY).sub h.cY).sub (h.cY.smul _))).add (h.cG.smul _)

theorem SurfIn.chart_del {g : negLapH.domain} {G GX GY GXX GYY : L2H'} (h : W.SurfIn g G GX GY GXX GYY) (s : ℝ) :
    W.Chart (gDel s GY GXX GYY)
      (((Real.exp (-2 * s) : ℝ) : ℂ) • domX ⟨domX g, h.hX⟩ + domY ⟨domY g, h.hY⟩ - domY g) :=
  ((h.cXX.smul _).add h.cYY).sub h.cY

/-- **The second part of `lem:surf-lap`, before `U_M`.** -/
theorem surf_step {g : negLapH.domain} {G GX GY GXX GYY : L2H'} (h : W.SurfIn g G GX GY GXX GYY) {hb : ℝ}
    (hb0 : hb ≠ 0) (s : ℝ) :
    ∃ hd : W.surfL hb s G ∈ (negLapMH Γ).domain,
      negLapMH Γ ⟨_, hd⟩ = -W.surfL hb s (gPhi hb s G GY GXX GYY) := by
  obtain ⟨hu, e⟩ := phase_transport_dom2 hb0 s g h.hX h.hY
  have c0 := W.TW_chart hb s h.cG
  have c1 := (W.TW_chart hb s (h.chart_phi hb s)).neg
  have c2 := (W.TW_chart hb s h.cX).smul ((Real.exp (-s) : ℝ) : ℂ)
  have c3 := W.TW_chart hb s (h.cY.sub (h.cG.smul (Complex.I / hb)))
  rw [← e] at c1
  rw [← domX_phase_transport hb s g hu] at c2
  rw [← domY_phase_transport hb0 s g hu] at c3
  obtain ⟨hd, hv⟩ := W.surf_lap (⟨_, hu⟩ : negLapH.domain) c0 c1 c2 c3
  refine ⟨hd, ?_⟩
  rw [show negLapMH Γ ⟨W.surfL hb s G, hd⟩ = negLapMH Γ ⟨W.perioW (W.TW hb s G), hd⟩ from rfl, hv, map_neg]
  rfl

/-- The product rule for `r ↦ T r (G r)`, `T` strongly continuous and locally bounded. -/
theorem hasDerivAt_family {T : ℝ → L2H' →L[ℂ] L2H'} {G : ℝ → L2H'} {G' D : L2H'} {s C : ℝ}
    (hC : ∀ᶠ r in 𝓝 s, ∀ x, ‖T r x‖ ≤ C * ‖x‖) (hS : Tendsto (fun r => T r G') (𝓝 s) (𝓝 (T s G')))
    (hd : HasDerivAt (fun r => T r (G s)) D s) (hG : HasDerivAt G G' s) :
    HasDerivAt (fun r => T r (G r)) (D + T s G') s := by
  rw [hasDerivAt_iff_isLittleO] at hd hG ⊢
  have h1 : (fun r => T r (G r - G s - (r - s) • G')) =o[𝓝 s] fun r => r - s := by
    refine IsBigO.trans_isLittleO ?_ hG
    exact IsBigO.of_bound C (hC.mono fun r hr => hr _)
  have h2 : (fun r => (r - s) • (T r G' - T s G')) =o[𝓝 s] fun r => r - s := by
    have h0 : (fun r => T r G' - T s G') =o[𝓝 s] (fun _ => (1 : ℝ)) :=
      (isLittleO_one_iff ℝ).2 (by simpa using hS.sub_const (T s G'))
    have := (isBigO_refl (fun r : ℝ => r - s) (𝓝 s)).smul_isLittleO h0
    simpa using this
  refine ((hd.add h1).add h2).congr_left fun r => ?_
  simp only [map_sub, map_smul, map_add, smul_add, smul_sub, ContinuousLinearMap.map_smul_of_tower]
  abel

/-- **Duhamel on `M`** (`lem:surf-duh`). -/
theorem surf_duhamel {hb : ℝ} (hb0 : hb ≠ 0) {g : ℝ → negLapH.domain} {G G' GX GY GXX GYY : ℝ → L2H'}
    (h : ∀ s, W.SurfIn (g s) (G s) (GX s) (GY s) (GXX s) (GYY s))
    (hd : ∀ s, HasDerivAt G (G' s) s) (hc' : Continuous G') (hcY : Continuous GY) (hcXX : Continuous GXX)
    (hcYY : Continuous GYY) (a b : ℝ) :
    W.surfV hb b (G b) - W.surfV hb a (G a)
      = ∫ s in a..b, W.surfV hb s (G' s - (Complex.I * (hb : ℂ) / 2) • gDel s (GY s) (GXX s) (GYY s)) := by
  have hh : (hb : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hb0
  have hcG : Continuous G := continuous_iff_continuousAt.2 fun s => (hd s).continuousAt
  have hexp : Continuous fun s : ℝ => ((Real.exp (-2 * s) : ℝ) : ℂ) := by fun_prop
  have hcDel : Continuous fun s => gDel s (GY s) (GXX s) (GYY s) := by
    unfold gDel
    exact ((hexp.smul hcXX).add hcYY).sub hcY
  have hcPhi : Continuous fun s => gPhi hb s (G s) (GY s) (GXX s) (GYY s) := by
    unfold gPhi
    have c2 : Continuous fun s => (2 * Complex.I / (hb : ℂ)) • GY s := hcY.const_smul (2 * Complex.I / (hb : ℂ))
    have c3 : Continuous fun s => ((-1 + Complex.I * (hb : ℂ)) / (hb : ℂ) ^ 2) • G s :=
      hcG.const_smul ((-1 + Complex.I * (hb : ℂ)) / (hb : ℂ) ^ 2)
    exact (hcDel.sub c2).add c3
  set GYh : ℝ → L2H' := fun s => GY s - (1 / 2 : ℂ) • G s with hGYh
  have hcYh : Continuous GYh := by
    have c1 : Continuous fun s => (1 / 2 : ℂ) • G s := hcG.const_smul (1 / 2 : ℂ)
    exact hcY.sub c1
  have hL : ∀ {F : ℝ → L2H'}, Continuous F → Continuous fun s => W.surfL hb s (F s) := fun hF =>
    W.perioW.continuous.comp (W.continuous_TW_comp hb hF)
  set E : ℝ → ℂ := fun s => Complex.exp (-(Complex.I * ((s / (2 * hb) : ℝ) : ℂ))) with hE
  have hEd : ∀ s, HasDerivAt E (E s * (-(Complex.I * ((1 / (2 * hb) : ℝ) : ℂ)))) s := fun s =>
    (((((hasDerivAt_id' s).div_const (2 * hb)).ofReal_comp).const_mul Complex.I).neg).cexp
  have hEc : Continuous E := continuous_iff_continuousAt.2 fun s => (hEd s).continuousAt
  have hT : ∀ s, HasDerivAt (fun r => W.TW hb r (G r)) (W.TW hb s (GYh s) + W.TW hb s (G' s)) s := fun s => by
    obtain ⟨D, hD0, hD⟩ := W.exists_mS_bound (|s| + 1)
    have hnear : ∀ᶠ r in 𝓝 s, |r| ≤ |s| + 1 := by
      have : ∀ᶠ r in 𝓝 s, |r| < |s| + 1 := (continuous_abs.tendsto s).eventually (gt_mem_nhds (by simp))
      exact this.mono fun r hr => hr.le
    exact hasDerivAt_family (C := D) (hnear.mono fun r hr x => W.norm_TW_le hb hD hr x)
      ((W.continuous_TW_apply hb (G' s)).tendsto s)
      (W.hasDerivAt_TW hb (g s) (h s).cG ((h s).cY.sub ((h s).cG.smul _)) s) (hd s)
  have hL' : ∀ s, HasDerivAt (fun r => W.surfL hb r (G r))
      (W.surfL hb s (GYh s) + W.surfL hb s (G' s)) s := fun s => by
    have := ((W.perioW.restrictScalars ℝ).hasFDerivAt).comp_hasDerivAt s (hT s)
    have e : W.surfL hb s (GYh s) + W.surfL hb s (G' s)
        = W.perioW (W.TW hb s (GYh s) + W.TW hb s (G' s)) := (map_add W.perioW _ _).symm
    rw [e]
    exact this
  have hw : ∀ s, HasDerivAt (fun r => E r • W.surfL hb r (G r))
      ((E s * (-(Complex.I * ((1 / (2 * hb) : ℝ) : ℂ)))) • W.surfL hb s (G s)
        + E s • (W.surfL hb s (GYh s) + W.surfL hb s (G' s))) s := fun s => by
    have := (hEd s).smul (hL' s)
    rw [add_comm] at this
    exact this
  have hdom : ∀ s, E s • W.surfL hb s (G s) ∈ (negLapMH Γ).domain := fun s =>
    Submodule.smul_mem _ _ (surf_step (h s) hb0 s).1
  have hA : ∀ s, negLapMH Γ ⟨E s • W.surfL hb s (G s), hdom s⟩
      = E s • (-W.surfL hb s (gPhi hb s (G s) (GY s) (GXX s) (GYY s))) := fun s => by
    obtain ⟨hd', e⟩ := surf_step (h s) hb0 s
    have : (⟨E s • W.surfL hb s (G s), hdom s⟩ : (negLapMH Γ).domain) = E s • ⟨_, hd'⟩ := rfl
    rw [this, ← e]
    exact (negLapMH Γ).toFun.map_smul (E s) _
  have hw'c : Continuous fun s => (E s * (-(Complex.I * ((1 / (2 * hb) : ℝ) : ℂ)))) • W.surfL hb s (G s)
      + E s • (W.surfL hb s (GYh s) + W.surfL hb s (G' s)) :=
    ((hEc.mul continuous_const).smul (hL hcG)).add (hEc.smul ((hL hcYh).add (hL hc')))
  have hAc : Continuous fun s => negLapMH Γ ⟨E s • W.surfL hb s (G s), hdom s⟩ := by
    simp_rw [hA]
    exact hEc.smul (hL hcPhi).neg
  have key := duhamel_evol (negLapMH_isSelfAdjoint Γ) hb a b hw hdom hw'c hAc
  have ev : ∀ (s : ℝ) (x : Lp ℂ 2 (surfMeasure Γ)),
      evol (negLapMH_isSelfAdjoint Γ) hb (-s) x = propCLM Γ hb (-s) x := fun _ _ => rfl
  have lhs : ∀ s, evol (negLapMH_isSelfAdjoint Γ) hb (-s) (E s • W.surfL hb s (G s)) = W.surfV hb s (G s) := fun s => by
    rw [map_smul, ev, surfV_apply]
  rw [lhs, lhs] at key
  rw [key]
  refine intervalIntegral.integral_congr fun s _ => ?_
  show evol (negLapMH_isSelfAdjoint Γ) hb (-s) _ = _
  rw [hA, surfV_apply, ← ev, ← map_smul]
  congr 1
  have hstuff : G' s - (Complex.I * (hb : ℂ) / 2) • gDel s (GY s) (GXX s) (GYY s)
      = (-(Complex.I * ((1 / (2 * hb) : ℝ) : ℂ))) • G s + (GYh s + G' s)
        + (Complex.I * (hb : ℂ) / 2) • (-gPhi hb s (G s) (GY s) (GXX s) (GYY s)) := by
    simp only [hGYh, gPhi]
    push_cast
    match_scalars <;> field_simp <;> ring_nf <;> simp [Complex.I_sq] <;> ring
  have hEs : Complex.exp (-(Complex.I * ((s / (2 * hb) : ℝ) : ℂ))) = E s := rfl
  rw [hstuff, hEs]
  simp only [map_add, map_smul, map_neg]
  module

end SurfW

end Qschubert
