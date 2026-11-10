import Qschubert.KLSurf4
import Qschubert.KLD3

/-!
# `Δ_M^N` through the surface object, and (D4)

* `vS_lap_step`, `vS_lapIter` (second part of `lem:surf-lap`): `Δ_M^N 𝒱_s P a = 𝒱_s Δ_φ(s)^N P a`, iterated form `LapIterM`;
* `integral_negLapMH`: `-Δ_M` commutes with integrals of continuous `Dom`-valued paths (from self-adjointness);
* `surf_D4`: **(D4) of `prop:dd-id`**: `Δ_M^N (𝒱_0 a - 𝒱_t a^{(K)}(t)) = c^{K+1} ∫_{Σ_{K+1}(t)} 𝒱_{s₁} b'(s) ds`,
  with `b'(s) = Δ_φ(s₁)^N Δ(s₁)⋯Δ(s_{K+1}) a`, and the norm bound `surf_D4_bound`.
-/

namespace Qschubert

open MeasureTheory UpperHalfPlane Filter Topology
open scoped ENNReal Pointwise MatrixGroups ComplexConjugate

local notation "L2H'" => Lp ℂ 2 (volume : Measure UpperHalfPlane)

variable (Γ : Subgroup PGL(2, ℝ)) [ProperlyDiscontinuousSMul Γ ℍ]

local notation "L2M" => Lp ℂ 2 (surfMeasure Γ)

/-- `u ∈ Dom(Δ_M^N)` with `Δ_M^N u = v`, iterating `Δ_M = -(-Δ_M)`. -/
def LapIterM : ℕ → L2M → L2M → Prop
  | 0, u, v => u = v
  | N + 1, u, v => ∃ h : u ∈ (negLapMH Γ).domain, LapIterM N (-negLapMH Γ ⟨u, h⟩) v

variable {Γ}

lemma LapIterM.snoc : ∀ (N : ℕ) {u v v' : L2M}, LapIterM Γ N u v →
    (∃ h : v ∈ (negLapMH Γ).domain, -negLapMH Γ ⟨v, h⟩ = v') → LapIterM Γ (N + 1) u v'
  | 0, u, v, v', h, h' => by
      obtain rfl : u = v := h
      obtain ⟨hv, e⟩ := h'
      exact ⟨hv, e⟩
  | N + 1, u, v, v', ⟨h, hi⟩, h' => ⟨h, LapIterM.snoc N hi h'⟩

lemma negLapMH_smul (c : ℂ) {u : L2M} (h : u ∈ (negLapMH Γ).domain) (h' : c • u ∈ (negLapMH Γ).domain) :
    negLapMH Γ ⟨c • u, h'⟩ = c • negLapMH Γ ⟨u, h⟩ :=
  (negLapMH Γ).toFun.map_smul c ⟨u, h⟩

lemma LapIterM.smul (c : ℂ) : ∀ (N : ℕ) {u v : L2M}, LapIterM Γ N u v → LapIterM Γ N (c • u) (c • v)
  | 0, u, v, h => by
      obtain rfl : u = v := h
      rfl
  | N + 1, u, v, ⟨h, hi⟩ => by
      refine ⟨Submodule.smul_mem _ _ h, ?_⟩
      rw [negLapMH_smul c h, ← smul_neg]
      exact LapIterM.smul c N hi

/-- Weak criterion for `Dom(-Δ_M)`. -/
lemma mem_negLapMH_of_weak {x y : L2M}
    (h : ∀ w : (negLapMH Γ).domain, inner ℂ y (w : L2M) = inner ℂ x (negLapMH Γ w)) :
    ∃ hx : x ∈ (negLapMH Γ).domain, negLapMH Γ ⟨x, hx⟩ = y := by
  have hadj : x ∈ (LinearPMap.adjoint (negLapMH Γ)).domain := LinearPMap.mem_adjoint_domain_of_exists x ⟨y, h⟩
  have hsa : LinearPMap.adjoint (negLapMH Γ) = negLapMH Γ := negLapMH_isSelfAdjoint Γ
  have hx : x ∈ (negLapMH Γ).domain := by rw [← hsa]; exact hadj
  refine ⟨hx, ?_⟩
  have hval : LinearPMap.adjoint (negLapMH Γ) ⟨x, hadj⟩ = y :=
    LinearPMap.adjoint_apply_eq (negLapMH_isSelfAdjoint Γ).dense_domain ⟨x, hadj⟩ h
  have e : negLapMH Γ ⟨x, hx⟩ = LinearPMap.adjoint (negLapMH Γ) ⟨x, hadj⟩ :=
    ((LinearPMap.ext_iff.mp hsa).2 (x := x) (hf := hadj) (hg := hx)).symm
  rw [e, hval]

/-- `-Δ_M` commutes with integrals of continuous paths in its graph. -/
theorem integral_negLapMH {f g : ℝ → L2M} (hf : Continuous f) (hg : Continuous g)
    (hd : ∀ s, ∃ h : f s ∈ (negLapMH Γ).domain, negLapMH Γ ⟨f s, h⟩ = g s) (a b : ℝ) :
    ∃ h : (∫ s in a..b, f s) ∈ (negLapMH Γ).domain, negLapMH Γ ⟨_, h⟩ = ∫ s in a..b, g s := by
  refine mem_negLapMH_of_weak fun w => ?_
  have e1 : ∀ {p : ℝ → L2M}, Continuous p → ∀ x : L2M,
      inner ℂ (∫ s in a..b, p s) x = conj (∫ s in a..b, inner ℂ x (p s)) := fun {p} hp x => by
    have h := (innerSL ℂ x).intervalIntegral_comp_comm (hp.intervalIntegrable (μ := volume) a b)
    rw [← inner_conj_symm (∫ s in a..b, p s) x]
    congr 1
    exact h.symm
  have hci : ∀ {p : ℝ → L2M}, Continuous p → ∀ x : L2M, Continuous fun s => inner ℂ x (p s) := fun hp x =>
    continuous_const.inner hp
  rw [e1 hg, e1 hf]
  congr 1
  refine intervalIntegral.integral_congr fun s _ => ?_
  obtain ⟨h, e⟩ := hd s
  have hs := (negLapMH_isPositive Γ).1 w ⟨f s, h⟩
  show inner ℂ (w : L2M) (g s) = inner ℂ (negLapMH Γ w) (f s)
  rw [← e]
  exact hs

/-- `Δ_M^N` of an integral. -/
theorem LapIterM.integral : ∀ (N : ℕ) (F : ℕ → ℝ → L2M), (∀ j, Continuous (F j)) →
    (∀ j s, ∃ h : F j s ∈ (negLapMH Γ).domain, -negLapMH Γ ⟨F j s, h⟩ = F (j + 1) s) → ∀ a b : ℝ,
    LapIterM Γ N (∫ s in a..b, F 0 s) (∫ s in a..b, F N s)
  | 0, F, _, _, a, b => rfl
  | N + 1, F, hc, hd, a, b => by
      have hd' : ∀ s, ∃ h : F 0 s ∈ (negLapMH Γ).domain, negLapMH Γ ⟨F 0 s, h⟩ = -F 1 s := fun s => by
        obtain ⟨h, e⟩ := hd 0 s
        exact ⟨h, by rw [← e, neg_neg]⟩
      obtain ⟨h, e⟩ := integral_negLapMH (g := fun s => -F 1 s) (hc 0) (hc 1).neg hd' a b
      refine ⟨h, ?_⟩
      rw [e, intervalIntegral.integral_neg, neg_neg]
      exact LapIterM.integral N (fun j => F (j + 1)) (fun j => hc _) (fun j s => hd _ s) a b

/-! ### Time-dependent `Δ_φ(s)` and its powers -/

/-- `Δ_φ(s)` with time-dependent coefficients. -/
noncomputable def deltaPhiT (ħ : ℝ) : TP :=
  deltaT ++ [(fun _ => -(2 * Complex.I) / ħ, [false]), (fun _ => (-1 + Complex.I * ħ) / (ħ : ℂ) ^ 2, [])]

def oneT : TP := [(fun _ => 1, [])]

def powTP (R : TP) : ℕ → TP
  | 0 => oneT
  | n + 1 => mulTP R (powTP R n)

lemma atT_append (R Q : TP) (s : ℝ) : atT (R ++ Q) s = atT R s ++ atT Q s := by simp [atT]

lemma atT_deltaPhiT (ħ s : ℝ) : atT (deltaPhiT ħ) s = deltaPhiP ħ s := by
  rw [deltaPhiT, atT_append, atT_deltaT]; rfl

lemma atT_powTP (R : TP) (s : ℝ) : ∀ n, atT (powTP R n) s = powWP (atT R s) n
  | 0 => rfl
  | n + 1 => by rw [powTP, atT_mulTP, atT_powTP R s n]; rfl

lemma cont_deltaPhiT (ħ : ℝ) : Cont (deltaPhiT ħ) := by
  intro t ht
  rcases List.mem_append.1 ht with h | h
  · exact cont_deltaT t h
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl <;> exact continuous_const

lemma cont_powTP {R : TP} (hR : Cont R) : ∀ n, Cont (powTP R n)
  | 0 => by
      intro t ht
      simp only [powTP, oneT, List.mem_singleton] at ht
      subst ht
      exact continuous_const
  | n + 1 => cont_mulTP hR (cont_powTP hR n)

namespace SurfW

variable [Countable Γ] {W : SurfW Γ} {a : L2H'} (hA : AllWords a) {Ga : List Bool → L2H'}
  (hGa : ∀ w, W.Chart (Ga w) (wordAct w a)) {hb : ℝ} (hb0 : hb ≠ 0)

include hA

lemma vec_phi (s : ℝ) (P : WP) (hX : domX ⟨polyAct P a, mem_polyAct hA P⟩ ∈ negLapH.domain)
    (hY : domY ⟨polyAct P a, mem_polyAct hA P⟩ ∈ negLapH.domain) :
    phaseDelta hb s ⟨polyAct P a, mem_polyAct hA P⟩ hX hY = polyAct (mulP (deltaPhiP hb s) P) a := by
  rw [← polyAct_mulP hA, deltaPhiP, polyAct_append, ← vec_del hA s P hX hY, polyAct_cons, polyAct_cons, polyAct_nil,
    add_zero]
  have hud : wordAct [] (polyAct P a) ∈ negLapH.domain := mem_polyAct hA P
  have eY : wordAct [false] (polyAct P a) = domY ⟨polyAct P a, mem_polyAct hA P⟩ := by
    rw [wordAct_cons false [] hud]; simp only [domZ, Bool.false_eq_true, ite_false]; rfl
  rw [eY, show wordAct [] (polyAct P a) = polyAct P a from rfl, phaseDelta]
  have hs : (-(2 * Complex.I) / (hb : ℂ)) • domY ⟨polyAct P a, mem_polyAct hA P⟩
      = -((2 * Complex.I / (hb : ℂ)) • domY ⟨polyAct P a, mem_polyAct hA P⟩) := by
    rw [neg_div, _root_.neg_smul]
  rw [hs]
  abel

include hGa hb0

/-- **One step of `Δ_M` through `𝒱_s`.** -/
theorem vS_lap_step (s : ℝ) (P : WP) :
    ∃ h : W.vS hb s (polyAct P a) ∈ (negLapMH Γ).domain,
      -negLapMH Γ ⟨_, h⟩ = W.vS hb s (polyAct (mulP (deltaPhiP hb s) P) a) := by
  have hIn := surfIn_poly hA hGa P
  obtain ⟨hd, e⟩ := surf_step hIn hb0 s
  obtain ⟨h1, e1⟩ := A_evol (negLapMH_isSelfAdjoint Γ) hb (-s) _ hd
  set E := Complex.exp (-(Complex.I * ((s / (2 * hb) : ℝ) : ℂ))) with hE
  have ev : W.vS hb s (polyAct P a)
      = E • evol (negLapMH_isSelfAdjoint Γ) hb (-s) (W.surfL hb s (chartP Ga P)) :=
    W.vS_apply hb s (chart_chartP hGa P)
  have hgφ : gPhi hb s (chartP Ga P) (chartP Ga (mulP (pZ false) P)) (chartP Ga (mulP (pZ true) (mulP (pZ true) P)))
      (chartP Ga (mulP (pZ false) (mulP (pZ false) P))) = chartP Ga (mulP (deltaPhiP hb s) P) := by
    refine (hIn.chart_phi hb s).unique ?_
    rw [vec_phi hA s P hIn.hX hIn.hY]
    exact chart_chartP hGa _
  have ev2 : W.vS hb s (polyAct (mulP (deltaPhiP hb s) P) a)
      = E • evol (negLapMH_isSelfAdjoint Γ) hb (-s) (W.surfL hb s (chartP Ga (mulP (deltaPhiP hb s) P))) :=
    W.vS_apply hb s (chart_chartP hGa _)
  have hm : E • evol (negLapMH_isSelfAdjoint Γ) hb (-s) (W.surfL hb s (chartP Ga P)) ∈ (negLapMH Γ).domain :=
    Submodule.smul_mem _ _ h1
  refine ⟨ev ▸ hm, ?_⟩
  have e2 : negLapMH Γ ⟨W.vS hb s (polyAct P a), ev ▸ hm⟩
      = E • negLapMH Γ ⟨_, h1⟩ := by
    have : (⟨W.vS hb s (polyAct P a), ev ▸ hm⟩ : (negLapMH Γ).domain) = E • ⟨_, h1⟩ := Subtype.ext ev
    rw [this]
    exact (negLapMH Γ).toFun.map_smul E _
  rw [e2, e1, e, hgφ, ev2, map_neg, smul_neg, neg_neg]

/-- **`lem:surf-lap`, iterated**: `Δ_M^N 𝒱_s P a = 𝒱_s Δ_φ(s)^N P a`. -/
theorem vS_lapIter (s : ℝ) (P : WP) (N : ℕ) :
    LapIterM Γ N (W.vS hb s (polyAct P a)) (W.vS hb s (polyAct (mulP (powWP (deltaPhiP hb s) N) P) a)) := by
  induction N with
  | zero =>
    show W.vS hb s (polyAct P a) = W.vS hb s (polyAct (mulP oneP P) a)
    congr 1
    rw [← polyAct_mulP hA, polyAct_oneP]
  | succ N ih =>
    refine LapIterM.snoc N ih ?_
    obtain ⟨h, e⟩ := vS_lap_step hA hGa hb0 s (mulP (powWP (deltaPhiP hb s) N) P)
    refine ⟨h, e.trans ?_⟩
    congr 1
    rw [← polyAct_mulP hA, ← polyAct_mulP hA, ← polyAct_mulP hA, polyAct_powWP_succ (allWords_polyAct hA P)]

/-- The iterated Dyson integrand. -/
noncomputable def fN (W : SurfW Γ) (hb : ℝ) (a : L2H') (K j : ℕ) (s : ℝ) : Lp ℂ 2 (surfMeasure Γ) :=
  W.vS hb s (polyAct (mulP (powWP (deltaPhiP hb s) j) (atT (mulTP deltaT (dysT K)) s)) a)

omit hb0 in
lemma continuous_fN (K j : ℕ) : Continuous (fN W hb a K j) := by
  have e : fN W hb a K j = fun s => W.surfV hb s (chartP Ga (atT (mulTP (powTP (deltaPhiT hb) j) (mulTP deltaT (dysT K))) s)) := by
    funext s
    rw [fN, W.vS_apply hb s (chart_chartP hGa _), atT_mulTP (powTP (deltaPhiT hb) j) (mulTP deltaT (dysT K)) s,
      atT_powTP, atT_deltaPhiT]
  rw [e]
  exact W.continuous_surfV_comp (continuous_chartP Ga
    (cont_mulTP (cont_powTP (cont_deltaPhiT hb) j) (cont_mulTP cont_deltaT (cont_dysT K))))

lemma fN_step (K j : ℕ) (s : ℝ) :
    ∃ h : fN W hb a K j s ∈ (negLapMH Γ).domain, -negLapMH Γ ⟨_, h⟩ = fN W hb a K (j + 1) s := by
  obtain ⟨h, e⟩ := vS_lap_step hA hGa hb0 s (mulP (powWP (deltaPhiP hb s) j) (atT (mulTP deltaT (dysT K)) s))
  refine ⟨h, e.trans ?_⟩
  rw [fN]
  congr 1
  rw [← polyAct_mulP hA, ← polyAct_mulP hA, ← polyAct_mulP hA, polyAct_powWP_succ (allWords_polyAct hA _)]

omit hGa hb0 in
/-- The iterated integrand as a simplex integral. -/
lemma fN_simplex (K N : ℕ) (s : ℝ) :
    fN W hb a K N s = simplexInt K s fun l => W.vS hb s (polyAct (bP hb N s (s :: l)) a) := by
  set Φ := powWP (deltaPhiP hb s) N
  have h := simplex_poly hA (W.vS hb s) K (mulP Φ (deltaP s)) s
  have hf : (fun l => W.vS hb s (polyAct (bP hb N s (s :: l)) a))
      = fun l => W.vS hb s (polyAct (mulP Φ (deltaP s)) (polyAct (deltaProd l) a)) := by
    funext l
    congr 1
    have hl : AllWords (polyAct (deltaProd l) a) := allWords_polyAct hA _
    show polyAct (mulP Φ (mulP (deltaP s) (deltaProd l))) a = _
    rw [← polyAct_mulP hA, ← polyAct_mulP hA, polyAct_mulP hl]
  rw [hf, h, fN]
  congr 1
  have hx : AllWords (xK a K s) := allWords_polyAct hA _
  rw [atT_mulTP, atT_deltaT, ← polyAct_mulP hA, ← polyAct_mulP hA, ← polyAct_mulP hx]
  try rfl

/-- **(D4) of `prop:dd-id`, the identity.** -/
theorem surf_D4 (K N : ℕ) (t : ℝ) :
    LapIterM Γ N (W.vS hb 0 a - W.vS hb t (∑ k ∈ Finset.range (K + 1), (Complex.I * (hb : ℂ) / 2) ^ k • xK a k t))
      ((Complex.I * (hb : ℂ) / 2) ^ (K + 1)
        • simplexInt (K + 1) t fun ss => W.vS hb (ss.headD 0) (polyAct (bP hb N (ss.headD 0) ss) a)) := by
  rw [surf_dyson_J hA hGa hb0]
  refine LapIterM.smul _ N ?_
  have h0 : jS W hb a K t = ∫ s in (0 : ℝ)..t, fN W hb a K 0 s := by
    unfold jS
    refine intervalIntegral.integral_congr fun s _ => ?_
    show W.vS hb s (polyAct (deltaP s) (xK a K s)) = W.vS hb s (polyAct (mulP oneP _) a)
    congr 1
    rw [poly_delta_xK hA, ← polyAct_mulP hA, polyAct_oneP]
  have hN : (simplexInt (K + 1) t fun ss => W.vS hb (ss.headD 0) (polyAct (bP hb N (ss.headD 0) ss) a))
      = ∫ s in (0 : ℝ)..t, fN W hb a K N s := by
    show (∫ s in (0 : ℝ)..t, simplexInt K s fun l =>
      W.vS hb ((s :: l).headD 0) (polyAct (bP hb N ((s :: l).headD 0) (s :: l)) a)) = _
    refine intervalIntegral.integral_congr fun s _ => ?_
    exact (fN_simplex hA K N s).symm
  rw [h0, hN]
  exact LapIterM.integral N (fun j => fN W hb a K j) (fun j => continuous_fN hA hGa K j)
    (fun j s => fN_step hA hGa hb0 K j s) 0 t

omit hA hGa hb0 in
/-- **(D4), the bound**: a uniform bound for `𝒱_{s₁} b'(s)` on the simplex gives `(ħ/2)^{K+1} M t^{K+1}/(K+1)!`. -/
theorem surf_D4_bound {K N : ℕ} {t M : ℝ} (ht : 0 ≤ t) (hM : 0 ≤ M)
    (hb1 : ∀ ss : List ℝ, ss.length = K + 1 → (∀ s ∈ ss, 0 ≤ s ∧ s ≤ t) →
      ‖W.vS hb (ss.headD 0) (polyAct (bP hb N (ss.headD 0) ss) a)‖ ≤ M) :
    ‖(Complex.I * (hb : ℂ) / 2) ^ (K + 1)
        • simplexInt (K + 1) t fun ss => W.vS hb (ss.headD 0) (polyAct (bP hb N (ss.headD 0) ss) a)‖
      ≤ (|hb| / 2) ^ (K + 1) * (M * t ^ (K + 1) / (K + 1).factorial) := by
  rw [norm_smul, norm_pow]
  have hc : ‖Complex.I * (hb : ℂ) / 2‖ = |hb| / 2 := by simp
  rw [hc]
  exact mul_le_mul_of_nonneg_left (norm_simplexInt_le hM (K + 1) t _ ht hb1) (by positivity)

end SurfW

end Qschubert
