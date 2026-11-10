import Qschubert.Friedrichs

/-!
# Naturality of the Friedrichs extension

If a unitary `U` and its inverse both map the domain of the densely defined positive `T` into itself
and commute with `T` there (`PreservesOp T U` and `PreservesOp T U.symm`; the predicate itself is
one-way, the pair gives `U(Dom T) = Dom T`), then `U` is an isometry of the form domain, extends to the form space
`Q` (`formU`, with `ι ∘ formU = U ∘ ι`, `formIncl_formU`), and commutes with the resolvent
`R = ιι*` (`formRes_U`). Hence `U` maps the domain of the Friedrichs extension `S` onto itself and
`S U = U S` there (`friedrichsExt_U`). This is used for the affine isometries of `ℍ`, which carry
the local Sobolev chart at `i` to every centre.
-/

namespace Qschubert

open Physicslib4.Spectral.Unbounded
open scoped InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- `U` preserves `Dom T` and commutes with `T`. -/
structure PreservesOp (T : H →ₗ.[ℂ] H) (U : H ≃ₗᵢ[ℂ] H) : Prop where
  mem : ∀ x ∈ T.domain, U x ∈ T.domain
  comm : ∀ (x : T.domain) (hx : U x ∈ T.domain), T ⟨U x, hx⟩ = U (T x)

variable (T : H →ₗ.[ℂ] H) [hT : Fact (IsPositive T)] {U : H ≃ₗᵢ[ℂ] H}

namespace FormDom

/-- `U` on the form domain. -/
noncomputable def mapU (hU : PreservesOp T U) : FormDom T →ₗ[ℂ] FormDom T where
  toFun x := ofDom T ⟨U (val T x), hU.mem _ (toDom T x).2⟩
  map_add' x y := by
    apply Subtype.ext
    show U (val T (x + y)) = U (val T x) + U (val T y)
    rw [val_add, map_add]
  map_smul' c x := by
    apply Subtype.ext
    show U (val T (c • x)) = c • U (val T x)
    rw [val_smul, map_smul]

omit [CompleteSpace H] hT in
lemma val_mapU (hU : PreservesOp T U) (x : FormDom T) : val T (mapU T hU x) = U (val T x) := rfl

omit [CompleteSpace H] hT in
lemma app_mapU (hU : PreservesOp T U) (x : FormDom T) : app T (mapU T hU x) = U (app T x) :=
  hU.comm (toDom T x) _

omit [CompleteSpace H] in
lemma inner_mapU (hU : PreservesOp T U) (x y : FormDom T) :
    ⟪mapU T hU x, mapU T hU y⟫_ℂ = ⟪x, y⟫_ℂ := by
  rw [inner_eq, inner_eq, formInner, formInner, val_mapU, val_mapU, app_mapU,
    LinearIsometryEquiv.inner_map_map, LinearIsometryEquiv.inner_map_map]

omit [CompleteSpace H] in
lemma norm_mapU (hU : PreservesOp T U) (x : FormDom T) : ‖mapU T hU x‖ = ‖x‖ := by
  rw [@norm_eq_sqrt_re_inner ℂ, @norm_eq_sqrt_re_inner ℂ, inner_mapU]

/-- `U` on the form domain as a continuous linear map. -/
noncomputable def mapUL (hU : PreservesOp T U) : FormDom T →L[ℂ] FormDom T :=
  LinearMap.mkContinuous (mapU T hU) 1 (fun x => by rw [norm_mapU, one_mul])

end FormDom

/-- `U` on the form space `Q`. -/
noncomputable def formU (hU : PreservesOp T U) : FormSpace T →L[ℂ] FormSpace T :=
  ((UniformSpace.Completion.toComplL : FormDom T →L[ℂ] FormSpace T).comp (FormDom.mapUL T hU)).extend
    (UniformSpace.Completion.toComplL : FormDom T →L[ℂ] FormSpace T)

lemma formU_coe (hU : PreservesOp T U) (x : FormDom T) :
    formU T hU (x : FormSpace T) = ((FormDom.mapU T hU x : FormDom T) : FormSpace T) :=
  ContinuousLinearMap.extend_eq _ (e := (UniformSpace.Completion.toComplL : FormDom T →L[ℂ] FormSpace T))
    UniformSpace.Completion.denseRange_coe (UniformSpace.Completion.isUniformInducing_coe _) x

lemma inner_formU (hU : PreservesOp T U) (u w : FormSpace T) :
    ⟪formU T hU u, formU T hU w⟫_ℂ = ⟪u, w⟫_ℂ := by
  refine UniformSpace.Completion.induction_on₂ u w ?_ ?_
  · exact isClosed_eq (((formU T hU).continuous.comp continuous_fst).inner
      ((formU T hU).continuous.comp continuous_snd)) (continuous_fst.inner continuous_snd)
  · intro x y
    rw [formU_coe, formU_coe, UniformSpace.Completion.inner_coe, UniformSpace.Completion.inner_coe,
      FormDom.inner_mapU]

lemma formIncl_formU (hU : PreservesOp T U) (u : FormSpace T) :
    formIncl T (formU T hU u) = U (formIncl T u) := by
  refine UniformSpace.Completion.induction_on u ?_ ?_
  · exact isClosed_eq ((formIncl T).continuous.comp (formU T hU).continuous)
      (U.continuous.comp (formIncl T).continuous)
  · intro x
    rw [formU_coe, formIncl_coe, formIncl_coe, FormDom.val_mapU]

lemma formU_formU_symm (hU : PreservesOp T U) (hU' : PreservesOp T U.symm) (w : FormSpace T) :
    formU T hU (formU T hU' w) = w := by
  refine UniformSpace.Completion.induction_on w ?_ ?_
  · exact isClosed_eq ((formU T hU).continuous.comp (formU T hU').continuous) continuous_id
  · intro x
    rw [formU_coe, formU_coe]
    congr 1
    apply Subtype.ext
    show U (U.symm (FormDom.val T x)) = FormDom.val T x
    simp

/-- `ι*(U f) = Ũ (ι* f)`. -/
lemma adjoint_formIncl_U (hU : PreservesOp T U) (hU' : PreservesOp T U.symm) (f : H) :
    ContinuousLinearMap.adjoint (formIncl T) (U f)
      = formU T hU (ContinuousLinearMap.adjoint (formIncl T) f) := by
  refine ext_inner_right ℂ fun w => ?_
  rw [ContinuousLinearMap.adjoint_inner_left]
  conv_rhs => rw [← formU_formU_symm T hU hU' w, inner_formU, ContinuousLinearMap.adjoint_inner_left,
    formIncl_formU]
  rw [← LinearIsometryEquiv.inner_map_map U f, LinearIsometryEquiv.apply_symm_apply]

/-- **`R U = U R`**. -/
theorem formRes_U (hU : PreservesOp T U) (hU' : PreservesOp T U.symm) (f : H) :
    formRes T (U f) = U (formRes T f) := by
  rw [formRes, ContinuousLinearMap.comp_apply, adjoint_formIncl_U T hU hU', formIncl_formU]
  rfl

/-- **Naturality of the Friedrichs extension**: `U` preserves `Dom S` and `S U = U S`. -/
theorem friedrichsExt_U (hd : HasDenseDomain T) (hU : PreservesOp T U) (hU' : PreservesOp T U.symm)
    (x : (friedrichsExt T hd).domain) :
    ∃ h : U x ∈ (friedrichsExt T hd).domain, friedrichsExt T hd ⟨U x, h⟩ = U (friedrichsExt T hd x) := by
  obtain ⟨g, rfl⟩ := (resEquiv T hd).surjective x
  have hmem : U (resEquiv T hd g : H) ∈ (friedrichsExt T hd).domain :=
    ⟨U g, by rw [coe_resEquiv]; exact formRes_U T hU hU' g⟩
  refine ⟨hmem, ?_⟩
  have heq : (⟨U (resEquiv T hd g : H), hmem⟩ : (friedrichsExt T hd).domain) = resEquiv T hd (U g) :=
    Subtype.ext (show U (formRes T g) = formRes T (U g) from (formRes_U T hU hU' g).symm)
  rw [heq, friedrichsExt_apply, friedrichsExt_apply, formRes_U T hU hU', map_sub]

end Qschubert
