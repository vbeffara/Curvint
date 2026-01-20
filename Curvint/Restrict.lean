import Mathlib

open Set Topology unitInterval Filter ContinuousMap

variable {E X Z : Type*} [TopologicalSpace E] [TopologicalSpace X] [TopologicalSpace Z]
  {e e₀ : E} {x x₀ : X} {p : E → X} {γ : C(I, X)} {m n : ℕ}

def restrict_prop {α β : Type*} {p : β → Prop} [TopologicalSpace α] [TopologicalSpace β]
    [LocallyCompactPair α β] : C(α, {b // p b}) ≃ₜ {f : C(α, β) // ∀ a, p (f a)} where
  toFun f := ⟨ContinuousMap.comp ⟨_, continuous_subtype_val⟩ f, fun a => (f a).2⟩
  invFun := by
    let Ψ : C({f : C(α, β) // ∀ a, p (f a)} × α, C(α, β) × α) := ⟨fun fx => ⟨fx.1.1, fx.2⟩, by fun_prop⟩
    let Λ : C(C(α, β) × α, β) := ⟨fun fx => fx.1 fx.2, continuous_eval⟩
    let Φ : C({f : C(α, β) // ∀ a, p (f a)} × α, {b // p b}) :=
    { toFun := fun fx => ⟨fx.1.1 fx.2, fx.1.2 fx.2⟩
      continuous_toFun := (Λ.comp Ψ).continuous.subtype_mk _ }
    exact Φ.curry.1
  left_inv f := rfl
  right_inv f := by ext ; simp
  continuous_toFun := Continuous.subtype_mk (continuous_postcomp _) _
  continuous_invFun := ContinuousMap.continuous_toFun _

def restrict_range {α β : Type*} {s : Set β} [TopologicalSpace α] [TopologicalSpace β]
    [LocallyCompactPair α β] : C(α, s) ≃ₜ {f : C(α, β) // range f ⊆ s} := by
  convert restrict_prop (α := α) (p := fun b => b ∈ s) <;> exact range_subset_iff

section restrict

namespace Trivialization

variable {F Z B : Type*} [TopologicalSpace F] [TopologicalSpace B] [TopologicalSpace Z] {p : Z → B}

def empty (hZ : IsEmpty Z) (hF : IsEmpty (B × F)) : Trivialization F p where
  source := univ
  baseSet := univ
  target := univ
  target_eq := univ_prod_univ.symm
  source_eq := rfl
  open_target := isOpen_univ
  open_source := isOpen_univ
  open_baseSet := isOpen_univ
  toFun z := hZ.false z |>.elim
  invFun z := hF.false z |>.elim
  map_source' _ _ := trivial
  map_target' _ _ := trivial
  left_inv' z := hZ.false z |>.elim
  right_inv' z := hF.false z |>.elim
  proj_toFun := by simp
  continuousOn_toFun := by simp [univ_eq_empty_iff.mpr hZ]
  continuousOn_invFun := by simp [eq_empty_of_isEmpty univ]

theorem continuous_dite_of_forall {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    {P : α → Prop} [DecidablePred P] {f : ∀ x, P x → β} {g : ∀ x, ¬ P x → β} {s : Set α}
    (hs : ∀ x ∈ s, P x) (hf : Continuous fun y : {x // P x} => f y.1 y.2) :
    ContinuousOn (fun x => if h : P x then f x h else g x h) s := by
  apply continuousOn_iff_continuous_restrict.2
  convert_to Continuous fun x : s => f x.1 <| hs x.1 x.2
  · ext x ; simp [hs]
  let φ (x : s) : {x // P x} := ⟨x.1, hs x.1 x.2⟩
  have h1 : Continuous φ := continuous_induced_dom.subtype_mk _
  exact hf.comp h1

noncomputable def restrictBaseSet_aux (T : Trivialization F p) (s : Set B) (z₀ : p ⁻¹' s) :
    Trivialization F (s.restrictPreimage p) where
  source := Subtype.val ⁻¹' T.source
  baseSet := Subtype.val ⁻¹' T.baseSet
  target := (Subtype.val ⁻¹' T.baseSet) ×ˢ univ
  target_eq := by dsimp
  source_eq := by ext ; dsimp ; simp only [T.source_eq, mem_preimage, restrictPreimage_coe]
  open_target := (T.open_baseSet.preimage continuous_subtype_val).prod isOpen_univ
  open_source := T.open_source.preimage continuous_subtype_val
  open_baseSet := T.open_baseSet.preimage continuous_subtype_val
  --
  toFun x := by
    by_cases hx : x.1 ∈ T.source
    · have : (T x).1 = p x := T.proj_toFun _ hx
      have : (T x).1 ∈ s := by rw [this] ; exact x.2
      exact ⟨⟨(T x).1, this⟩, (T x).2⟩
    · let Tx := T x
      refine ⟨⟨p x, x.2⟩, (T x).2⟩
  invFun x := by
    by_cases hx : (x.1.1, x.2) ∈ T.target
    · refine ⟨T.invFun (x.1.1, x.2), by simp [T.proj_symm_apply hx]⟩
    · exact z₀
  --
  map_source' x (hx : x.1 ∈ T.source) := by
    simp only [hx, ↓reduceDIte, coe_fst, mem_prod, mem_preimage, mem_univ, and_true]
    have h1 := T.map_source' hx
    have h2 := T.proj_symm_apply h1
    simp only [OpenPartialHomeomorph.toFun_eq_coe, coe_coe, T.mem_target] at h1
    have := T.left_inv' hx
    simp only [OpenPartialHomeomorph.toFun_eq_coe, coe_coe, PartialEquiv.invFun_as_coe,
      OpenPartialHomeomorph.coe_coe_symm] at this
    simp only [OpenPartialHomeomorph.toFun_eq_coe, coe_coe, this] at h2
    simpa only [h2]
  map_target' x hx := by
    have hx' : (↑x.1, x.2) ∈ T.target := by simpa only [T.mem_target, mem_preimage] using hx.1
    simp only [hx', ↓reduceDIte, PartialEquiv.invFun_as_coe, OpenPartialHomeomorph.coe_coe_symm,
      mem_preimage, OpenPartialHomeomorph.map_target]
  left_inv' x (hx : x.1 ∈ T.source) := by
    simp only [hx, ↓reduceDIte, coe_fst, PartialEquiv.invFun_as_coe, OpenPartialHomeomorph.coe_coe_symm,
      symm_apply_mk_proj, Subtype.coe_eta, dite_eq_left_iff]
    have h1 : T x ∈ T.target := T.map_source hx
    simp [← T.coe_fst hx, h1]
  right_inv' x hx :=  by
    have hx' : (↑x.1, x.2) ∈ T.target := by simpa only [T.mem_target, mem_preimage] using hx.1
    simp only [hx', ↓reduceDIte, PartialEquiv.invFun_as_coe, OpenPartialHomeomorph.coe_coe_symm,
      OpenPartialHomeomorph.map_target, T.apply_symm_apply, Subtype.coe_eta, Prod.mk.eta]
  proj_toFun x (hx : x.1 ∈ T.source) := by ext ; simp [hx]
  --
  continuousOn_toFun := by
    classical
    have key : ContinuousOn T T.source := T.continuousOn_toFun
    apply continuous_dite_of_forall (by simp)
    refine continuous_prodMk.mpr ⟨?_, ?_⟩
    · apply Continuous.subtype_mk
      apply @continuousOn_iff_continuous_restrict (p ⁻¹' s) _ _ _ (fun u => (T u).1) _ |>.mp
      apply continuous_fst.comp_continuousOn
      exact key.comp continuous_subtype_val.continuousOn (fun x hx => hx)
    · exact continuous_snd.comp <| key.comp_continuous (by fun_prop) (by simp)
  continuousOn_invFun := by
    classical
    apply continuous_dite_of_forall (by simp [T.mem_target])
    apply Continuous.subtype_mk
    apply @continuousOn_iff_continuous_restrict (↑s × F) Z _ _
      (fun x => (OpenPartialHomeomorph.symm T.toOpenPartialHomeomorph) (↑x.1, x.2)) _ |>.mp
    exact T.continuousOn_invFun.comp (by fun_prop) (fun x hx => hx)

noncomputable def restrictBaseSet (T : Trivialization F p) (s : Set B) :
    Trivialization F ((s ∩ T.baseSet).restrictPreimage p) := by
  by_cases hZ : IsEmpty (p ⁻¹' (s ∩ T.baseSet))
  · apply Trivialization.empty hZ
    by_contra hs
    let y := Classical.choice <| not_isEmpty_iff.mp hs
    have : T.invFun (y.1.1, y.2) ∈ (p ⁻¹' (s ∩ T.baseSet)) := by
      simp only [PartialEquiv.invFun_as_coe, OpenPartialHomeomorph.coe_coe_symm, mem_preimage]
      rw [T.proj_symm_apply' y.1.2.2]
      exact y.1.2
    exact hZ.false ⟨_, this⟩
  · exact T.restrictBaseSet_aux _ <| Classical.choice <| not_isEmpty_iff.mp hZ

end Trivialization

namespace IsEvenlyCovered

variable {F Z B : Type*} [TopologicalSpace F] [TopologicalSpace B] [TopologicalSpace Z] {p : Z → B}

theorem of_isEmpty {x : B} (hZ : IsEmpty Z) (hF : IsEmpty F) : IsEvenlyCovered p x F := by
  let T := Trivialization.empty (F := F) (p := p) hZ (by simp [hF])
  apply IsEvenlyCovered.of_trivialization (t := T)
  simp [T,Trivialization.empty]

end IsEvenlyCovered

namespace IsCoveringMapOn

-- theorem isCoveringMap_aux {p : E → X} {s : Set X} (hp : IsCoveringMapOn p s) (z₀ : p ⁻¹' s) :
--     IsCoveringMap (s.restrictPreimage p) := by
--   intro x
--   specialize hp
--   obtain ⟨t, h2⟩ := hp x x.2 |>.toTrivialization


--   obtain ⟨h1, t, h2⟩ := hp x.1 x.2
--   have key : DiscreteTopology (s.restrictPreimage p ⁻¹' {x}) := by
--     rw [Set.preimage_restrictPreimage, Set.image_singleton]
--     change DiscreteTopology ↑((_ ∘ _) ⁻¹' _)
--     simp only [preimage_comp]
--     exact h1.preimage_of_continuous_injective _ continuous_subtype_val Subtype.val_injective
--   apply IsEvenlyCovered.of_trivialization
--   let TT : Trivialization (↑(s.restrictPreimage p ⁻¹' {x})) (s.restrictPreimage p) := by
--     apply (Trivialization.restrictBaseSet_aux t s z₀).transFiberHomeomorph
--     refine ⟨?_, continuous_of_discreteTopology, continuous_of_discreteTopology⟩
--     refine ⟨?_, ?_, ?_, ?_⟩
--     · intro z
--       have : p z = x := z.2
--       refine ⟨⟨z.1, by simp [this]⟩, by simp [this]⟩
--     · intro z
--       have : (s.restrictPreimage p) z = x := z.2
--       refine ⟨z.1, by simp [← this]⟩
--     all_goals { intro z ; simp }
--   refine ⟨key, ?_, ?_⟩
--   · exact h2

theorem isCoveringMap {p : E → X} {s : Set X} (hp : IsCoveringMapOn p s) :
    IsCoveringMap (s.restrictPreimage p) := by
  exact isCoveringMap_restrictPreimage s hp

end IsCoveringMapOn

end restrict
