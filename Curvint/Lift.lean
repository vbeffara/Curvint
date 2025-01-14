import Mathlib.Topology.ContinuousMap.Interval
import Mathlib.Topology.UnitInterval
import Mathlib.Topology.Covering
import Mathlib.Tactic.Peel

open Set Topology unitInterval Filter ContinuousMap

local instance : Fact ((0 : ℝ) ≤ 1) := ⟨zero_le_one⟩

variable {E X Z : Type*} [TopologicalSpace E] [TopologicalSpace X] [TopologicalSpace Z]
  {e e₀ : E} {x x₀ : X} {p : E → X} {γ : C(I, X)} {m n : ℕ}

namespace IsCoveringMap

theorem lift_unique (hp : IsCoveringMap p) {Γ₁ Γ₂ : C(I, E)} (h0 : Γ₁ 0 = Γ₂ 0)
    (h : p ∘ Γ₁ = p ∘ Γ₂) : Γ₁ = Γ₂ :=
  ContinuousMap.ext <| congrFun <| hp.eq_of_comp_eq Γ₁.continuous Γ₂.continuous h 0 h0

/-- Subdivision of an interval with an associated sequence of trivializations of the covering `p`.
  One can lift a path `γ` by gluing local lifts along such a subdivision if it is adapted to it,
  see `fits`. -/
structure LiftSetup (p : E → X) where
  /-- The bounds of the intervals in the subdivision. -/
  t : ℕ → ℝ
  /-- The number of (non-trivial) pieces. -/
  n : ℕ
  /-- The sequence of basepoints for the trivializations. -/
  c : ℕ → X
  /-- The trivializations. -/
  T : ∀ i, Trivialization (p ⁻¹' {c i}) p
  ht : Monotone t
  ht0 : t 0 = 0
  ht1 : ∀ m ≥ n, t m = 1

variable {S : LiftSetup p}

local instance : Fact (S.t 0 ≤ S.t n) := ⟨S.ht n.zero_le⟩

local instance : Fact (S.t n ≤ S.t (n + 1)) := ⟨S.ht n.le_succ⟩

namespace LiftSetup

/-- The `n`th interval in the partition contained in `S`. -/
abbrev icc (S : LiftSetup p) (n : ℕ) : Set ℝ := Icc (S.t n) (S.t (n + 1))

@[simp]
theorem htn : S.t S.n = 1 := S.ht1 S.n le_rfl

@[simp]
theorem mem_I : S.t n ∈ I := by
  refine ⟨?_, ?_⟩ <;> simp [← S.ht0, ← S.ht1 (n + S.n) (by omega)] <;> apply S.ht <;> omega

@[simp]
theorem subset : Icc (S.t m) (S.t n) ⊆ I := by
  rintro t ⟨ht0, ht1⟩ ; exact ⟨le_trans mem_I.1 ht0, le_trans ht1 mem_I.2⟩

attribute [simp] ht0 ht1

/-- The embedding of intervals adapted to the partition in `S` into the unit interval. -/
def inj (S : LiftSetup p) : C(Icc (S.t m) (S.t n), I) :=
  ⟨fun t => ⟨t, subset t.2⟩, by fun_prop⟩

/-- This holds if the path `γ` maps each interval in the partition in `S` to the base set of the
corresponding trivialization. -/
def fits (S : LiftSetup p) (γ : C(I, X)) : Prop :=
  ∀ n ∈ Finset.range S.n, MapsTo (IccExtendCM γ) (S.icc n) (S.T n).baseSet

noncomputable def exist (hp : IsCoveringMap p) (γ : C(I, X)) : { S : LiftSetup p // S.fits γ } := by
  let T (t : I) : Trivialization (p ⁻¹' {γ t}) p := Classical.choose (hp (γ t)).2
  let mem_T (t : I) : γ t ∈ (T t).baseSet := Classical.choose_spec (hp (γ t)).2
  let V (t : I) : Set I := γ ⁻¹' (T t).baseSet
  have h1 t : IsOpen (V t) := (T t).open_baseSet.preimage γ.continuous
  have h2 : univ ⊆ ⋃ t, V t := by intro t _ ; rw [mem_iUnion] ; use t ; apply mem_T
  have := exists_monotone_Icc_subset_open_cover_unitInterval h1 h2
  choose t ht0 ht ht1 c hc using this
  choose n ht1 using ht1
  use ⟨(t ·), n, γ ∘ c, fun n => T (c n), ht, by simpa using ht0, by simpa using ht1⟩
  rintro k - s hs
  simpa [subset hs] using hc k hs

theorem fits.eventually {Y : Type*} [TopologicalSpace Y] {y₀ : Y} {γ : C(Y, C(I, X))}
    (hS : S.fits (γ y₀)) : ∀ᶠ y in 𝓝 y₀, S.fits (γ y) := by
  simp only [LiftSetup.fits, eventually_all_finset] at hS ⊢
  peel hS with n hn hS
  have key := ContinuousMap.eventually_mapsTo CompactIccSpace.isCompact_Icc (S.T n).open_baseSet hS
  have h4 := IccExtendCM.2.tendsto (γ y₀) |>.eventually key
  exact γ.2.tendsto y₀ |>.eventually h4

abbrev Liftable (S : LiftSetup p) := { γe : C(I, X) × E // S.fits γe.1 ∧ p γe.2 = γe.1 0 }

def γn (γe : Liftable S) (hn : n ∈ Finset.range S.n) : C(S.icc n, (S.T n).baseSet) := by
  refine ⟨fun t => ⟨γe.1.1 (S.inj t), ?_⟩, ?_⟩
  · simpa [LiftSetup.subset t.2, LiftSetup.inj] using γe.2.1 n hn t.2
  · fun_prop

end LiftSetup

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

noncomputable def LiftWithin_partialCM (hn : n ≤ S.n) :
    {F : C(S.Liftable, C(Icc (S.t 0) (S.t n), E)) // ∀ γe,
      F γe ⊥ = γe.1.2 ∧
      ∀ t, p (F γe t) = γe.1.1 (S.inj t)} := by
  induction n with
  | zero =>
    refine ⟨?_, ?_⟩
    · apply ContinuousMap.const'.comp ⟨fun ye => ye.1.2, by fun_prop⟩
    · simp ; rintro γ e - he t rfl ; exact he
  | succ n ih =>
    specialize ih (by omega)
    have h1 : n ∈ Finset.range S.n := by simp ; omega
    refine ⟨?_, ?_⟩
    · refine (concatCM (b := S.t n)).comp ⟨?_, ?_⟩
      · intro γe
        have h5 : p (ih.1 γe ⊤) = γe.1.1 ⟨S.t n, _⟩ := (ih.2 γe).2 ⊤
        have h6 : S.t n ∈ S.icc n := by simpa using S.ht n.le_succ
        let left : C(↑(Icc (S.t 0) (S.t n)), E) := ih.1 γe
        let next : C(S.icc n, E) := by
          refine .comp ⟨_, continuous_subtype_val⟩ <| (S.T n).clift (⟨left ⊤, ?_⟩, S.γn γe h1)
          simpa [Trivialization.mem_source, left, h5, LiftSetup.subset h6] using γe.2.1 n h1 h6
        use ⟨left, next⟩
        simp only [comp_apply, coe_mk, next]
        rw [Trivialization.clift_self]
        simp [left, ih.2]
        rfl
      · refine Continuous.subtype_mk (continuous_prod_mk.2 ⟨by fun_prop, ?_⟩) _
        apply ContinuousMap.continuous_postcomp _ |>.comp
        apply (S.T n).clift.continuous.comp
        refine continuous_prod_mk.2 ⟨?_, ?_⟩
        · exact (continuous_eval_const _).comp ih.1.continuous |>.subtype_mk _
        · let Ψ : C(S.Liftable × S.icc n, C(I, X) × I) :=
            ⟨fun fx => (fx.1.1.1, ⟨fx.2.1, LiftSetup.subset fx.2.2⟩), by fun_prop⟩
          let Φ : C(S.Liftable × S.icc n, (S.T n).baseSet) := by
            refine ⟨fun fx => ⟨fx.1.1.1 ⟨fx.2.1, LiftSetup.subset fx.2.2⟩, ?_⟩, ?_⟩
            · obtain ⟨_, _⟩ := LiftSetup.subset fx.2.2
              have := fx.1.2.1 n h1 fx.2.2
              rw [IccExtendCM_of_mem] at this ; assumption
            · apply Continuous.subtype_mk
              exact ContinuousEval.continuous_eval.comp Ψ.continuous
          exact Φ.curry.continuous
    · rintro ⟨⟨γ, e⟩, hγ, he⟩ ; dsimp ; constructor
      · rw [concatCM_left (S.ht n.zero_le)] ; exact ih.2 ⟨⟨γ, e⟩, hγ, he⟩ |>.1
      · rintro ⟨t, ht⟩
        by_cases htn : t ≤ S.t n
        · rw [concatCM_left htn] ; exact ih.2 ⟨⟨γ, e⟩, hγ, he⟩ |>.2 ⟨t, _⟩
        · rw [concatCM_right <| le_of_not_le htn]
          set γe : S.Liftable := ⟨(γ, e), hγ, he⟩ with hγe
          have := ih.2 γe ; simp [hγe] at this
          simp [Trivialization.proj_clift (proj := p)]
          rfl

noncomputable def LiftWithin_CM :
    {F : C(S.Liftable, C(I, E)) // ∀ γe, F γe 0 = γe.1.2 ∧ ∀ t, p (F γe t) = γe.1.1 t} := by
  obtain ⟨F, hF⟩ := LiftWithin_partialCM (S := S) le_rfl
  let Φ : C(I, Icc (S.t 0) (S.t S.n)) := ⟨fun t => ⟨t, by simp⟩, by fun_prop⟩
  refine ⟨⟨fun γe => (F γe).comp Φ, by fun_prop⟩, fun γe => ⟨?_, fun t => ?_⟩⟩
  · simpa [Bot.bot] using hF γe |>.1
  · simpa [LiftSetup.inj] using hF γe |>.2 (Φ t)

theorem exists_unique_lift (hp : IsCoveringMap p) (he : p e = γ 0) :
    ∃! Γ : C(I, E), Γ 0 = e ∧ p ∘ Γ = γ := by
  obtain ⟨S, hS⟩ := LiftSetup.exist hp γ
  obtain ⟨F, hF⟩ := LiftWithin_CM (S := S)
  have h1 : F ⟨⟨γ, e⟩, hS, he⟩ 0 = e := hF ⟨⟨γ, e⟩, hS, he⟩ |>.1
  have h2 : p ∘ F ⟨⟨γ, e⟩, hS, he⟩ = γ := by ext t ; exact hF ⟨⟨γ, e⟩, hS, he⟩ |>.2 t
  refine ⟨F ⟨⟨γ, e⟩, hS, he⟩, ⟨h1, h2⟩, ?_⟩
  rintro Γ ⟨hΓ₁, hΓ₂⟩
  apply hp.lift_unique <;> simp [*]

noncomputable def lift (γ : C(I, X)) (hp : IsCoveringMap p) (he : p e = γ 0) : C(I, E) :=
  (exists_unique_lift hp he).exists.choose

@[simp]
theorem lift_spec (γ : C(I, X)) (hp : IsCoveringMap p) (he : p e = γ 0) :
    lift γ hp he 0 = e ∧ p ∘ lift γ hp he = γ :=
  (exists_unique_lift hp he).exists.choose_spec

section HLift

variable {Y : Type*} [TopologicalSpace Y] {γ : C(I × Y, X)} {Γ₀ : C(Y, E)}

def Slice (γ : C(I × Y, X)) : C(Y, C(I, X)) := γ.comp prodSwap |>.curry

noncomputable def JointLift (hp : IsCoveringMap p) (hΓ₀ : ∀ y, p (Γ₀ y) = γ (0, y)) :
    C(Y, C(I, E)) := by
  refine ⟨fun y => lift (Slice γ y) hp (hΓ₀ y), ?_⟩
  rw [continuous_iff_continuousAt] ; intro y₀
  obtain ⟨S, hS⟩ := LiftSetup.exist hp (Slice γ y₀)
  apply ContinuousOn.continuousAt ?_ hS.eventually
  rw [continuousOn_iff_continuous_restrict]
  let G₁ : C(S.Liftable, C(I, E)) := LiftWithin_CM |>.1
  let G₂ : C({y // S.fits (Slice γ y)}, S.Liftable) :=
    ⟨fun y => ⟨⟨Slice γ y, Γ₀ y⟩, y.2, hΓ₀ y⟩, by fun_prop⟩
  convert G₁.comp G₂ |>.continuous
  ext1 y
  have h3 := LiftWithin_CM |>.2 ⟨⟨Slice γ y, Γ₀ y⟩, y.2, hΓ₀ y⟩
  apply hp.lift_unique <;> simp [G₁, G₂, h3, lift_spec]
  ext t ; simp [h3]

theorem HLift (hp : IsCoveringMap p) (hΓ₀ : ∀ y, p (Γ₀ y) = γ (0, y)) :
    ∃! Γ : C(I × Y, E), ∀ y, Γ (0, y) = Γ₀ y ∧ p ∘ (Γ ⟨·, y⟩) = (γ ⟨·, y⟩) := by
  refine ⟨JointLift hp hΓ₀ |>.uncurry |>.comp prodSwap, ?_, ?_⟩
  · exact fun y => lift_spec (Slice γ y) hp (hΓ₀ y)
  · rintro Γ hΓ ; ext1 ⟨t, y⟩
    have h1 : p (Γ₀ y) = Slice γ y 0 := hΓ₀ y
    suffices (Γ.comp prodSwap |>.curry y) = (lift _ hp h1) from ContinuousMap.congr_fun this t
    apply hp.lift_unique
    · simp [lift_spec _ hp h1, hΓ]
    · simp ; ext t
      have := congr_fun (hΓ y |>.2) t ; simp at this
      simp [this, Slice]

theorem HLift' [LocallyCompactSpace Y] (hp : IsCoveringMap p) {γ : C(I, C(Y, X))}
    (hΓ₀ : ∀ y, p (Γ₀ y) = γ 0 y) :
    ∃! Γ : C(I, C(Y, E)), ∀ y, Γ 0 y = Γ₀ y ∧ p ∘ (Γ · y) = (γ · y) := by
  obtain ⟨Γ, h1, h2⟩ := HLift hp hΓ₀ (γ := γ.uncurry)
  refine ⟨Γ.curry, h1, fun Γ' h3 => ?_⟩
  simp [← h2 Γ'.uncurry h3] ; rfl

end HLift

end IsCoveringMap

#print axioms IsCoveringMap.HLift

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
    simp only [PartialHomeomorph.toFun_eq_coe, coe_coe, T.mem_target] at h1
    have := T.left_inv' hx
    simp only [PartialHomeomorph.toFun_eq_coe, coe_coe, PartialEquiv.invFun_as_coe,
      PartialHomeomorph.coe_coe_symm] at this
    simp only [PartialHomeomorph.toFun_eq_coe, coe_coe, this] at h2
    simpa only [h2]
  map_target' x hx := by
    have hx' : (↑x.1, x.2) ∈ T.target := by simpa only [T.mem_target, mem_preimage] using hx.1
    simp only [hx', ↓reduceDIte, PartialEquiv.invFun_as_coe, PartialHomeomorph.coe_coe_symm,
      mem_preimage, PartialHomeomorph.map_target]
  left_inv' x (hx : x.1 ∈ T.source) := by
    simp only [hx, ↓reduceDIte, coe_fst, PartialEquiv.invFun_as_coe, PartialHomeomorph.coe_coe_symm,
      symm_apply_mk_proj, Subtype.coe_eta, id_eq, eq_mpr_eq_cast, dite_eq_left_iff]
    have h1 : T x ∈ T.target := T.map_source hx
    simp [← T.coe_fst hx, h1]
  right_inv' x hx :=  by
    have hx' : (↑x.1, x.2) ∈ T.target := by simpa only [T.mem_target, mem_preimage] using hx.1
    simp only [hx', ↓reduceDIte, PartialEquiv.invFun_as_coe, PartialHomeomorph.coe_coe_symm,
      PartialHomeomorph.map_target, T.apply_symm_apply, Subtype.coe_eta, Prod.mk.eta]
  proj_toFun x (hx : x.1 ∈ T.source) := by ext ; simp [hx]
  --
  continuousOn_toFun := by
    classical
    have key : ContinuousOn T T.source := T.continuousOn_toFun
    apply continuous_dite_of_forall (by simp)
    refine continuous_prod_mk.mpr ⟨?_, ?_⟩
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
      (fun x => (PartialHomeomorph.symm T.toPartialHomeomorph) (↑x.1, x.2)) _ |>.mp
    exact T.continuousOn_invFun.comp (by fun_prop) (fun x hx => hx)

noncomputable def restrictBaseSet (T : Trivialization F p) (s : Set B) :
    Trivialization F ((s ∩ T.baseSet).restrictPreimage p) := by
  by_cases hZ : IsEmpty (p ⁻¹' (s ∩ T.baseSet))
  · apply Trivialization.empty hZ
    by_contra hs
    let y := Classical.choice <| not_isEmpty_iff.mp hs
    have : T.invFun (y.1.1, y.2) ∈ (p ⁻¹' (s ∩ T.baseSet)) := by
      simp only [PartialEquiv.invFun_as_coe, PartialHomeomorph.coe_coe_symm, mem_preimage]
      rw [T.proj_symm_apply' y.1.2.2]
      exact y.1.2
    exact hZ.false ⟨_, this⟩
  · exact T.restrictBaseSet_aux _ <| Classical.choice <| not_isEmpty_iff.mp hZ

end Trivialization

namespace IsEvenlyCovered

variable {F Z B : Type*} [TopologicalSpace F] [TopologicalSpace B] [TopologicalSpace Z] {p : Z → B}

theorem of_isEmpty {x : B} (hZ : IsEmpty Z) (hF : IsEmpty F) : IsEvenlyCovered p x F :=
  ⟨Subsingleton.discreteTopology, .empty hZ (by simp [hF]), trivial⟩

end IsEvenlyCovered

namespace IsCoveringMapOn

theorem isCoveringMap_aux {p : E → X} {s : Set X} (hp : IsCoveringMapOn p s) (z₀ : p ⁻¹' s) :
    IsCoveringMap (s.restrictPreimage p) := by
  intro x
  obtain ⟨h1, t, h2⟩ := hp x.1 x.2
  have key : DiscreteTopology (s.restrictPreimage p ⁻¹' {x}) := by
    rw [Set.preimage_restrictPreimage, Set.image_singleton]
    change DiscreteTopology ↑((_ ∘ _) ⁻¹' _)
    simp only [preimage_comp]
    exact h1.preimage_of_continuous_injective _ continuous_subtype_val Subtype.val_injective
  refine ⟨key, ?_, ?_⟩
  · apply (t.restrictBaseSet_aux s z₀).transFiberHomeomorph
    refine ⟨?_, continuous_of_discreteTopology, continuous_of_discreteTopology⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro z
      have : p z = x := z.2
      refine ⟨⟨z.1, by simp [this]⟩, by simp [this]⟩
    · intro z
      have : (s.restrictPreimage p) z = x := z.2
      refine ⟨z.1, by simp [← this]⟩
    all_goals { intro z ; simp }
  · exact h2

theorem isCoveringMap {p : E → X} {s : Set X} (hp : IsCoveringMapOn p s) :
    IsCoveringMap (s.restrictPreimage p) := by
  by_cases hs : IsEmpty (p ⁻¹' s)
  · exact fun _ => IsEvenlyCovered.of_isEmpty hs inferInstance
  · exact isCoveringMap_aux hp <| Classical.choice <| not_isEmpty_iff.mp hs

end IsCoveringMapOn

theorem IsCoveringMap.of_isEmpty {p : E → X} (hp : IsEmpty E) : IsCoveringMap p := by
  intro x
  convert IsEvenlyCovered.of_isEmpty hp <| instIsEmptyElemEmptyCollection E
  exact eq_empty_of_isEmpty (p ⁻¹' {x})

end restrict

#lint
