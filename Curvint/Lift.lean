import Mathlib.Topology.ContinuousMap.Interval
import Mathlib.Topology.FiberBundle.Trivialization
import Mathlib.Topology.UnitInterval
import Mathlib.Topology.Covering
import Mathlib.Tactic.Peel
import Mathlib.Topology.CompactOpen

open Set Topology unitInterval Filter ContinuousMap

variable
  {E : Type*} [TopologicalSpace E] {e e₀ : E}
  {F : Type*} [TopologicalSpace F]
  {X : Type*} [TopologicalSpace X] {x x₀ : X} {p : E → X} {γ : C(I, X)}
  {Z : Type*} [TopologicalSpace Z]

local instance : Fact ((0 : ℝ) ≤ 1) := ⟨zero_le_one⟩

namespace Trivialization

variable {T : Trivialization Z p} {a b : ℝ}

def lift (T : Trivialization Z p) (e : E) (x : X) : E := T.invFun (x, (T e).2)

@[simp] theorem lift_self (hx : p e ∈ T.baseSet) : T.lift e (p e) = e := by
  simp [lift] ; rw [symm_apply_mk_proj] ; rwa [mem_source]

@[simp] theorem lift_proj (hx : x ∈ T.baseSet) : p (T.lift e x) = x := by
  simp [lift] ; apply proj_symm_apply ; rwa [mem_target]

def liftCM (T : Trivialization Z p) : C(T.source × T.baseSet, T.source) where
  toFun ex := ⟨T.lift ex.1 ex.2, T.map_target (by simp [mem_target])⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    refine T.continuousOn_invFun.comp_continuous ?_ (by simp [mem_target])
    apply continuous_prod_mk.mpr ⟨by fun_prop, continuous_snd.comp ?_⟩
    exact T.continuousOn_toFun.comp_continuous (by fun_prop) (by simp)

def clift (T : Trivialization Z p) : C(T.source × C(Icc a b, T.baseSet), C(Icc a b, T.source)) := by
  let Ψ : C((T.source × C(Icc a b, T.baseSet)) × Icc a b, C(Icc a b, T.baseSet) × Icc a b) :=
    ⟨fun eγt => (eγt.1.2, eγt.2), by fun_prop⟩
  refine ContinuousMap.curry <| T.liftCM.comp <| ⟨fun eγt => ⟨eγt.1.1, eγt.1.2 eγt.2⟩, ?_⟩
  simpa using ⟨by fun_prop, ContinuousEval.continuous_eval.comp Ψ.continuous⟩

variable {e : T.source} {γ : C(Icc a b, T.baseSet)} {t : Icc a b}

@[simp] theorem clift_proj : p (T.clift (e, γ) t) = γ t := by
  simp [clift, liftCM]

@[simp] theorem clift_left [Fact (a ≤ b)] (h : p e.1 = γ ⊥) :
    T.clift (e, γ) ⊥ = e := by
  ext ; simp [clift, liftCM, ← h] ; rw [lift_self] ; simp [h]

end Trivialization

namespace IsCoveringMap

theorem eq_of_comp_eq' (hp : IsCoveringMap p) {A : Type*} [TopologicalSpace A] [PreconnectedSpace A]
    {g₁ g₂ : C(A, E)} (he : p ∘ g₁ = p ∘ g₂) {a : A} (ha : g₁ a = g₂ a) : g₁ = g₂ :=
  ContinuousMap.ext (congrFun <| hp.eq_of_comp_eq g₁.continuous_toFun g₂.continuous_toFun he a ha)

theorem lift_unique (hp : IsCoveringMap p) {Γ₁ Γ₂ : C(I, E)} (h0 : Γ₁ 0 = Γ₂ 0)
    (h : p ∘ Γ₁ = p ∘ Γ₂) : Γ₁ = Γ₂ := by
  exact hp.eq_of_comp_eq' h h0

end IsCoveringMap

structure Setup (p : E → X) where
  t : ℕ → ℝ
  n : ℕ
  --
  ht : Monotone t
  ht0 : t 0 = 0
  ht1 : ∀ m ≥ n, t m = 1
  --
  c : ℕ → X
  T (i : ℕ) : Trivialization (p ⁻¹' {c i}) p

namespace Setup

variable {S : Setup p} {m n : ℕ}

instance : Fact (S.t 0 ≤ S.t n) := ⟨S.ht n.zero_le⟩
instance : Fact (S.t n ≤ S.t (n + 1)) := ⟨S.ht n.le_succ⟩

abbrev icc (S : Setup p) (n : ℕ) : Set ℝ := Icc (S.t n) (S.t (n + 1))

@[simp] theorem htn : S.t S.n = 1 := S.ht1 S.n le_rfl

@[simp] theorem mem_I : S.t n ∈ I := by
  refine ⟨?_, ?_⟩ <;> simp [← S.ht0, ← S.ht1 (n + S.n) (by omega)] <;> apply S.ht <;> omega

@[simp] theorem subset : Icc (S.t m) (S.t n) ⊆ I := by
  rintro t ⟨ht0, ht1⟩ ; exact ⟨le_trans mem_I.1 ht0, le_trans ht1 mem_I.2⟩

attribute [simp] ht0 ht1

def inj (S : Setup p) : C(Icc (S.t m) (S.t n), I) := ⟨fun t => ⟨t, subset t.2⟩, by fun_prop⟩

def fits (S : Setup p) (γ : C(I, X)) : Prop :=
  ∀ n ∈ Finset.range S.n, MapsTo (IccExtendCM γ) (S.icc n) (S.T n).baseSet

abbrev Liftable (S : Setup p) := {γe : C(I, X) × E // S.fits γe.1 ∧ p γe.2 = γe.1 0}

def γn (γe : S.Liftable) (hn : n ∈ Finset.range S.n) : C(S.icc n, (S.T n).baseSet) := by
  refine ⟨fun t => ⟨γe.1.1 (S.inj t), ?_⟩, ?_⟩
  · simpa [Setup.subset t.2, Setup.inj] using γe.2.1 n hn t.2
  · fun_prop

noncomputable def exist (hp : IsCoveringMap p) (γ : C(I, X)) : { S : Setup p // S.fits γ } := by
  let T (t : I) : Trivialization (p ⁻¹' {γ t}) p := Classical.choose (hp (γ t)).2
  let mem_T (t : I) : γ t ∈ (T t).baseSet := Classical.choose_spec (hp (γ t)).2
  let V (t : I) : Set I := γ ⁻¹' (T t).baseSet
  have h1 t : IsOpen (V t) := (T t).open_baseSet.preimage γ.continuous
  have h2 : univ ⊆ ⋃ t, V t := by intro t _ ; rw [mem_iUnion] ; use t ; apply mem_T
  have := exists_monotone_Icc_subset_open_cover_unitInterval h1 h2
  choose t ht0 ht ht1 c hc using this
  choose n ht1 using ht1
  refine ⟨⟨fun n => t n, n, ht, by simpa using ht0, by simpa using ht1, fun n => γ (c n),
    fun n => T (c n)⟩, ?_⟩
  rintro k - s hs
  simpa [subset hs] using hc k hs

theorem fits.eventually {Y : Type*} [TopologicalSpace Y] {y₀ : Y} {γ : C(Y, C(I, X))}
    (hS : S.fits (γ y₀)) : ∀ᶠ y in 𝓝 y₀, S.fits (γ y) := by
  simp only [Setup.fits, eventually_all_finset] at hS ⊢
  peel hS with n hn hS
  have key := ContinuousMap.eventually_mapsTo CompactIccSpace.isCompact_Icc (S.T n).open_baseSet hS
  have h4 := IccExtendCM.2.tendsto (γ y₀) |>.eventually key
  exact γ.2.tendsto y₀ |>.eventually h4

end Setup

section reboot

variable {S : Setup p} {n : ℕ}

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
          simpa [Trivialization.mem_source, h5, Setup.subset h6] using γe.2.1 n h1 h6
        use ⟨left, next⟩
        simp only [comp_apply, coe_mk, next]
        rw [Trivialization.clift_left]
        simp [ih.2] ; rfl
      · refine Continuous.subtype_mk (continuous_prod_mk.2 ⟨by fun_prop, ?_⟩) _
        apply ContinuousMap.continuous_postcomp _ |>.comp
        apply (S.T n).clift.continuous.comp
        refine continuous_prod_mk.2 ⟨?_, ?_⟩
        · exact (continuous_eval_const _).comp ih.1.continuous |>.subtype_mk _
        · let Ψ : C(S.Liftable × S.icc n, C(I, X) × I) :=
            ⟨fun fx => (fx.1.1.1, ⟨fx.2.1, Setup.subset fx.2.2⟩), by fun_prop⟩
          let Φ : C(S.Liftable × S.icc n, (S.T n).baseSet) := by
            refine ⟨fun fx => ⟨fx.1.1.1 ⟨fx.2.1, Setup.subset fx.2.2⟩, ?_⟩, ?_⟩
            · obtain ⟨_, _⟩ := Setup.subset fx.2.2
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
        · rw [concatCM_right <| le_of_not_le htn] ; simp ; rfl

noncomputable def LiftWithin_CM :
    {F : C(S.Liftable, C(I, E)) // ∀ γe, F γe 0 = γe.1.2 ∧ ∀ t, p (F γe t) = γe.1.1 t} := by
  obtain ⟨F, hF⟩ := LiftWithin_partialCM (S := S) le_rfl
  let Φ : C(I, Icc (S.t 0) (S.t S.n)) := ⟨fun t => ⟨t, by simp⟩, by fun_prop⟩
  refine ⟨⟨fun γe => (F γe).comp Φ, by fun_prop⟩, fun γe => ⟨?_, fun t => ?_⟩⟩
  · simpa [Bot.bot] using hF γe |>.1
  · simpa [Setup.inj] using hF γe |>.2 (Φ t)

theorem Lift (hp : IsCoveringMap p) (he : p e = γ 0) :
    ∃! Γ : C(I, E), Γ 0 = e ∧ p ∘ Γ = γ := by
  obtain ⟨S, hS⟩ := Setup.exist hp γ
  obtain ⟨F, hF⟩ := LiftWithin_CM (S := S)
  have h1 : F ⟨⟨γ, e⟩, hS, he⟩ 0 = e := hF ⟨⟨γ, e⟩, hS, he⟩ |>.1
  have h2 : p ∘ F ⟨⟨γ, e⟩, hS, he⟩ = γ := by ext t ; exact hF ⟨⟨γ, e⟩, hS, he⟩ |>.2 t
  refine ⟨F ⟨⟨γ, e⟩, hS, he⟩, ⟨h1, h2⟩, ?_⟩
  rintro Γ ⟨hΓ₁, hΓ₂⟩
  apply hp.lift_unique <;> simp [*]

#print axioms Lift

noncomputable def TheLift (γ : C(I, X)) (hp : IsCoveringMap p) (he : p e = γ 0) : C(I, E) :=
  (Lift hp he).exists.choose

@[simp] theorem TheLift_spec (γ : C(I, X)) (hp : IsCoveringMap p) (he : p e = γ 0) :
    (TheLift γ hp he) 0 = e ∧ p ∘ (TheLift γ hp he) = γ :=
  (Lift hp he).exists.choose_spec

end reboot

section HLift

variable {Y : Type*} [TopologicalSpace Y] {γ : C(I × Y, X)} {Γ₀ : C(Y, E)}

def Slice (γ : C(I × Y, X)) : C(Y, C(I, X)) := γ.comp prodSwap |>.curry

noncomputable def JointLift (hp : IsCoveringMap p) (hΓ₀ : ∀ y, p (Γ₀ y) = γ (0, y)) :
    C(Y, C(I, E)) := by
  refine ⟨fun y => TheLift (Slice γ y) hp (hΓ₀ y), ?_⟩
  rw [continuous_iff_continuousAt] ; intro y₀
  obtain ⟨S, hS⟩ := Setup.exist hp (Slice γ y₀)
  apply ContinuousOn.continuousAt ?_ hS.eventually
  rw [continuousOn_iff_continuous_restrict]
  let G₁ : C(S.Liftable, C(I, E)) := LiftWithin_CM |>.1
  let G₂ : C({y // S.fits (Slice γ y)}, S.Liftable) :=
    ⟨fun y => ⟨⟨Slice γ y, Γ₀ y⟩, y.2, hΓ₀ y⟩, by fun_prop⟩
  convert G₁.comp G₂ |>.continuous
  ext1 y
  have h3 := LiftWithin_CM |>.2 ⟨⟨Slice γ y, Γ₀ y⟩, y.2, hΓ₀ y⟩
  apply hp.lift_unique
  · simp [G₁, G₂, h3, TheLift_spec]
  · simp [G₁, G₂, TheLift_spec] ; ext t ; simp [h3]

theorem HLift (hp : IsCoveringMap p) (hΓ₀ : ∀ y, p (Γ₀ y) = γ (0, y)) :
    ∃! Γ : C(I × Y, E), ∀ y, Γ (0, y) = Γ₀ y ∧ p ∘ (Γ ⟨·, y⟩) = (γ ⟨·, y⟩) := by
  refine ⟨JointLift hp hΓ₀ |>.uncurry |>.comp prodSwap, ?_, ?_⟩
  · exact fun y => TheLift_spec (Slice γ y) hp (hΓ₀ y)
  · rintro Γ hΓ ; ext1 ⟨t, y⟩
    have h1 : p (Γ₀ y) = Slice γ y 0 := hΓ₀ y
    suffices (Γ.comp prodSwap |>.curry y) = (TheLift _ hp h1) from ContinuousMap.congr_fun this t
    apply hp.lift_unique
    · simp [TheLift_spec _ hp h1, hΓ]
    · simp ; ext t
      have := congr_fun (hΓ y |>.2) t ; simp at this
      simp [this, Slice]

#print axioms HLift

theorem HLift' [LocallyCompactSpace Y] (hp : IsCoveringMap p) {γ : C(I, C(Y, X))}
    (hΓ₀ : ∀ y, p (Γ₀ y) = γ 0 y) :
    ∃! Γ : C(I, C(Y, E)), ∀ y, Γ 0 y = Γ₀ y ∧ p ∘ (Γ · y) = (γ · y) := by
  obtain ⟨Γ, h1, h2⟩ := HLift hp hΓ₀ (γ := γ.uncurry)
  refine ⟨Γ.curry, h1, fun Γ' h3 => ?_⟩
  simp [← h2 Γ'.uncurry h3] ; rfl

end HLift

section restrict

theorem bla {p : E → X} {s : Set X} (hp : IsCoveringMapOn p s) :
    IsCoveringMap (s.restrictPreimage p) := by
  intro x
  obtain ⟨h1, t, h2⟩ := hp x.1 x.2
  refine ⟨?_, ?_⟩
  · rw [Set.preimage_restrictPreimage, Set.image_singleton]
    change DiscreteTopology ↑((_ ∘ _) ⁻¹' _)
    simp only [preimage_comp]
    exact h1.preimage_of_continuous_injective _ continuous_subtype_val Subtype.val_injective
  · sorry

end restrict
