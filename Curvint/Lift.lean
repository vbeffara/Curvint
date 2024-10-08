import Mathlib

open Set Topology Metric unitInterval Filter ContinuousMap

variable
  {α : Type*} [LinearOrder α] [TopologicalSpace α] [OrderTopology α] {a b c : α}
  {E : Type*} [TopologicalSpace E] {e e₀ : E}
  {F : Type*} [TopologicalSpace F]
  {X : Type*} [TopologicalSpace X] {x x₀ : X} {p : E → X} {γ : C(I, X)}
  {Z : Type*} [TopologicalSpace Z]

namespace ContinuousMap

def subset {s₁ s₂ : Set E} (h : s₁ ⊆ s₂) : C(s₁, s₂) := ⟨fun x => ⟨x.1, h x.2⟩, by fun_prop⟩

def subset_left (h : b ∈ Icc a c) : C(Icc a b, Icc a c) := subset (Icc_subset_Icc le_rfl h.2)

def subset_right (h : b ∈ Icc a c) : C(Icc b c, Icc a c) := subset (Icc_subset_Icc h.1 le_rfl)

def firstval (hab : a ≤ b) : C(C(Icc a b, E), E) := ⟨fun f => f ⟨a, le_rfl, hab⟩, by continuity⟩

def lastval (hab : a ≤ b) : C(C(Icc a b, E), E) := ⟨fun f => f ⟨b, hab, le_rfl⟩, by continuity⟩

omit [OrderTopology α] in
@[simp] theorem firstval_comp {hab : a ≤ b} {γ : C(Icc a b, E)} {f : C(E, F)} :
    firstval hab (f.comp γ) = f (firstval hab γ) := rfl

omit [OrderTopology α] in
@[simp] theorem lastval_comp {hab : a ≤ b} {γ : C(Icc a b, E)} {f : C(E, F)} :
    lastval hab (f.comp γ) = f (lastval hab γ) := rfl

def IccExtendCM (hab : a ≤ b) : C(C(Icc a b, E), C(α, E)) where
  toFun f := f.comp ⟨projIcc a b hab, continuous_projIcc⟩
  continuous_toFun := continuous_comp_left _

@[simp] theorem IccExtendCM_of_mem {hab : a ≤ b} {f : C(Icc a b, E)} {x : α} (hx : x ∈ Icc a b) :
    IccExtendCM hab f x = f ⟨x, hx⟩ := by
  simp [IccExtendCM, projIcc, hx.1, hx.2]

noncomputable def concat (h : b ∈ Icc a c) (f : C(Icc a b, E)) (g : C(Icc b c, E)) : C(Icc a c, E) := by
  by_cases hb : lastval h.1 f = firstval h.2 g
  · let h (t : α) : E := if t ≤ b then IccExtendCM h.1 f t else IccExtendCM h.2 g t
    suffices Continuous h from ⟨fun t => h t, by fun_prop⟩
    apply Continuous.if_le (by fun_prop) (by fun_prop) continuous_id continuous_const
    rintro x rfl ; simpa [IccExtendCM]
  · exact .const _ (firstval h.1 f) -- junk value

variable {f : C(Icc a b, E)} {g : C(Icc b c, E)}

theorem concat_comp_left (h : b ∈ Icc a c) (hb : lastval h.1 f = firstval h.2 g) :
    f = (concat h f g).comp (subset_left h) := by
  ext x ; simp [concat, IccExtendCM, hb, subset_left, subset, x.2.2]

theorem concat_comp_right (h : b ∈ Icc a c) (hb : lastval h.1 f = firstval h.2 g) :
    g = (concat h f g).comp (subset_right h) := by
  ext x ; by_cases hxb : x = b
  · simp [concat, hb, subset_right, subset, hxb]
    simp [lastval, firstval] at hb ; simp [IccExtendCM, hb] ; simp [← hxb]
  · have := lt_of_le_of_ne x.2.1 (Ne.symm hxb) |>.not_le
    simp [concat, hb, subset_right, subset, x.2.2, this, IccExtendCM]

@[simp] theorem concat_left (h : b ∈ Icc a c) (hb : lastval h.1 f = firstval h.2 g)
    {t : Icc a c} (ht : t ≤ b) : concat h f g t = f ⟨t, t.2.1, ht⟩ := by
  nth_rewrite 2 [concat_comp_left h hb] ; rfl

@[simp] theorem concat_right (h : b ∈ Icc a c) (hb : lastval h.1 f = firstval h.2 g)
    {t : Icc a c} (ht : b ≤ t) : concat h f g t = g ⟨t, ht, t.2.2⟩ := by
  nth_rewrite 2 [concat_comp_right h hb] ; rfl

theorem concat_forall (h : b ∈ Icc a c) (hb : lastval h.1 f = firstval h.2 g) (pred : α → E → Prop)
    (h1 : ∀ t : Icc a b, pred t (f t)) (h2 : ∀ t : Icc b c, pred t (g t)) (t : Icc a c) :
    pred t (concat h f g t) := by
  by_cases ht : t ≤ b
  · simp [ht, hb] ; convert h1 _ using 1 ; rfl
  · simp [le_of_not_le ht, hb] ; convert h2 _ using 1 ; rfl

variable {ι : Type*} {p : Filter ι} {F : ι → C(Icc a b, E)} {G : ι → C(Icc b c, E)} [CompactIccSpace α]

theorem tendsto_concat (h : b ∈ Icc a c) (hfg : ∀ᶠ i in p, lastval h.1 (F i) = firstval h.2 (G i))
    (hfg' : lastval h.1 f = firstval h.2 g) (hf : Tendsto F p (𝓝 f)) (hg : Tendsto G p (𝓝 g)) :
    Tendsto (fun i => concat h (F i) (G i)) p (𝓝 (concat h f g)) := by
  rw [tendsto_nhds_compactOpen] at hf hg ⊢
  rintro K hK U hU hfgU
  let K₁ : Set (Icc a b) := subset_left h ⁻¹' K
  let K₂ : Set (Icc b c) := subset_right h ⁻¹' K
  have hK₁ : IsCompact K₁ := hK.preimage_continuous (subset_left h).2
  have hK₂ : IsCompact K₂ := hK.preimage_continuous (subset_right h).2
  have hfU : MapsTo f K₁ U := by rw [concat_comp_left h hfg'] ; exact hfgU.comp (mapsTo_preimage _ _)
  have hgU : MapsTo g K₂ U := by rw [concat_comp_right h hfg'] ; exact hfgU.comp (mapsTo_preimage _ _)
  filter_upwards [hf K₁ hK₁ U hU hfU, hg K₂ hK₂ U hU hgU, hfg] with i hf hg hfg x hx
  by_cases hx' : x ≤ b
  · simpa [concat_left h hfg hx'] using hf hx
  · simpa [concat_right h hfg (lt_of_not_le hx' |>.le)] using hg hx

noncomputable def concatCM (h : b ∈ Icc a c) :
    C({f : C(Icc a b, E) × C(Icc b c, E) // lastval h.1 f.1 = firstval h.2 f.2}, C(Icc a c, E)) := by
  refine ⟨fun fg => concat h fg.1.1 fg.1.2, ?_⟩
  let Φ : C(Icc a b, E) × C(Icc b c, E) → C(Icc a c, E) := (concat h).uncurry
  let S : Set (C(Icc a b, E) × C(Icc b c, E)) := {f | lastval h.1 f.1 = firstval h.2 f.2}
  change Continuous (S.restrict Φ)
  refine continuousOn_iff_continuous_restrict.mp (fun fg hfg => ?_)
  refine tendsto_concat h ?_ hfg ?_ ?_
  · apply eventually_nhdsWithin_of_forall ; intro f hf ; exact hf
  · exact tendsto_nhdsWithin_of_tendsto_nhds continuousAt_fst
  · exact tendsto_nhdsWithin_of_tendsto_nhds continuousAt_snd

@[simp] theorem concatCM_left {h : b ∈ Icc a c} {x : Icc a c} (hx : x ≤ b)
    {fg : {f : C(Icc a b, E) × C(Icc b c, E) // lastval h.1 f.1 = firstval h.2 f.2}} :
    concatCM h fg x = fg.1.1 ⟨x.1, x.2.1, hx⟩ := by
  exact concat_left h fg.2 hx

@[simp] theorem concatCM_right {h : b ∈ Icc a c} {x : Icc a c} (hx : b ≤ x)
    {fg : {f : C(Icc a b, E) × C(Icc b c, E) // lastval h.1 f.1 = firstval h.2 f.2}} :
    concatCM h fg x = fg.1.2 ⟨x.1, hx, x.2.2⟩ := by
  exact concat_right h fg.2 hx

def restr {α β : Type*} [TopologicalSpace α] [TopologicalSpace β] {A : Set α} {B : Set β} (hS : IsOpen B) :
    C({f : C(A, β) // range f ⊆ B}, C(A, B)) := by
  refine ⟨fun γ => ⟨fun t => ⟨γ.1 t, γ.2 (mem_range_self t)⟩, by fun_prop⟩, ?_⟩
  refine (continuous_compactOpen.mpr ?_)
  intro K hK U hU
  have h1 := isOpen_setOf_mapsTo hK <| hS.isOpenMap_subtype_val U hU
  convert isOpen_induced h1 ; ext ⟨γ, hγ⟩ ; constructor
  · intro h t ht ; simpa using ⟨hγ <| mem_range_self _, h ht⟩
  · intro h t ht ; obtain ⟨⟨a, ha⟩, b1, rfl⟩ := h ht ; assumption

end ContinuousMap

namespace Trivialization

variable {T : Trivialization Z p} {a b : ℝ}

abbrev S (T : Trivialization Z p) := T.source × T.baseSet
abbrev Γ (T : Trivialization Z p) (a b : ℝ) := C(Icc a b, T.baseSet)

def lift (T : Trivialization Z p) (e : E) (x : X) : E := T.invFun (x, (T e).2)

@[simp] theorem lift_self (hx : p e ∈ T.baseSet) : T.lift e (p e) = e := by
  simp [lift] ; rw [symm_apply_mk_proj] ; rwa [mem_source]

@[simp] theorem lift_proj (hx : x ∈ T.baseSet) : p (T.lift e x) = x := by
  simp [lift] ; apply proj_symm_apply ; rwa [mem_target]

def liftCM (T : Trivialization Z p) : C(T.S, T.source) where
  toFun ex := ⟨T.lift ex.1 ex.2, T.map_target (by simp [mem_target])⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    refine T.continuousOn_invFun.comp_continuous ?_ (by simp [mem_target])
    apply continuous_prod_mk.mpr ⟨by fun_prop, continuous_snd.comp ?_⟩
    exact T.continuousOn_toFun.comp_continuous (by fun_prop) (by simp)

def clift (T : Trivialization Z p) : C(T.source × T.Γ a b, C(Icc a b, T.source)) := by
  refine ContinuousMap.curry <| T.liftCM.comp <| ⟨fun eγt => ⟨eγt.1.1, eγt.1.2 eγt.2⟩, ?_⟩
  let Ψ : C((T.source × T.Γ a b) × Icc a b, T.Γ a b × Icc a b) :=
    ⟨fun eγt => (eγt.1.2, eγt.2), by fun_prop⟩
  simpa using ⟨by fun_prop, ContinuousMap.continuous_eval.comp Ψ.continuous⟩

@[simp] theorem clift_proj {e} {γ : T.Γ a b} {t} : p (T.clift (e, γ) t) = γ t := by
  simp [clift, liftCM]

@[simp] theorem clift_left (hab : a ≤ b) {e} {γ : T.Γ a b} {h : p e.1 = γ ⟨a, left_mem_Icc.2 hab⟩} :
    T.clift (e, γ) ⟨a, left_mem_Icc.2 hab⟩ = e := by
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

abbrev icc (S : Setup p) (n : ℕ) : Set ℝ := Icc (S.t n) (S.t (n + 1))

@[simp] theorem htn : S.t S.n = 1 := S.ht1 S.n le_rfl

@[simp] theorem mem_I : S.t n ∈ I := by
  refine ⟨?_, ?_⟩ <;> simp [← S.ht0, ← S.ht1 (n + S.n) (by omega)] <;> apply S.ht <;> omega

@[simp] theorem left_mem : S.t n ∈ S.icc n := by simp ; apply S.ht ; simp

@[simp] theorem right_mem : S.t (n + 1) ∈ S.icc n := by simp ; apply S.ht ; simp

@[simp] theorem subset : Icc (S.t m) (S.t n) ⊆ I := by
  rintro t ⟨ht0, ht1⟩ ; exact ⟨le_trans mem_I.1 ht0, le_trans ht1 mem_I.2⟩

attribute [simp] ht0 ht1

def inj (S : Setup p) : C(Icc (S.t m) (S.t n), I) := ⟨fun t => ⟨t, subset t.2⟩, by fun_prop⟩

def fits (S : Setup p) (γ : C(I, X)) : Prop :=
  ∀ n ∈ Finset.range S.n, MapsTo (IccExtendCM zero_le_one γ) (S.icc n) (S.T n).baseSet

abbrev Liftable (S : Setup p) := {γe : C(I, X) × E // S.fits γe.1 ∧ p γe.2 = γe.1 0}

def γn (γe : S.Liftable) (hn : n ∈ Finset.range S.n) : (S.T n).Γ (S.t n) (S.t (n + 1)) := by
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
  have h4 := (IccExtendCM zero_le_one).2.tendsto (γ y₀) |>.eventually key
  exact γ.2.tendsto y₀ |>.eventually h4

theorem fits.eventually_nhds (hS : S.fits γ) : ∀ᶠ δ in 𝓝 γ, S.fits δ := by
  let Γ : C(C(I, X), C(I, X)) := ⟨fun γ => γ, by fun_prop⟩
  exact hS.eventually (γ := Γ)

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
  continuous_toFun := Continuous.subtype_mk (continuous_comp _) _
  continuous_invFun := ContinuousMap.continuous_toFun _

def restrict_range {α β : Type*} {s : Set β} [TopologicalSpace α] [TopologicalSpace β]
    [LocallyCompactPair α β] : C(α, s) ≃ₜ {f : C(α, β) // range f ⊆ s} := by
  convert restrict_prop (α := α) (p := fun b => b ∈ s) <;> exact range_subset_iff

noncomputable def LiftWithin_partialCM (hn : n ≤ S.n) :
    {F : C(S.Liftable, C(Icc (S.t 0) (S.t n), E)) // ∀ γe,
      F γe ⟨S.t 0, left_mem_Icc.mpr (S.ht (by omega))⟩ = γe.1.2 ∧
      ∀ t, p (F γe t) = γe.1.1 (S.inj t)} := by
  induction n with
  | zero =>
    refine ⟨?_, ?_⟩
    · apply ContinuousMap.const'.comp ⟨fun ye => ye.1.2, by fun_prop⟩
    · simp ; rintro γ e - he t rfl ; exact he
  | succ n ih =>
    specialize ih (by omega)
    have h4 : S.t 0 ≤ S.t n := S.ht (by omega)
    have h7 : S.t n ≤ S.t (n + 1) := S.ht (by omega)
    refine ⟨?_, ?_⟩
    · have h2 : S.t n ∈ Icc (S.t 0) (S.t (n + 1)) := by constructor <;> apply S.ht <;> omega
      have h3 : n ∈ Finset.range S.n := by simp ; omega
      refine (concatCM h2).comp ⟨?_, ?_⟩
      · intro γe
        let left : C(↑(Icc (S.t 0) (S.t n)), E) := ih.1 γe
        let next : C(S.icc n, E) := by
          have h8 : S.t n ∈ Icc (S.t 0) (S.t n) := right_mem_Icc.mpr h4
          have h5 : p (ih.1 γe ⟨S.t n, _⟩) = γe.1.1 ⟨S.t n, _⟩ := (ih.2 γe).2 ⟨S.t n, h8⟩
          have h6 : S.t n ∈ S.icc n := Setup.left_mem
          refine .comp ⟨_, continuous_subtype_val⟩ <| (S.T n).clift (⟨lastval h4 left, ?_⟩, S.γn γe h3)
          simpa [lastval, Trivialization.mem_source, h5, Setup.subset h6] using γe.2.1 n h3 h6
        have : lastval h4 left = firstval h7 next := by
          simp [lastval, firstval, next]
          rw [Trivialization.clift_left h7]
          simp [ih.2] ; rfl
        exact ⟨⟨left, next⟩, this⟩
      · refine Continuous.subtype_mk (continuous_prod_mk.2 ⟨by fun_prop, ?_⟩) _
        apply ContinuousMap.continuous_comp _ |>.comp
        apply (S.T n).clift.continuous.comp
        refine continuous_prod_mk.2 ⟨by fun_prop, ?_⟩
        · let Ψ : C(S.Liftable × S.icc n, C(I, X) × I) :=
            ⟨fun fx => (fx.1.1.1, ⟨fx.2.1, Setup.subset fx.2.2⟩), by fun_prop⟩
          let Φ : C(S.Liftable × S.icc n, (S.T n).baseSet) := by
            refine ⟨fun fx => ⟨fx.1.1.1 ⟨fx.2.1, Setup.subset fx.2.2⟩, ?_⟩, ?_⟩
            · obtain ⟨_, _⟩ := Setup.subset fx.2.2
              have := fx.1.2.1 n h3 fx.2.2
              rw [IccExtendCM_of_mem] at this ; assumption
            · apply Continuous.subtype_mk
              exact ContinuousMap.continuous_eval.comp Ψ.continuous
          exact Φ.curry.continuous
    · rintro ⟨⟨γ, e⟩, hγ, he⟩ ; dsimp ; constructor
      · rw [concatCM_left h4] ; exact ih.2 ⟨⟨γ, e⟩, hγ, he⟩ |>.1
      · rintro ⟨t, ht⟩
        by_cases htn : t ≤ S.t n
        · rw [concatCM_left htn] ; exact ih.2 ⟨⟨γ, e⟩, hγ, he⟩ |>.2 ⟨t, _⟩
        · rw [concatCM_right <| le_of_not_le htn] ; simp ; rfl

noncomputable def LiftWithin_CM :
    {F : C(S.Liftable, C(I, E)) // ∀ γe, F γe 0 = γe.1.2 ∧ ∀ t, p (F γe t) = γe.1.1 t} := by
  obtain ⟨F, hF⟩ := LiftWithin_partialCM (S := S) le_rfl
  let Φ : C(I, Icc (S.t 0) (S.t S.n)) := ⟨fun t => ⟨t, by simp⟩, by fun_prop⟩
  refine ⟨⟨fun γe => (F γe).comp Φ, by fun_prop⟩, fun γe => ⟨?_, fun t => ?_⟩⟩
  · simpa using hF γe |>.1
  · simpa [Setup.inj, Φ] using hF γe |>.2 (Φ t)

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
