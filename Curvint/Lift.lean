import Mathlib

open Set Topology Metric unitInterval Filter ContinuousMap

namespace ContinuousMap

variable
  {α : Type*} [LinearOrder α] [TopologicalSpace α] [OrderTopology α] {a b c : α}
  {E : Type*} [TopologicalSpace E]

def subset {s₁ s₂ : Set E} (h : s₁ ⊆ s₂) : C(s₁, s₂) := ⟨fun x => ⟨x.1, h x.2⟩, by fun_prop⟩

def subset_left (h : b ∈ Icc a c) : C(Icc a b, Icc a c) := subset (Icc_subset_Icc le_rfl h.2)

def subset_right (h : b ∈ Icc a c) : C(Icc b c, Icc a c) := subset (Icc_subset_Icc h.1 le_rfl)

def firstval (hab : a ≤ b) : C(C(Icc a b, E), E) := ⟨fun f => f ⟨a, le_rfl, hab⟩, by continuity⟩

def lastval (hab : a ≤ b) : C(C(Icc a b, E), E) := ⟨fun f => f ⟨b, hab, le_rfl⟩, by continuity⟩

def icce (hab : a ≤ b) : C(C(Icc a b, E), C(α, E)) where
  toFun f := f.comp ⟨projIcc a b hab, continuous_projIcc⟩
  continuous_toFun := continuous_comp_left _

noncomputable def concat (h : b ∈ Icc a c) (f : C(Icc a b, E)) (g : C(Icc b c, E)) : C(Icc a c, E) := by
  by_cases hb : lastval h.1 f = firstval h.2 g
  · let h (t : α) : E := if t ≤ b then icce h.1 f t else icce h.2 g t
    suffices Continuous h from ⟨fun t => h t, by fun_prop⟩
    apply Continuous.if_le (by fun_prop) (by fun_prop) continuous_id continuous_const
    rintro x rfl ; simpa [icce]
  · exact .const _ (firstval h.1 f) -- junk value

variable {f : C(Icc a b, E)} {g : C(Icc b c, E)}

theorem concat_comp_left (h : b ∈ Icc a c) (hb : lastval h.1 f = firstval h.2 g) :
    f = (concat h f g).comp (subset_left h) := by
  ext x ; simp [concat, icce, hb, subset_left, subset, x.2.2]

theorem concat_comp_right (h : b ∈ Icc a c) (hb : lastval h.1 f = firstval h.2 g) :
    g = (concat h f g).comp (subset_right h) := by
  ext x ; by_cases hxb : x = b
  · simp [concat, hb, subset_right, subset, hxb]
    simp [lastval, firstval] at hb ; simp [icce, hb] ; simp [← hxb]
  · have := lt_of_le_of_ne x.2.1 (Ne.symm hxb) |>.not_le
    simp [concat, hb, subset_right, subset, x.2.2, this, icce]

@[simp] theorem concat_left (h : b ∈ Icc a c) (hb : lastval h.1 f = firstval h.2 g)
    {t : Icc a c} (ht : t ≤ b) : concat h f g t = f ⟨t, t.2.1, ht⟩ := by
  nth_rewrite 2 [concat_comp_left h hb] ; rfl

@[simp] theorem concat_right (h : b ∈ Icc a c) (hb : lastval h.1 f = firstval h.2 g)
    {t : Icc a c} (ht : b ≤ t) : concat h f g t = g ⟨t, ht, t.2.2⟩ := by
  nth_rewrite 2 [concat_comp_right h hb] ; rfl

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

end ContinuousMap

variable
  {E X Z: Type*} [TopologicalSpace E] [TopologicalSpace X] [TopologicalSpace Z]
  {p : E → X} {γ : C(I, X)} {x x₀ : X} {e₀ : E}

namespace Trivialization

def lift (T : Trivialization Z p) (e : E) (x : X) : E := T.invFun (x, (T e).2)

@[simp] theorem lift_self (T : Trivialization Z p) (e : E) (hx : p e ∈ T.baseSet) :
    T.lift e (p e) = e := by
  simp [lift] ; rw [symm_apply_mk_proj] ; rwa [mem_source]

@[simp] theorem lift_proj (T : Trivialization Z p) (e : E) (hx : x ∈ T.baseSet) :
    p (T.lift e x) = x := by
  simp [lift] ; apply proj_symm_apply ; rwa [mem_target]

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

@[simp] theorem htn : S.t S.n = 1 := S.ht1 S.n le_rfl

@[simp] theorem mem_I : S.t n ∈ I := by
  refine ⟨?_, ?_⟩ <;> simp [← S.ht0, ← S.ht1 (n + S.n) (by omega)] <;> apply S.ht <;> omega

@[simp] theorem left_mem : S.t n ∈ Icc (S.t n) (S.t (n + 1)) := by simp ; apply S.ht ; simp

@[simp] theorem right_mem : S.t (n + 1) ∈ Icc (S.t n) (S.t (n + 1)) := by simp ; apply S.ht ; simp

@[simp] theorem subset : Icc (S.t m) (S.t n) ⊆ I := by
  rintro t ⟨ht0, ht1⟩ ; exact ⟨le_trans mem_I.1 ht0, le_trans ht1 mem_I.2⟩

def chain (S : Setup p) (γ : C(I, X)) (e₀ : E) : ℕ → E
  | 0 => e₀
  | n + 1 => (S.T n).lift (S.chain γ e₀ n) (γ ⟨S.t (n + 1), S.mem_I⟩)

def fits (S : Setup p) (γ : C(I, X)) : Prop :=
  ∀ n ∈ Finset.range S.n, MapsTo (icce zero_le_one γ) (Icc (S.t n) (S.t (n + 1))) (S.T n).baseSet

noncomputable def exist (hp : IsCoveringMap p) (γ : C(I, X)) : { S : Setup p // S.fits γ } := by
  let T (t : I) : Trivialization (p ⁻¹' {γ t}) p := Classical.choose (hp (γ t)).2
  let mem_T (t : I) : γ t ∈ (T t).baseSet := Classical.choose_spec (hp (γ t)).2
  let V (t : I) : Set I := γ ⁻¹' (T t).baseSet
  have h1 t : IsOpen (V t) := (T t).open_baseSet.preimage γ.continuous
  have h2 : univ ⊆ ⋃ t, V t := by intro t _ ; rw [mem_iUnion] ; use t ; apply mem_T
  have := exists_monotone_Icc_subset_open_cover_unitInterval h1 h2
  choose t ht0 ht ht1 c hc using this
  choose n ht1 using ht1
  refine ⟨⟨fun n => t n, n, ht, by simpa using ht0, by simpa using ht1, fun n => γ (c n), fun n => T (c n)⟩, ?_⟩
  rintro k - s hs
  simpa [icce, projIcc, (t k).2.1 |>.trans hs.1, hs.2.trans (t (k + 1)).2.2] using hc k hs

noncomputable def partial_map (S : Setup p) (γ : C(I, X)) (e₀ : E) (n : ℕ) :
    C(Icc (S.t n) (S.t (n + 1)), E) := by
  by_cases hn : n ∈ Finset.range S.n
  · by_cases hS : S.fits γ
    · let f (t : (Icc (S.t n) (S.t (n + 1)))) : E := by
        have := S.subset t.2
        exact (S.T n).lift (S.chain γ e₀ n) (γ ⟨t.1, S.subset t.2⟩)
      use f ; simp [autoParam]
      · apply (S.T n).continuousOn_invFun.comp_continuous (by fun_prop)
        intro t
        rw [Trivialization.mem_target]
        have htI := S.subset t.2
        simpa [icce, projIcc, htI.1, htI.2] using hS n hn t.2
    · exact .const _ (S.chain γ e₀ n)
  · exact .const _ (S.chain γ e₀ n)

noncomputable def pmap (S : Setup p) (γ : C(I, X)) (e₀ : E) : ∀ n, C(Icc (S.t 0) (S.t n), E)
  | 0 => .const _ e₀
  | n + 1 => concat ⟨S.ht (by omega), S.ht (by omega)⟩ (pmap S γ e₀ n) (S.partial_map γ e₀ n)

noncomputable def map (S : Setup p) (γ : C(I, X)) (e₀ : E) : C(I, E) := by
  have h1 (t : I) : t.1 ∈ Icc (S.t 0) (S.t S.n) := by
    rcases t with ⟨t, ht0, ht1⟩
    simp [*, S.ht0]
  let f (t : I) := S.pmap γ e₀ S.n ⟨t, h1 t⟩
  have h2 : Continuous f := by fun_prop
  exact ⟨f, h2⟩

namespace fits

theorem chain_proj (hS : S.fits γ) (he₀ : p e₀ = γ 0) (hn : n ≤ S.n):
    p (S.chain γ e₀ n) = γ ⟨S.t n, mem_I⟩ := by
  cases n with
  | zero => simp [chain, he₀, S.ht0]
  | succ n =>
    have hn : n ∈ Finset.range S.n := by simp ; omega
    apply Trivialization.lift_proj
    simpa [icce, projIcc, mem_I.1, mem_I.2] using hS n hn <| S.right_mem

@[simp] theorem partial_map_left (hS : S.fits γ) (he₀ : p e₀ = γ 0) (hn : n ∈ Finset.range S.n) :
    firstval (S.ht (by omega)) (partial_map S γ e₀ n) = S.chain γ e₀ n := by
  have h2 : n < S.n := by simpa using hn
  have h1 := hS.chain_proj he₀ h2.le
  simp [firstval, partial_map, ← h1, hS, h2]
  apply (S.T _).lift_self ; simp [h1]
  simpa [icce, projIcc, mem_I.1, mem_I.2] using hS n hn <| S.left_mem

@[simp] theorem partial_map_right (hS : S.fits γ) (e₀ : E) (hn : n ∈ Finset.range S.n) :
    partial_map S γ e₀ n ⟨_, right_mem⟩ = S.chain γ e₀ (n + 1) := by
  simp only [partial_map, hS, hn] ; rfl

@[simp] theorem pmap_last (hS : S.fits γ) (he₀ : p e₀ = γ 0) (hn : n ≤ S.n) :
    lastval (S.ht (by omega)) (pmap S γ e₀ n) = S.chain γ e₀ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hn' : n ∈ Finset.range S.n := by simp ; omega
    simp [lastval] ; rw [pmap, concat_right]
    · rw [partial_map_right] ; exact hS ; exact hn'
    · rw [ih, partial_map_left]
      · exact hS
      · exact he₀
      · exact hn'
      · omega
    · apply S.ht ; omega

@[simp] theorem pmap_first (hS : S.fits γ) (he₀ : p e₀ = γ 0) (hn : n ≤ S.n) :
    firstval (S.ht (by omega)) (pmap S γ e₀ n) = e₀ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hn' : n ∈ Finset.range S.n := by simp ; omega
    simp [firstval]
    rw [pmap, concat_left]
    · apply ih ; omega
    · rw [partial_map_left hS he₀ hn']
      rw [pmap_last hS he₀]
      omega
    · apply S.ht ; omega

@[simp] theorem pmap_apply (hS : S.fits γ) (he₀ : p e₀ = γ 0) (hn : n ≤ S.n)
    (t : Icc (S.t 0) (S.t n)) : p (pmap S γ e₀ n t) = γ ⟨t, S.subset t.2⟩ := by
  induction n with
  | zero => obtain ⟨t, ht⟩ := t ; simp [S.ht0] at ht ; simp [pmap, he₀, ht]
  | succ n ih =>
    have hn' : n ∈ Finset.range S.n := by simp ; omega
    simp [pmap]
    by_cases h : t ≤ S.t n
    · rw [concat_left]
      · apply ih (by omega)
      · rw [partial_map_left hS he₀ hn']
        rw [pmap_last hS he₀ (by omega)]
      · exact h
    · have : S.t n ≤ t := by simp at h ; exact h.le
      rw [concat_right _ _ this]
      · simp only [partial_map, hn']
        simp [partial_map, hS]
        apply Trivialization.lift_proj
        have htI := S.subset t.2
        simpa [icce, projIcc, htI.1, htI.2] using hS n hn' ⟨this, t.2.2⟩
      · rw [partial_map_left hS he₀ hn']
        rw [pmap_last hS he₀ (by omega)]

@[simp] theorem map_zero (hS : S.fits γ) (he₀ : p e₀ = γ 0) : S.map γ e₀ 0 = e₀ := by
  simpa [firstval, S.ht0] using pmap_first hS he₀ le_rfl

@[simp] theorem map_apply (hS : S.fits γ) (he₀ : p e₀ = γ 0) (t : I) : p (S.map γ e₀ t) = γ t := by
  simp [Setup.map, *]

@[simp] theorem map_comp (hS : S.fits γ) (he₀ : p e₀ = γ 0) : p ∘ (S.map γ e₀) = γ := by
  ext t ; simp [*]

theorem congr (hp : IsCoveringMap p) {S' : Setup p} (hS : S.fits γ) (hS' : S'.fits γ) (he₀ : p e₀ = γ 0) :
    S.map γ e₀ = S'.map γ e₀ := by
  apply hp.lift_unique <;> simp [hS, hS', he₀]

end fits

end Setup

theorem Lift (hp : IsCoveringMap p) (he₀ : p e₀ = γ 0) : ∃! Γ : C(I, E), Γ 0 = e₀ ∧ p ∘ Γ = γ := by
  obtain ⟨S, hS⟩ := Setup.exist hp γ
  refine ⟨S.map γ e₀, ?_, fun Γ hΓ => ?_⟩
  · simp [*]
  · apply hp.lift_unique <;> simp [hΓ, *]

#print axioms Lift

section HomotopyLift

variable {Y : Type*} [TopologicalSpace Y] {γ : C(Y, C(I , X))} {Γ₀ : Y → E} {y₀ y : Y} {t : I}

def fiber (γ : C(I × Y, X)) : C(Y, C(I, X)) := γ.comp prodSwap |>.curry

def square [LocallyCompactSpace Y] (γ : C(I, C(Y, X))) : C(I × Y, X) := γ.uncurry

instance toto : CompactIccSpace I := ⟨fun {_ _} => isClosed_Icc.isCompact⟩

theorem eventually_fits {S : Setup p} (hS : S.fits (γ y₀)) : ∀ᶠ y in 𝓝 y₀, S.fits (γ y) := by
  let icce01 := @ContinuousMap.icce ℝ _ _ _ 0 1 X _ zero_le_one
  simp only [Setup.fits, eventually_all_finset] at hS ⊢
  peel hS with n hn hS
  have key := ContinuousMap.eventually_mapsTo CompactIccSpace.isCompact_Icc (S.T n).open_baseSet hS
  have h4 := icce01.2.tendsto (γ y₀) |>.eventually key
  exact γ.2.tendsto y₀ |>.eventually h4

variable (hp : IsCoveringMap p)

noncomputable def Lift_at (γ : C(Y, C(I , X))) (Γ₀ : Y → E) (y₀ : Y) : C(I, E) := by
  exact (Setup.exist hp (γ y₀)).1.map (γ y₀) (Γ₀ y₀)

noncomputable def Lift_around (γ : C(Y, C(I , X))) (Γ₀ : Y → E) (y₀ y : Y) :
    C(I, E) := by
  obtain ⟨S, -⟩ := Setup.exist hp (γ y₀)
  exact S.map (γ y) (Γ₀ y)

theorem Lift_around_eq (γ : C(Y, C(I , X))) (y₀ : Y) :
    Lift_around hp γ Γ₀ y₀ y₀ = Lift_at hp γ Γ₀ y₀ := rfl

variable (hΓ₀ : ∀ y, p (Γ₀ y) = γ y 0)
include hΓ₀

@[simp] theorem Lift_at_first : (Lift_at hp γ Γ₀ y₀) 0 = Γ₀ y₀ :=
  (Setup.exist hp (γ y₀)).2.map_zero (hΓ₀ y₀)

@[simp] theorem Lift_at_apply : p ((Lift_at hp γ Γ₀ y₀) t) = (γ y₀) t :=
  (Setup.exist hp (γ y₀)).2.map_apply (hΓ₀ y₀) t

@[simp] theorem Lift_at_comp : p ∘ Lift_at hp γ Γ₀ y = γ y := by ext t ; simp [hΓ₀]

theorem continuousAt_pmap {S : Setup p} (hS : S.fits (γ y₀)) {n : ℕ} (hn : n ≤ S.n) :
    ContinuousAt (fun y ↦ (S.pmap (γ y) (Γ₀ y) S.n)) y₀ :=
  sorry

theorem Lift_around_continuous : ContinuousAt (Lift_around hp γ Γ₀ y₀) y₀ := by
  let S := Setup.exist hp (γ y₀)
  change ContinuousAt (fun y => S.1.map (γ y) (Γ₀ y)) y₀
  simp [Setup.map]
  let Ψ := (fun y ↦ S.1.pmap (γ y) (Γ₀ y) S.1.n)
  let Φ := Homeomorph.Set.univ I
  have : ContinuousAt Ψ y₀ := continuousAt_pmap hΓ₀ S.2 le_rfl
  sorry

theorem Lift_around_nhds : Lift_around hp γ Γ₀ y₀ =ᶠ[𝓝 y₀] Lift_at hp γ Γ₀ := by
  filter_upwards [eventually_fits (Setup.exist hp (γ y₀)).2] with y hS
  apply hp.lift_unique
  · simpa [hΓ₀] using hS.map_zero (hΓ₀ y)
  · simpa [hΓ₀] using hS.map_comp (hΓ₀ y)

theorem continuous_LiftAt : Continuous (Lift_at hp γ Γ₀) := by
  rw [continuous_iff_continuousAt] ; intro y
  apply Lift_around_continuous (y₀ := y) hp hΓ₀ |>.congr
  exact (Lift_around_nhds hp hΓ₀)

theorem HomotopyLift_backwards (hp : IsCoveringMap p) :
    ∃! Γ : C(Y, C(I, E)), ∀ y, Γ y 0 = Γ₀ y ∧ p ∘ (Γ y) = γ y := by
  refine ⟨⟨Lift_at hp γ Γ₀, continuous_LiftAt hp hΓ₀⟩, by simp [*], ?_⟩
  intro Γ' hΓ' ; ext1 y
  apply hp.lift_unique <;> simp [hp, hΓ₀, hΓ']

end HomotopyLift
