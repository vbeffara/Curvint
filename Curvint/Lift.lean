import Mathlib

open Set Topology Metric unitInterval Filter ContinuousMap

namespace ContinuousMap

variable
  {α : Type*} [LinearOrder α] [TopologicalSpace α] [OrderTopology α] {a b c : α}
  {E : Type*} [TopologicalSpace E]

def firstval (hab : a ≤ b) (f : C(Icc a b, E)) : E := f ⟨a, left_mem_Icc.2 hab⟩

def lastval (hab : a ≤ b) (f : C(Icc a b, E)) : E := f ⟨b, right_mem_Icc.2 hab⟩

noncomputable def concat (h : b ∈ Icc a c) (f : C(Icc a b, E)) (g : C(Icc b c, E)) :
    C(Icc a c, E) := by
  by_cases hb : f.lastval h.1 = g.firstval h.2
  · let h (t : α) : E := if t ≤ b then IccExtend h.1 f t else IccExtend h.2 g t
    suffices Continuous h from ⟨fun t => h t, by fun_prop⟩
    apply Continuous.if_le (by fun_prop) (by fun_prop) continuous_id continuous_const
    rintro x rfl ; simpa
  · exact .const _ (f ⟨a, left_mem_Icc.mpr h.1⟩)

@[simp] theorem concat_left {f : C(Icc a b, E)} {g : C(Icc b c, E)} (h : b ∈ Icc a c)
    (hb : f.lastval h.1 = g.firstval h.2) {t : Icc a c} (ht : t ≤ b) :
    concat h f g t = f ⟨t, t.2.1, ht⟩ := by
  simp [concat, hb, ht, IccExtend_apply, t.2.1]

@[simp] theorem concat_right {f : C(Icc a b, E)} {g : C(Icc b c, E)} (h : b ∈ Icc a c)
    (hb : f.lastval h.1 = g.firstval h.2) {t : Icc a c} (ht : b ≤ t) :
    concat h f g t = g ⟨t, ht, t.2.2⟩ := by
  simp [concat, hb, ht, IccExtend_apply, t.2.2, h.1]
  intro ht' ; have : b = t := le_antisymm ht ht' ; simpa [← this]

end ContinuousMap

variable
  {E X Z: Type*} [TopologicalSpace E] [TopologicalSpace X] [TopologicalSpace Z]
  {p : E → X} {γ : C(I, X)} {x x₀ : X} {e₀ : E}

namespace Trivialization

def lift (T : Trivialization Z p) (e : E) (x : X) : E := T.invFun (x, (T e).2)

@[simp] theorem lift_self (T : Trivialization Z p) (e : E) (hx : p e ∈ T.baseSet) :
    T.lift e (p e) = e := by
  simp [lift] ; rw [symm_apply_mk_proj] ; rwa [mem_source]

@[simp] theorem lift_proj (T : Trivialization Z p) (e : E) (x : X) (hx : x ∈ T.baseSet) :
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
  t : ℕ → I
  n : ℕ
  --
  ht : Monotone t
  ht0 : t 0 = 0
  ht1 : ∀ m ≥ n, t m = 1
  --
  c : ℕ → X
  T (n : ℕ) : Trivialization (p ⁻¹' {c n}) p

namespace Setup

variable {S : Setup p} {n : ℕ}

theorem left_mem : S.t n ∈ Icc (S.t n) (S.t (n + 1)) := by simp ; apply S.ht ; simp

theorem right_mem : S.t (n + 1) ∈ Icc (S.t n) (S.t (n + 1)) := by simp ; apply S.ht ; simp

def chain (S : Setup p) (γ : C(I, X)) (e₀ : E) : ℕ → E
  | 0 => e₀
  | n + 1 => (S.T n).lift (S.chain γ e₀ n) (γ (S.t (n + 1)))

def fits (S : Setup p) (γ : C(I, X)) : Prop :=
  ∀ n ∈ Finset.Iic S.n, Set.Icc (S.t n) (S.t (n + 1)) ⊆ γ ⁻¹' (S.T n).baseSet

noncomputable def exist (hp : IsCoveringMap p) (γ : C(I, X)) : { S : Setup p // S.fits γ } := by
  let T (t : I) : Trivialization (p ⁻¹' {γ t}) p := Classical.choose (hp (γ t)).2
  let mem_T (t : I) : γ t ∈ (T t).baseSet := Classical.choose_spec (hp (γ t)).2
  let V (t : I) : Set I := γ ⁻¹' (T t).baseSet
  have h1 t : IsOpen (V t) := (T t).open_baseSet.preimage γ.continuous
  have h2 : univ ⊆ ⋃ t, V t := by intro t _ ; rw [mem_iUnion] ; use t ; apply mem_T
  have := exists_monotone_Icc_subset_open_cover_unitInterval h1 h2
  choose t ht0 ht ht1 c hc using this
  choose n ht1 using ht1
  exact ⟨⟨t, n, ht, ht0, ht1, fun n => γ (c n), fun n => T (c n)⟩, fun n _ => hc n⟩

namespace fits

theorem chain_proj (hS : S.fits γ) (he₀ : p e₀ = γ 0) (n : ℕ) (hn : n ∈ Finset.Iic S.n) :
    p (S.chain γ e₀ n) = γ (S.t n) := by
  cases n with
  | zero => simp [chain, he₀, S.ht0]
  | succ n =>
    have hn' : n ∈ Finset.Iic S.n := by simp at hn ⊢ ; omega
    apply Trivialization.lift_proj ; apply hS n hn' ; apply S.right_mem

def partial_map (hS : S.fits γ) (e₀ : E) (n : ℕ) (hn : n ∈ Finset.Iic S.n) :
    C(Icc (S.t n) (S.t (n + 1)), E) := by
  let f (t : (Icc (S.t n) (S.t (n + 1)))) : E := (S.T n).lift (S.chain γ e₀ n) (γ ↑t)
  have : Continuous f := by
    apply (S.T n).continuousOn_invFun.comp_continuous (by fun_prop)
    intro t ; rw [Trivialization.mem_target] ; exact hS n hn t.2
  exact ⟨f, this⟩

@[simp] theorem partial_map_left (hS : S.fits γ) (he₀ : p e₀ = γ 0) (n : ℕ) (hn : n ∈ Finset.Iic S.n) :
    hS.partial_map e₀ n hn ⟨_, left_mem⟩ = S.chain γ e₀ n := by
  have h1 := hS.chain_proj he₀ n hn
  simp [partial_map, ← h1] ; apply (S.T _).lift_self ; simp [h1] ; apply hS n hn ; apply S.left_mem

@[simp] theorem partial_map_right (hS : S.fits γ) (e₀ : E) (n : ℕ) (hn : n ∈ Finset.Iic S.n) :
    hS.partial_map e₀ n hn ⟨_, right_mem⟩ = S.chain γ e₀ (n + 1) := by
  simp [fits.partial_map] ; rfl

noncomputable def pmap (hS : S.fits γ) (he₀ : p e₀ = γ 0) :
    ∀ n ∈ Finset.Iic S.n,
      { f : C(Icc (S.t 0) (S.t n), E) // f.lastval (S.ht (Nat.zero_le n)) = S.chain γ e₀ n }
  | 0 => fun _ => ⟨.const _ e₀, by simp [lastval, chain]⟩
  | n + 1 => by
    intro hn1
    have hn : n ∈ Finset.Iic S.n := by simp at hn1 ⊢ ; omega
    let f := hS.pmap he₀ n hn
    have h1 : S.t 0 ≤ S.t n := by apply S.ht ; simp
    have h2 : S.t n ≤ S.t (n + 1) := by apply S.ht ; simp
    have h3 : lastval h1 ↑f = firstval h2 (hS.partial_map e₀ n hn) := by
      simpa [lastval, firstval, he₀] using f.prop
    let g := f.1.concat ⟨h1, h2⟩ (hS.partial_map e₀ n hn)
    have h4 : lastval (h1.trans h2) g = S.chain γ e₀ (n + 1) := by
      by_cases h : S.t (n + 1) ≤ S.t n
      · rw [lastval, concat_left _ h3]
        · have h1 : S.t n ≤ S.t (n + 1) := by apply S.ht ; simp
          have h2 : S.t (n + 1) = S.t n := le_antisymm h h1
          have h3 := hS.chain_proj he₀ n hn
          rw [chain] ; simp [h2, f.prop, ← h3]
          rw [(S.T _).lift_self] ; exact f.prop
          simp [h3] ; apply hS n hn ; apply S.left_mem
        · exact h
      · rw [lastval, concat_right _ h3]
        · simp
        · apply S.ht ; simp
    exact ⟨g, h4⟩

@[simp] theorem pmap_zero (hS : S.fits γ) (he₀ : p e₀ = γ 0) (n : ℕ) (hn : n ∈ Finset.Iic S.n) :
    (hS.pmap he₀ n hn).1 ⟨0, by simp [S.ht0]⟩ = e₀ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp [fits.pmap]
    rw [concat_left]
    · apply ih
    · simp [firstval]
      have : n ∈ Finset.Iic S.n := by (simp at hn ⊢ ; omega)
      rw [hS.pmap he₀ n this |>.2]
      rw [partial_map_left]
      exact he₀
    · simp


@[simp] theorem pmap_apply (hS : S.fits γ) (he₀ : p e₀ = γ 0) (n : ℕ) (hn : n ∈ Finset.Iic S.n)
    (t : Icc (S.t 0) (S.t n)) : p ((hS.pmap he₀ n hn).1 t) = γ t := by
  induction n with
  | zero => rcases t with ⟨t, ht⟩ ; simp [S.ht0] at ht ; subst ht ; simpa [pmap]
  | succ n ih =>
    simp [pmap] ; by_cases h : t ≤ S.t n
    · rw [concat_left]
      apply ih
      · -- TODO this is duplicated
        have : n ∈ Finset.Iic S.n := by (simp at hn ⊢ ; omega)
        simp [firstval]
        rw [hS.pmap he₀ n this |>.2]
        rw [partial_map_left]
        exact he₀
      · exact h
    · have : S.t n ≤ t := by simp at h ; exact h.le
      rw [concat_right _ _ this]
      · simp [fits.partial_map]
        apply Trivialization.lift_proj ; apply hS ; simp at hn ⊢ ; omega ; simp [this, t.2.2]
      · -- TODO this is duplicated
        have : n ∈ Finset.Iic S.n := by (simp at hn ⊢ ; omega)
        simp [firstval]
        rw [hS.pmap he₀ n this |>.2]
        rw [partial_map_left]
        exact he₀

noncomputable def map (hS : S.fits γ) (he₀ : p e₀ = γ 0) : C(I, E) := by
  have h1 (t : I) : t ∈ Icc (S.t 0) (S.t S.n) := by
    rcases t with ⟨t, ht0, ht1⟩
    simp [S.ht0, S.ht1]
    simpa using ht1
  let f (t : I) := (hS.pmap he₀ S.n (by simp)).1 ⟨t, h1 t⟩
  have h2 : Continuous f := by fun_prop
  exact ⟨f, h2⟩

@[simp] theorem map_zero (hS : S.fits γ) (he₀ : p e₀ = γ 0) : hS.map he₀ 0 = e₀ := by
  simp [map]

@[simp] theorem map_apply (hS : S.fits γ) (he₀ : p e₀ = γ 0) (t : I) : p (hS.map he₀ t) = γ t := by
  simp [fits.map]

@[simp] theorem map_comp (hS : S.fits γ) (he₀ : p e₀ = γ 0) : p ∘ hS.map he₀ = γ := by ext t ; simp

end fits

end Setup

theorem Lift (hp : IsCoveringMap p) (he₀ : p e₀ = γ 0) : ∃! Γ : C(I, E), Γ 0 = e₀ ∧ p ∘ Γ = γ := by
  obtain ⟨S, hS⟩ := Setup.exist hp γ
  refine ⟨hS.map he₀, by simp, fun Γ hΓ => ?_⟩
  apply hp.lift_unique <;> simp [hΓ]

#print axioms Lift

section HomotopyLift

variable {Y : Type*} [TopologicalSpace Y]

def fiber (γ : C(I × Y, X)) : C(Y, C(I, X)) := γ.comp prodSwap |>.curry

def square [LocallyCompactSpace Y] (γ : C(I, C(Y, X))) : C(I × Y, X) := γ.uncurry

instance toto : CompactIccSpace I := ⟨fun {_ _} => isClosed_Icc.isCompact⟩

theorem eventually_fits (γ : C(Y, C(I, X))) (S : Setup p) (y₀ : Y) (hS : S.fits (γ y₀)) :
    ∀ᶠ y in 𝓝 y₀, S.fits (γ y) := by
  simp only [Setup.fits, eventually_all_finset] at hS ⊢
  peel hS with n hn hS
  have h1 : IsCompact (Icc (S.t n) (S.t (n + 1))) := CompactIccSpace.isCompact_Icc
  have h2 : IsOpen (S.T n).baseSet := (S.T n).open_baseSet
  exact γ.2.tendsto y₀ <| ContinuousMap.eventually_mapsTo h1 h2 hS

noncomputable def fiber_lift (hp : IsCoveringMap p) (γ : C(Y, C(I , X))) (Γ₀ : Y → E)
    (hΓ₀ : ∀ y, p (Γ₀ y) = γ y 0) (y : Y) : C(I, E) :=
  (Lift hp (hΓ₀ y)).choose

noncomputable def fiber_map (S : Setup p) (γ : C(Y, C(I , X))) (Γ₀ : Y → E)
    (hΓ₀ : ∀ y, p (Γ₀ y) = γ y 0) (y : Y) (hS : S.fits (γ y)) : C(I, E) :=
  hS.map (hΓ₀ y)

theorem map_eq_lift (hp : IsCoveringMap p) (γ : C(Y, C(I , X))) (Γ₀ : Y → E)
    (hΓ₀ : ∀ y, p (Γ₀ y) = γ y 0) (y : Y) (S : Setup p) (hS : S.fits (γ y)) :
    fiber_map S γ Γ₀ hΓ₀ y hS = fiber_lift hp γ Γ₀ hΓ₀ y :=
  (Lift hp (hΓ₀ y)).choose_spec.2 _ ⟨hS.map_zero (hΓ₀ y), hS.map_comp (hΓ₀ y)⟩

noncomputable def fiber_partial_map (S : Setup p) (γ : C(Y, C(I , X))) (Γ₀ : Y → E)
    (hΓ₀ : ∀ y, p (Γ₀ y) = γ y 0) (y : {y // S.fits (γ y)}) : C(I, E) :=
  fiber_map S γ Γ₀ hΓ₀ y y.2

theorem continuous_fiber_partial_map (S : Setup p) (γ : C(Y, C(I , X))) (Γ₀ : Y → E)
    (hΓ₀ : ∀ y, p (Γ₀ y) = γ y 0) : Continuous (fiber_partial_map S γ Γ₀ hΓ₀) := by
  rw [continuous_iff_continuousAt] ; intro y
  unfold fiber_partial_map fiber_map Setup.fits.map
  sorry

end HomotopyLift
