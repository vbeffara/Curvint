import Mathlib

open Set Topology Metric unitInterval Filter ContinuousMap

namespace ContinuousMap

variable
  {α : Type*} [LinearOrder α] [TopologicalSpace α] [OrderTopology α] {a b c : α}
  {E : Type*} [TopologicalSpace E]

def firstval (hab : a ≤ b) (f : C(Icc a b, E)) : E := f ⟨a, left_mem_Icc.2 hab⟩

def lastval (hab : a ≤ b) (f : C(Icc a b, E)) : E := f ⟨b, right_mem_Icc.2 hab⟩

noncomputable def concat (hab : a ≤ b) (hbc : b ≤ c) (f : C(Icc a b, E)) (g : C(Icc b c, E))
    (hb : f.lastval hab = g.firstval hbc) : C(Icc a c, E) := by
  let h (t : α) : E := if t ≤ b then IccExtend hab f t else IccExtend hbc g t
  suffices Continuous h from ⟨fun t => h t, by fun_prop⟩
  apply Continuous.if_le (by fun_prop) (by fun_prop) continuous_id continuous_const
  rintro x rfl ; simpa

@[simp] theorem concat_left (hab : a ≤ b) (hbc : b ≤ c) {f : C(Icc a b, E)} {g : C(Icc b c, E)}
    (hb : f.lastval hab = g.firstval hbc) {t : Icc a c} (ht : t ≤ b) :
    concat hab hbc f g hb t = f ⟨t, t.2.1, ht⟩ := by
  simp [concat, ht, IccExtend_apply, t.2.1]

@[simp] theorem concat_right (hab : a ≤ b) (hbc : b ≤ c) {f : C(Icc a b, E)} {g : C(Icc b c, E)}
    (hb : f.lastval hab = g.firstval hbc) {t : Icc a c} (ht : b ≤ t) :
    concat hab hbc f g hb t = g ⟨t, ht, t.2.2⟩ := by
  simp [concat, ht, IccExtend_apply, t.2.2, hab]
  intro ht' ; have : b = t := le_antisymm ht ht' ; simpa [← this]

end ContinuousMap

variable {E X α : Type*} [TopologicalSpace E] [TopologicalSpace X] {p : E → X} {γ : C(I, X)} {x : X}{e₀ : E}

namespace IsCoveringMap

noncomputable def T (hp : IsCoveringMap p) (x : X) : Trivialization (p ⁻¹' {x}) p :=
  Classical.choose (hp x).2

theorem mem_T (hp : IsCoveringMap p) (x : X) : x ∈ (hp.T x).baseSet :=
  Classical.choose_spec (hp x).2

-- the value at `x` of the `x₀`-sheat passing through `e₀`
noncomputable def plift' (hp : IsCoveringMap p) (x₀ : X) (e : E) (x : X) : E :=
  let T := hp.T x₀ ; T.invFun (x, (T e).2)

@[simp] theorem plift'_self (hp : IsCoveringMap p) (x₀ : X) (e : E) (hx : p e ∈ (hp.T x₀).baseSet) :
    hp.plift' x₀ e (p e) = e := by
  simp [plift'] ; rw [Trivialization.symm_apply_mk_proj] ; rwa [Trivialization.mem_source]

@[simp] theorem plift'_proj (hp : IsCoveringMap p) (x₀ : X) (e : E) (x : X) (hx : x ∈ (hp.T x₀).baseSet) :
    p (hp.plift' x₀ e x) = x := by
  simp [plift'] ; apply Trivialization.proj_symm_apply ; rwa [Trivialization.mem_target]

theorem eq_of_comp_eq' (hp : IsCoveringMap p) {A : Type*} [TopologicalSpace A] [PreconnectedSpace A]
    {g₁ g₂ : C(A, E)} (he : p ∘ g₁ = p ∘ g₂) (a : A) (ha : g₁ a = g₂ a) : g₁ = g₂ :=
  ContinuousMap.ext (congrFun <| hp.eq_of_comp_eq g₁.continuous_toFun g₂.continuous_toFun he a ha)

theorem lift_unique (hp : IsCoveringMap p) {Γ₁ Γ₂ : C(I, E)} (h0 : Γ₁ 0 = Γ₂ 0)
    (h : p ∘ Γ₁ = p ∘ Γ₂) : Γ₁ = Γ₂ := by
  exact hp.eq_of_comp_eq' h 0 h0

end IsCoveringMap

structure Setup (p : E → X) where
  t : ℕ → I
  c : ℕ → I
  n : ℕ
  --
  ht : Monotone t
  ht0 : t 0 = 0
  ht1 : ∀ m ≥ n, t m = 1
  --
  hp : IsCoveringMap p

namespace Setup

variable {S : Setup p} {n : ℕ}

theorem left_mem : S.t n ∈ Icc (S.t n) (S.t (n + 1)) := by
  apply left_mem_Icc.mpr ; apply S.ht ; simp

theorem right_mem : S.t (n + 1) ∈ Icc (S.t n) (S.t (n + 1)) := by
  apply right_mem_Icc.mpr ; apply S.ht ; simp

noncomputable def chain (S : Setup p) (γ : C(I, X)) (e₀ : E) : ℕ → E
  | 0 => e₀
  | n + 1 => S.hp.plift' (γ (S.c n)) (S.chain γ e₀ n) (γ (S.t (n + 1)))

def fits (S : Setup p) (γ : C(I, X)) : Prop :=
  ∀ n, Set.Icc (S.t n) (S.t (n + 1)) ⊆ γ ⁻¹' (S.hp.T (γ (S.c n))).baseSet

noncomputable def exist (hp : IsCoveringMap p) (γ : C(I, X)) : { S : Setup p // S.fits γ } := by
  let V (t : I) : Set I := γ ⁻¹' (hp.T (γ t)).baseSet
  have h1 t : IsOpen (V t) := (hp.T (γ t)).open_baseSet.preimage γ.continuous
  have h2 : univ ⊆ ⋃ t, V t := by intro t _ ; rw [mem_iUnion] ; use t ; apply hp.mem_T
  have := exists_monotone_Icc_subset_open_cover_unitInterval h1 h2
  choose t ht0 ht ht1 c hc using this
  choose n ht1 using ht1
  refine ⟨⟨t, c, n, ht, ht0, ht1, hp⟩, hc⟩

theorem fits.chain_proj (hS : S.fits γ) (he₀ : p e₀ = γ 0) (n : ℕ) :
    p (S.chain γ e₀ n) = γ (S.t n) := by
  cases n with
  | zero => simp [chain, he₀, S.ht0]
  | succ n => apply IsCoveringMap.plift'_proj ; apply hS n ; apply S.right_mem

noncomputable def fits.partial_map (hS : S.fits γ) (e₀ : E) (n : ℕ) :
    C(Icc (S.t n) (S.t (n + 1)), E) := by
  refine ⟨fun t => S.hp.plift' (γ (S.c n)) (S.chain γ e₀ n) (γ t), ?_⟩
  apply (S.hp.T (γ (S.c n))).continuousOn_invFun.comp_continuous (by fun_prop)
  intro t ; rw [Trivialization.mem_target] ; exact hS n t.2

theorem fits.partial_map_left (hS : S.fits γ) (he₀ : p e₀ = γ 0) (n : ℕ) :
    hS.partial_map e₀ n ⟨_, left_mem⟩ = S.chain γ e₀ n := by
  have h1 := hS.chain_proj he₀ n
  simp [partial_map, ← h1] ; apply S.hp.plift'_self ; simp [h1] ; apply hS ; apply S.left_mem

theorem fits.partial_map_right (hS : S.fits γ) (e₀ : E) (n : ℕ) :
    hS.partial_map e₀ n ⟨_, right_mem⟩ = S.chain γ e₀ (n + 1) := by
  simp [fits.partial_map] ; rfl

noncomputable def fits.pmap (hS : S.fits γ) (he₀ : p e₀ = γ 0) :
    ∀ n : ℕ, { f : C(Icc (S.t 0) (S.t n), E) //
      f ⟨S.t n, right_mem_Icc.mpr (S.ht (Nat.zero_le n))⟩ = S.chain γ e₀ n }
  | 0 => ⟨.const _ e₀, by simp [chain]⟩
  | n + 1 => by
    let f := hS.pmap he₀ n
    refine ⟨f.1.concat ?_ ?_ (hS.partial_map e₀ n) ?_, ?_⟩
    · apply S.ht ; simp
    · apply S.ht ; simp
    · simp [lastval, firstval, f.prop, hS.partial_map_left he₀]
    · by_cases h : S.t (n + 1) ≤ S.t n
      · rw [concat_left]
        · have h1 : S.t n ≤ S.t (n + 1) := by apply S.ht ; simp
          have h2 : S.t (n + 1) = S.t n := le_antisymm h h1
          have h3 := hS.chain_proj he₀ n
          rw [chain] ; simp [h2, f.prop, ← h3]
          rw [S.hp.plift'_self]
          simp [h3]
          apply hS ; apply S.left_mem
        · exact h
      · rw [concat_right] ; simp [partial_map_right]
        simp at h ; exact h.le

@[simp] theorem fits.pmap_zero (hS : S.fits γ) (he₀ : p e₀ = γ 0) (n : ℕ) :
    (hS.pmap he₀ n).1 ⟨0, by { simp [S.ht0] }⟩ = e₀ := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [fits.pmap]

@[simp] theorem fits.pmap_apply (hS : S.fits γ) (he₀ : p e₀ = γ 0) (n : ℕ)
    (t : Icc (S.t 0) (S.t n)) : p ((hS.pmap he₀ n).1 t) = γ t := by
  induction n with
  | zero => rcases t with ⟨t, ht⟩ ; simp [S.ht0] at ht ; subst ht ; simpa [pmap]
  | succ n ih =>
    simp [pmap] ; by_cases h : t ≤ S.t n
    · rw [concat_left] ; apply ih ; exact h
    · have : S.t n ≤ t := by simp at h ; exact h.le
      rw [concat_right _ _ _ this]
      apply S.hp.plift'_proj ; apply hS ; simp [this, t.2.2]

noncomputable def fits.map (hS : S.fits γ) (he₀ : p e₀ = γ 0) : C(I, E) := by
  obtain ⟨f, -⟩ := hS.pmap he₀ S.n
  refine ⟨fun t => f ⟨t, ?_⟩, ?_⟩
  · rcases t with ⟨t, ht0, ht1⟩
    simp [S.ht0, S.ht1]
    simpa using ht1
  · fun_prop

@[simp] theorem fits.map_zero (hS : S.fits γ) (he₀ : p e₀ = γ 0) : hS.map he₀ 0 = e₀ := by
  simp [map]

@[simp] theorem fits.map_apply (hS : S.fits γ) (he₀ : p e₀ = γ 0) (t : I) : p (hS.map he₀ t) = γ t := by
  simp [fits.map]

@[simp] theorem fits.map_comp (hS : S.fits γ) (he₀ : p e₀ = γ 0) : p ∘ hS.map he₀ = γ := by
  ext t ; simp

end Setup

theorem Lift (hp : IsCoveringMap p) (he₀ : p e₀ = γ 0) : ∃! Γ : C(I, E), Γ 0 = e₀ ∧ p ∘ Γ = γ := by
  obtain ⟨S, hS⟩ := Setup.exist hp γ
  refine ⟨hS.map he₀, by simp, fun Γ hΓ => ?_⟩
  apply hp.lift_unique <;> simp [hΓ]
