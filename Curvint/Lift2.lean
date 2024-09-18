import Mathlib

open Set Topology Metric unitInterval Filter ContinuousMap

variable {E X α : Type*} [TopologicalSpace E] [TopologicalSpace X] {p : E → X} {γ : C(I, X)} {e : E}

namespace ContinuousMap

variable {a b c : I}

noncomputable def concat (hab : a ≤ b) (hbc : b ≤ c) (f : C(Icc a b, E)) (g : C(Icc b c, E))
    (hb : f ⟨b, right_mem_Icc.2 hab⟩ = g ⟨b, left_mem_Icc.2 hbc⟩) : C(Icc a c, E) := by
  refine ⟨fun t => if t ≤ b then IccExtend hab f t else IccExtend hbc g t, ?_⟩
  suffices Continuous fun t ↦ if t ≤ b then (IccExtend hab f) t else (IccExtend hbc g) t from
    this.comp continuous_subtype_val
  refine Continuous.if_le ?_ ?_ continuous_id continuous_const ?_
  exact ContinuousMap.continuous (IccExtend hab f)
  exact ContinuousMap.continuous (IccExtend hbc g)
  rintro x rfl ; simpa

theorem concat_left (hab : a ≤ b) (hbc : b ≤ c) (f : C(Icc a b, E)) (g : C(Icc b c, E))
    (hb : f ⟨b, right_mem_Icc.2 hab⟩ = g ⟨b, left_mem_Icc.2 hbc⟩) (t : Icc a c) (ht : t ≤ b) :
    concat hab hbc f g hb t = f ⟨t, t.2.1, ht⟩ := by
  simp [concat, ht, IccExtend_apply, t.2.1]

end ContinuousMap

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
  let T := hp.T x₀
  simp [plift']
  rw [T.symm_apply_mk_proj]
  apply T.mem_source.mpr hx

@[simp] theorem plift'_proj (hp : IsCoveringMap p) (x₀ : X) (e : E) (x : X) (hx : x ∈ (hp.T x₀).baseSet) :
    p (hp.plift' x₀ e x) = x := by
  simp [plift']
  let T := hp.T x₀
  exact T.proj_symm_apply <| T.mem_target.mpr hx

end IsCoveringMap

structure Setup (p : E → X) (γ : C(I, X)) where
  t : ℕ → I
  c : ℕ → I
  n : ℕ
  --
  ht : Monotone t
  ht0 : t 0 = 0
  ht1 : ∀ m ≥ n, t m = 1
  --
  hp : IsCoveringMap p
  hc : ∀ n, Set.Icc (t n) (t (n + 1)) ⊆ γ ⁻¹' (hp.T (γ (c n))).baseSet

namespace Setup

theorem left_mem (S : Setup p γ) (n : ℕ) : S.t n ∈ Icc (S.t n) (S.t (n + 1)) := by
  apply left_mem_Icc.mpr ; apply S.ht ; simp

theorem right_mem (S : Setup p γ) (n : ℕ) : S.t (n + 1) ∈ Icc (S.t n) (S.t (n + 1)) := by
  apply right_mem_Icc.mpr ; apply S.ht ; simp

noncomputable def exist (hp : IsCoveringMap p) : Setup p γ := by
  let V (t : I) : Set I := γ ⁻¹' (hp.T (γ t)).baseSet
  have h1 t : IsOpen (V t) := (hp.T (γ t)).open_baseSet.preimage γ.continuous
  have h2 : univ ⊆ ⋃ t, V t := by intro t _ ; rw [mem_iUnion] ; use t ; apply hp.mem_T
  have := exists_monotone_Icc_subset_open_cover_unitInterval h1 h2
  choose t ht0 ht ht1 c hc using this
  choose n ht1 using ht1
  refine ⟨t, c, n, ht, ht0, ht1, hp, hc⟩

theorem covers (S : Setup p γ) : ⋃ n, Set.Icc (S.t n) (S.t (n + 1)) = univ := by
  rw [eq_univ_iff_forall]
  intro t ; by_cases h : t = 0
  · simp [h] ; use 0 ; exact S.ht0
  have h0 : 0 < t := by apply lt_of_le_of_ne t.prop.1 ; symm ; contrapose! h ; simpa using h
  have h1 : t ∈ Ioc (0 : I) 1 := by simp [h0] ; exact t.prop.2
  have h2 := S.ht.biUnion_Ico_Ioc_map_succ 0 S.n
  simp [S.ht1 S.n le_rfl, S.ht0] at h2 ; rw [← h2, mem_iUnion₂] at h1
  obtain ⟨i, -, hhi⟩ := h1
  rw [mem_iUnion] ; use i ; apply Ioc_subset_Icc_self ; exact hhi

noncomputable def chain (S : Setup p γ) (e₀ : E) : ℕ → E
  | 0 => e₀
  | n + 1 => S.hp.plift' (γ (S.c n)) (chain S e₀ n) (γ (S.t (n + 1)))

theorem chain_proj (S : Setup p γ) (e₀ : E) (he₀ : p e₀ = γ 0) (n : ℕ) : p (S.chain e₀ n) = γ (S.t n) := by
  cases n with
  | zero => simp [chain, he₀, S.ht0]
  | succ n => apply IsCoveringMap.plift'_proj ; apply S.hc n ; apply right_mem_Icc.mpr ; apply S.ht ; simp

noncomputable def partial_map (S : Setup p γ) (e₀ : E) (n : ℕ) :
    C(Icc (S.t n) (S.t (n + 1)), E) := by
  refine ⟨fun t => S.hp.plift' (γ (S.c n)) (S.chain e₀ n) (γ t), ?_⟩
  apply (S.hp.T (γ (S.c n))).continuousOn_invFun.comp_continuous (by fun_prop)
  intro t ; rw [Trivialization.mem_target] ; exact S.hc n t.2

theorem partial_map_left (S : Setup p γ) (e₀ : E) (he₀ : p e₀ = γ 0) (n : ℕ) :
    S.partial_map e₀ n ⟨_, S.left_mem _⟩ = S.chain e₀ n := by
  have h1 := S.chain_proj e₀ he₀ n
  simp [partial_map, ← h1] ; apply S.hp.plift'_self ; simp [h1] ; apply S.hc ; apply left_mem_Icc.mpr
  apply S.ht ; simp

theorem partial_map_right (S : Setup p γ) (e₀ : E) (n : ℕ) :
    S.partial_map e₀ n ⟨_, S.right_mem _⟩ = S.chain e₀ (n + 1) := by
  simp [partial_map] ; rfl

theorem compat (S : Setup p γ) (e₀ : E) (he₀ : p e₀ = γ 0) (n : ℕ) :
    S.partial_map e₀ n ⟨_, S.right_mem _⟩ = S.partial_map e₀ (n + 1) ⟨_, S.left_mem _⟩ := by
  rw [partial_map_left, partial_map_right] ; assumption

noncomputable def pmap (S : Setup p γ) (e₀ : E) : ∀ n : ℕ, C(Icc (S.t 0) (S.t n), E)
  | 0 => .const _ e₀
  | n + 1 => by
    let fn := pmap S e₀ n
    apply fn.concat
    · sorry
    · sorry
    · sorry
    · sorry

noncomputable def map (S : Setup p γ) (e₀ : E) (t : I) : E := by
  have h1 : ∃ n, t ∈ Icc (S.t n) (S.t (n + 1)) := by
    have := S.covers ; simp only [eq_univ_iff_forall] at this ; exact mem_iUnion.mp (this t)
  let n := Nat.find h1
  exact S.hp.plift' (γ (S.c n)) (S.chain e₀ n) (γ t)

end Setup

theorem Lift (hp : IsCoveringMap p) (he : p e = γ 0) :
    ∃! Γ : C(I, E), Γ 0 = e ∧ p ∘ Γ = γ := by
  let S : Setup p γ := Setup.exist hp
  sorry
