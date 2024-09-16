import Mathlib

open Set Topology Metric unitInterval Filter ContinuousMap

variable {E X α : Type*} [TopologicalSpace E] [TopologicalSpace X] {p : E → X} {γ : C(I, X)} {e : E}

structure Subd where
  t : ℕ → I
  prop : Monotone t
  n : ℕ
  t0 : t 0 = 0
  t1 : ∀ m ≥ n, t m = 1

namespace Subd

end Subd

namespace IsCoveringMap

noncomputable def T (hp : IsCoveringMap p) (x : X) : Trivialization (p ⁻¹' {x}) p :=
  Classical.choose (hp x).2

theorem mem_T (hp : IsCoveringMap p) (x : X) : x ∈ (hp.T x).baseSet :=
  Classical.choose_spec (hp x).2

-- the value at `x` of the `x₀`-sheat passing through `e₀`
noncomputable def plift' (hp : IsCoveringMap p) (x₀ : X) (e : E) (x : X) : E :=
  let T := hp.T x₀ ; T.invFun (x, (T e).2)

theorem plift'_self (hp : IsCoveringMap p) (x₀ : X) (e : E) (hx : p e ∈ (hp.T x₀).baseSet) :
    hp.plift' x₀ e (p e) = e := by
  let T := hp.T x₀
  simp [plift']
  rw [T.symm_apply_mk_proj]
  apply T.mem_source.mpr hx

theorem plift'_proj (hp : IsCoveringMap p) (x₀ : X) (e : E) (x : X) (hx : x ∈ (hp.T x₀).baseSet) :
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

noncomputable def map (S : Setup p γ) (e₀ : E) (t : I) : E := by
  have h1 : ∃ n, t ∈ Icc (S.t n) (S.t (n + 1)) := by
    have := S.covers ; simp only [eq_univ_iff_forall] at this ; exact mem_iUnion.mp (this t)
  let n := Nat.find h1
  exact S.hp.plift' (γ (S.c n)) (S.chain e₀ n) (γ t)

end Setup

noncomputable def chain_subd (hp : IsCoveringMap p) (γ : C(I, X)) (S : Subd) (c : ℕ → I) (e₀ : E) : ℕ → E
  | 0 => e₀
  | n + 1 => hp.plift' (γ (c n)) (chain_subd hp γ S c e₀ n) (γ (S.t (n + 1)))

noncomputable def chain_map (hp : IsCoveringMap p) (γ : C(I, X)) (S : Subd) (c : ℕ → I) (e₀ : E)
    (n : ℕ) (t : I) : E := by
  let e := chain_subd hp γ S c e₀ n
  exact hp.plift' (γ (c n)) e (γ t)

theorem main (hp : IsCoveringMap p) (γ : C(I, X)) (S : Subd) (c : ℕ → I) (e₀ : E)
    (n : ℕ) : chain_map hp γ S c e₀ n (S.t (n + 1)) = chain_map hp γ S c e₀ (n + 1) (S.t (n + 1)) := by
  simp [chain_map]
  sorry

theorem Lift (hp : IsCoveringMap p) (he : p e = γ 0) :
    ∃! Γ : C(I, E), Γ 0 = e ∧ p ∘ Γ = γ := by
  let S : Setup p γ := Setup.exist hp
  sorry
