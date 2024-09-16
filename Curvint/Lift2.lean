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

theorem fits_elim (V : I → Set I) (hV1 : ∀ t, t ∈ V t) (hV2 : ∀ t, IsOpen (V t)) :
    ∃ s : Subd, ∃ c : ℕ → I, ∀ n, Set.Icc (s.t n) (s.t (n+1)) ⊆ V (c n) := by
  have h1 : univ ⊆ ⋃ i, V i := fun x _ => mem_iUnion.mpr ⟨x, hV1 x⟩
  obtain ⟨t, h3, h4, ⟨n, h5⟩, hs⟩ := exists_monotone_Icc_subset_open_cover_unitInterval hV2 h1
  choose c hc using hs
  exact ⟨⟨t, h4, n, h3, h5⟩, c, hc⟩

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

noncomputable def exist (hp : IsCoveringMap p): Setup p γ := by
  let V (t : I) : Set I := γ ⁻¹' (hp.T (γ t)).baseSet
  have h1 t : IsOpen (V t) := (hp.T (γ t)).open_baseSet.preimage γ.continuous
  have h2 : univ ⊆ ⋃ t, V t := by intro t _ ; rw [mem_iUnion] ; use t ; apply hp.mem_T
  have := exists_monotone_Icc_subset_open_cover_unitInterval h1 h2
  choose t ht0 ht ht1 c hc using this
  choose n ht1 using ht1
  refine ⟨t, c, n, ht, ht0, ht1, hp, hc⟩

noncomputable def chain (S : Setup p γ) (e₀ : E) : ℕ → E
  | 0 => e₀
  | n + 1 => S.hp.plift' (γ (S.c n)) (chain S e₀ n) (γ (S.t (n + 1)))

theorem chain_proj (S : Setup p γ) (e₀ : E) (he₀ : p e₀ = γ 0) (n : ℕ) : p (S.chain e₀ n) = γ (S.t n) := by
  cases n with
  | zero => simp [chain, he₀, S.ht0]
  | succ n => apply plift'_proj ; apply S.hc n ; apply right_mem_Icc.mpr ; apply S.ht ; simp

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

end IsCoveringMap

theorem Lift (hp : IsCoveringMap p) (he : p e = γ 0) :
    ∃! Γ : C(I, E), Γ 0 = e ∧ p ∘ Γ = γ := by

  -- Step 1: cover the interval in relevant sets
  let U (t : I) : Set X := hp.T (γ t) |>.baseSet
  let V (t : I) : Set I := γ ⁻¹' U t
  have h1 (t : I) : IsOpen (V t) := (hp.T (γ t)).open_baseSet.preimage γ.continuous
  have h3 (t : I) : t ∈ V t := hp.mem_T _
  have h2 : ⋃ t, V t = univ := by
    simpa only [eq_univ_iff_forall] using fun t => mem_iUnion.mpr ⟨t, h3 t⟩

  obtain ⟨s, c, hs⟩ := Subd.fits_elim V h3 h1

  -- Step 1 : use compactness to cover the range
  -- let K := Set.range γ
  -- let V (x : X) : Set X := hp.T x |>.baseSet
  -- have h1 : IsCompact K := isCompact_range γ.continuous
  -- have h2 : K ⊆ ⋃ x, V x := fun x hx => mem_iUnion.mpr ⟨x, hp.mem_T x⟩
  -- have h3 (x : X) : IsOpen (V x) := (hp.T x).open_baseSet
  -- obtain ⟨s, hs⟩ := h1.elim_finite_subcover V h3 h2

  -- Step 2 : build the map

  sorry
