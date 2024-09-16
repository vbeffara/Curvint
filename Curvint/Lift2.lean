import Mathlib

open Set Topology Metric unitInterval Filter ContinuousMap

variable {E X α : Type*} [TopologicalSpace E] [TopologicalSpace X] {p : E → X} {γ : C(I, X)} {e : E}

structure Subd where
  pts : List I -- the intermediate points
  ord : pts.Sorted (· ≤ ·)

namespace Subd

def lefts (s : Subd) : List I := 0 :: s.pts
def rights (s : Subd) : List I := s.pts ++ [1]
def pairs (s : Subd) : List (I × I) := List.zip s.lefts s.rights

def fits (s : Subd) (V : I → Set I) : Prop := ∀ st ∈ s.pairs, Set.Icc st.1 st.2 ⊆ V st.1

theorem fits_elim (V : I → Set I) (hV : ∀ t, V t ∈ 𝓝 t) : ∃ s : Subd, fits s V := by
  sorry

end Subd

namespace IsCoveringMap

noncomputable def T (hp : IsCoveringMap p) (x : X) : Trivialization (p ⁻¹' {x}) p :=
  Classical.choose (hp x).2

noncomputable def T' (hp : IsCoveringMap p) (e₀ : E) : Trivialization (p ⁻¹' {p e₀}) p := hp.T (p e₀)

theorem mem_T (hp : IsCoveringMap p) (x : X) : x ∈ (hp.T x).baseSet :=
  Classical.choose_spec (hp x).2

theorem mem_T_source (hp : IsCoveringMap p) (e₀ : E) : e₀ ∈ (hp.T' e₀).source :=
  (hp.T' e₀).mem_source |>.mpr (hp.mem_T (p e₀))

-- this is the local lift around `p e₀` going through `e₀`
noncomputable def plift (hp : IsCoveringMap p) (e₀ : E) (x : X) : E :=
  let T := hp.T' e₀ ; T.invFun (x, (T e₀).2)

theorem plift_comp (hp : IsCoveringMap p) (e₀ : E) (x : X) (hx : x ∈ (hp.T' e₀).baseSet) :
    p (plift hp e₀ x) = x := by
  let T := hp.T (p e₀)
  exact T.proj_symm_apply <| T.mem_target.mpr hx

theorem plift_continuous (hp : IsCoveringMap p) (e₀ : E) :
    ContinuousOn (hp.plift e₀) (hp.T' e₀).baseSet := by
  apply (hp.T' e₀).continuousOn_invFun.comp (by fun_prop)
  intro x hx ; simpa [Trivialization.mem_target]

-- This composes partial lifts, the itea being that the `ts` are between `t₀` and `t`
noncomputable def chain (hp : IsCoveringMap p) (γ : C(I, X)) (e₀ : E) (t : I) : List I → E
  | [] => hp.plift e₀ (γ t)
  | s :: ts => by
      let e : E := hp.plift e₀ (γ s)
      exact hp.chain γ e t ts

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

  -- Step 1 : use compactness to cover the range
  -- let K := Set.range γ
  -- let V (x : X) : Set X := hp.T x |>.baseSet
  -- have h1 : IsCompact K := isCompact_range γ.continuous
  -- have h2 : K ⊆ ⋃ x, V x := fun x hx => mem_iUnion.mpr ⟨x, hp.mem_T x⟩
  -- have h3 (x : X) : IsOpen (V x) := (hp.T x).open_baseSet
  -- obtain ⟨s, hs⟩ := h1.elim_finite_subcover V h3 h2

  -- Step 2 : build the map

  sorry
