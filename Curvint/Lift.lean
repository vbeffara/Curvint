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
  · exact .const _ (firstval h.1 f) -- junk value

variable {f : C(Icc a b, E)} {g : C(Icc b c, E)}

@[simp] theorem concat_left (h : b ∈ Icc a c) (hb : f.lastval h.1 = g.firstval h.2)
    {t : Icc a c} (ht : t ≤ b) : concat h f g t = f ⟨t, t.2.1, ht⟩ := by
  simp [concat, hb, ht, IccExtend_apply, t.2.1]

@[simp] theorem concat_right (h : b ∈ Icc a c) (hb : f.lastval h.1 = g.firstval h.2)
    {t : Icc a c} (ht : b ≤ t) : concat h f g t = g ⟨t, ht, t.2.2⟩ := by
  simp [concat, hb, ht, IccExtend_apply, t.2.2, h.1]
  intro ht' ; have : b = t := le_antisymm ht ht' ; simpa [← this]

variable {Y : Type*} [TopologicalSpace Y] [LocallyCompactSpace Y] [CompactIccSpace α]
    {F : C(Y, C(Icc a b, E))} {G : C(Y, C(Icc b c, E))}

theorem concat_continuous (h : b ∈ Icc a c) (hfg : ∀ y, lastval h.1 (F y) = firstval h.2 (G y)) :
    Continuous (fun y => concat h (F y) (G y)) := by
  let FF := F.uncurry |>.comp ContinuousMap.prodSwap |>.curry
  let GG := G.uncurry |>.comp ContinuousMap.prodSwap |>.curry
  let FG := concat h FF GG |>.uncurry |>.comp ContinuousMap.prodSwap |>.curry |>.2
  convert FG ; rename_i y ; ext t
  by_cases htb : t ≤ b
  · simp [concat_left, hfg, htb]
    rw [concat_left h (by { ext y ; exact hfg y }) htb] ; rfl
  · have : b ≤ t := le_of_not_le htb
    simp [concat_right, hfg, this]
    rw [concat_right h (by { ext y ; exact hfg y }) this] ; rfl

theorem concat_continuousOn (h : b ∈ Icc a c) {ys : Set Y} (hys : IsClosed ys)
    (hfg : ∀ y ∈ ys, lastval h.1 (F y) = firstval h.2 (G y)) :
    ContinuousOn (fun y => concat h (F y) (G y)) ys := by
  rw [continuousOn_iff_continuous_restrict]
  change Continuous (fun y : ys ↦ concat h (F y) (G y))
  haveI : LocallyCompactSpace ys := hys.locallyCompactSpace
  apply @concat_continuous α _ _ _ a b c E _ ys _ _ _ (F.restrict ys) (G.restrict ys) h
  intro y ; exact hfg y y.2

variable {ι : Type} {p : Filter ι} {F : ι → C(Icc a b, E)} {G : ι → C(Icc b c, E)}

theorem cts (h : b ∈ Icc a c) (hfg : ∀ᶠ i in p, (F i).lastval h.1 = (G i).firstval h.2)
    (hfg' : f.lastval h.1 = g.firstval h.2)
    (hf : Tendsto F p (𝓝 f)) (hg : Tendsto G p (𝓝 g)) :
    Tendsto (fun i => concat h (F i) (G i)) p (𝓝 (concat h f g)) := by
  rw [tendsto_nhds_compactOpen] at hf hg ⊢
  rintro K hK U hU hfgU
  let π₁ : C(Icc a b, Icc a c) := ⟨fun x => ⟨x.1, x.2.1, x.2.2.trans h.2⟩, by fun_prop⟩
  let π₂ : C(Icc b c, Icc a c) := ⟨fun x => ⟨x.1, h.1.trans x.2.1, x.2.2⟩, by fun_prop⟩
  let K₁ : Set (Icc a b) := π₁ ⁻¹' K
  let K₂ : Set (Icc b c) := π₂ ⁻¹' K
  have hK₁ : IsCompact K₁ := hK.preimage_continuous π₁.2
  have hK₂ : IsCompact K₂ := hK.preimage_continuous π₂.2
  have hfU : MapsTo f K₁ U := by intro x hx ; simpa [concat, hfg', π₁, x.2.2] using hfgU hx
  have hgU : MapsTo g K₂ U := by
    intro x hx
    by_cases hxb : b = x
    · simp [lastval, firstval, hxb] at hfg' ; rw [← hfg']
      exact hfU hx
    · have : ¬ (x ≤ b) := by simpa using lt_of_le_of_ne x.2.1 hxb
      simpa [concat, hfg', π₂, this] using hfgU hx
  specialize hf K₁ hK₁ U hU hfU
  specialize hg K₂ hK₂ U hU hgU
  filter_upwards [hf, hg, hfg] with i hf hg hfg x hx
  by_cases hx' : x ≤ b
  · simp [concat, hfg, hx', Set.IccExtend, projIcc, x.2.1]
    apply hf ; simp [K₁, π₁, hx]
  · simp [concat, hfg, hx', le_of_not_le hx', Set.IccExtend, projIcc, x.2.2]
    apply hg ; simp [K₂, π₂, hx]

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

@[simp] theorem left_mem : S.t n ∈ Icc (S.t n) (S.t (n + 1)) := by simp ; apply S.ht ; simp

@[simp] theorem right_mem : S.t (n + 1) ∈ Icc (S.t n) (S.t (n + 1)) := by simp ; apply S.ht ; simp

def chain (S : Setup p) (γ : C(I, X)) (e₀ : E) : ℕ → E
  | 0 => e₀
  | n + 1 => (S.T n).lift (S.chain γ e₀ n) (γ (S.t (n + 1)))

def fits (S : Setup p) (γ : C(I, X)) : Prop :=
  ∀ n, Set.Icc (S.t n) (S.t (n + 1)) ⊆ γ ⁻¹' (S.T n).baseSet

noncomputable def exist (hp : IsCoveringMap p) (γ : C(I, X)) : { S : Setup p // S.fits γ } := by
  let T (t : I) : Trivialization (p ⁻¹' {γ t}) p := Classical.choose (hp (γ t)).2
  let mem_T (t : I) : γ t ∈ (T t).baseSet := Classical.choose_spec (hp (γ t)).2
  let V (t : I) : Set I := γ ⁻¹' (T t).baseSet
  have h1 t : IsOpen (V t) := (T t).open_baseSet.preimage γ.continuous
  have h2 : univ ⊆ ⋃ t, V t := by intro t _ ; rw [mem_iUnion] ; use t ; apply mem_T
  have := exists_monotone_Icc_subset_open_cover_unitInterval h1 h2
  choose t ht0 ht ht1 c hc using this
  choose n ht1 using ht1
  exact ⟨⟨t, n, ht, ht0, ht1, fun n => γ (c n), fun n => T (c n)⟩, hc⟩

noncomputable def partial_map (S : Setup p) (γ : C(I, X)) (e₀ : E) (n : ℕ) :
    C(Icc (S.t n) (S.t (n + 1)), E) := by
  by_cases hS : S.fits γ
  · let f (t : (Icc (S.t n) (S.t (n + 1)))) : E := (S.T n).lift (S.chain γ e₀ n) (γ ↑t)
    have : Continuous f := by
      apply (S.T n).continuousOn_invFun.comp_continuous (by fun_prop)
      intro t ; rw [Trivialization.mem_target] ; exact hS n t.2
    exact ⟨f, this⟩
  · exact .const _ (S.chain γ e₀ n)

noncomputable def pmap (S : Setup p) (γ : C(I, X)) (e₀ : E) : ∀ n, C(Icc (S.t 0) (S.t n), E)
  | 0 => .const _ e₀
  | n + 1 => concat ⟨S.ht (by omega), S.ht (by omega)⟩ (pmap S γ e₀ n) (S.partial_map γ e₀ n)

noncomputable def map (S : Setup p) (γ : C(I, X)) (e₀ : E) : C(I, E) := by
  have h1 (t : I) : t ∈ Icc (S.t 0) (S.t S.n) := by
    rcases t with ⟨t, ht0, ht1⟩
    simp [S.ht0, S.ht1]
    simpa using ht1
  have := S.pmap γ e₀ S.n
  let f (t : I) := S.pmap γ e₀ S.n ⟨t, h1 t⟩
  have h2 : Continuous f := by fun_prop
  exact ⟨f, h2⟩

namespace fits

theorem chain_proj (hS : S.fits γ) (he₀ : p e₀ = γ 0) (n : ℕ) :
    p (S.chain γ e₀ n) = γ (S.t n) := by
  cases n with
  | zero => simp [chain, he₀, S.ht0]
  | succ n =>
    apply Trivialization.lift_proj ; apply hS n ; apply S.right_mem

@[simp] theorem partial_map_left (hS : S.fits γ) (he₀ : p e₀ = γ 0) (n : ℕ) :
    firstval (S.ht (by omega)) (partial_map S γ e₀ n) = S.chain γ e₀ n := by
  have h1 := hS.chain_proj he₀ n
  simp [firstval, partial_map, ← h1, hS]
  apply (S.T _).lift_self ; simp [h1] ; apply hS n ; apply S.left_mem

@[simp] theorem partial_map_right (hS : S.fits γ) (e₀ : E) (n : ℕ) :
    partial_map S γ e₀ n ⟨_, right_mem⟩ = S.chain γ e₀ (n + 1) := by
  simp [partial_map, hS] ; rfl

@[simp] theorem pmap_last (hS : S.fits γ) (he₀ : p e₀ = γ 0) :
    lastval (S.ht (by omega)) (pmap S γ e₀ n) = S.chain γ e₀ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [lastval, pmap, concat_right]
    · rw [partial_map_right] ; exact hS
    · rw [ih, partial_map_left]
      · exact hS
      · exact he₀
    · apply S.ht ; omega

@[simp] theorem pmap_first (hS : S.fits γ) (he₀ : p e₀ = γ 0) :
    firstval (S.ht (by omega)) (pmap S γ e₀ n) = e₀ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rwa [firstval, pmap, concat_left]
    · simp [*]
    · apply S.ht ; omega

@[simp] theorem pmap_apply (hS : S.fits γ) (he₀ : p e₀ = γ 0) (n : ℕ)
    (t : Icc (S.t 0) (S.t n)) : p (pmap S γ e₀ n t) = γ t := by
  induction n with
  | zero =>
    obtain ⟨t, ht⟩ := t ; simp [S.ht0] at ht ; subst ht
    simp [pmap, he₀]
  | succ n ih =>
    simp [pmap]
    by_cases h : t ≤ S.t n
    · rw [concat_left]
      · apply ih
      · simp [*]
      · exact h
    · have : S.t n ≤ t := by simp at h ; exact h.le
      rw [concat_right _ _ this]
      · simp [partial_map, hS]
        apply Trivialization.lift_proj
        apply hS
        refine ⟨this, t.2.2⟩
      · simp [*]

@[simp] theorem map_zero (hS : S.fits γ) (he₀ : p e₀ = γ 0) : S.map γ e₀ 0 = e₀ := by
  simpa [firstval, S.ht0, map, pmap] using pmap_first hS he₀

@[simp] theorem map_apply (hS : S.fits γ) (he₀ : p e₀ = γ 0) (t : I) : p (S.map γ e₀ t) = γ t := by
  simp [Setup.map, *]

@[simp] theorem map_comp (hS : S.fits γ) (he₀ : p e₀ = γ 0) : p ∘ (S.map γ e₀) = γ := by
  ext t ; simp [*]

end fits

end Setup

theorem Lift (hp : IsCoveringMap p) (he₀ : p e₀ = γ 0) : ∃! Γ : C(I, E), Γ 0 = e₀ ∧ p ∘ Γ = γ := by
  obtain ⟨S, hS⟩ := Setup.exist hp γ
  refine ⟨S.map γ e₀, ?_, fun Γ hΓ => ?_⟩
  · simp [*]
  · apply hp.lift_unique <;> simp [hΓ, *]

#print axioms Lift

section HomotopyLift

variable {Y : Type*} [TopologicalSpace Y]

def fiber (γ : C(I × Y, X)) : C(Y, C(I, X)) := γ.comp prodSwap |>.curry

def square [LocallyCompactSpace Y] (γ : C(I, C(Y, X))) : C(I × Y, X) := γ.uncurry

instance toto : CompactIccSpace I := ⟨fun {_ _} => isClosed_Icc.isCompact⟩

-- theorem eventually_fits (γ : C(Y, C(I, X))) (S : Setup p) (y₀ : Y) (hS : S.fits (γ y₀)) :
--     ∀ᶠ y in 𝓝 y₀, S.fits (γ y) := by
--   simp only [Setup.fits, eventually_all_finset] at hS ⊢
--   peel hS with n hn hS
--   have h1 : IsCompact (Icc (S.t n) (S.t (n + 1))) := CompactIccSpace.isCompact_Icc
--   have h2 : IsOpen (S.T n).baseSet := (S.T n).open_baseSet
--   exact γ.2.tendsto y₀ <| ContinuousMap.eventually_mapsTo h1 h2 hS

noncomputable def fiber_lift (hp : IsCoveringMap p) (γ : C(Y, C(I , X))) (Γ₀ : Y → E)
    (hΓ₀ : ∀ y, p (Γ₀ y) = γ y 0) (y : Y) : C(I, E) :=
  (Lift hp (hΓ₀ y)).choose

noncomputable def fiber_map (S : Setup p) (γ : C(Y, C(I , X))) (Γ₀ : Y → E) (y : Y) : C(I, E) :=
  S.map (γ y) (Γ₀ y)

theorem map_eq_lift (hp : IsCoveringMap p) (γ : C(Y, C(I , X))) (Γ₀ : Y → E)
    (hΓ₀ : ∀ y, p (Γ₀ y) = γ y 0) (y : Y) (S : Setup p) (hS : S.fits (γ y)) :
    fiber_map S γ Γ₀ y = fiber_lift hp γ Γ₀ hΓ₀ y :=
  (Lift hp (hΓ₀ y)).choose_spec.2 _ ⟨hS.map_zero (hΓ₀ y), hS.map_comp (hΓ₀ y)⟩

noncomputable def fiber_partial_map (S : Setup p) (γ : C(Y, C(I , X))) (Γ₀ : Y → E)
    (y : {y // S.fits (γ y)}) : C(I, E) :=
  fiber_map S γ Γ₀ y

theorem continuous_fiber_partial_map (S : Setup p) (γ : C(Y, C(I , X))) (Γ₀ : Y → E)
    (hΓ₀ : ∀ y, p (Γ₀ y) = γ y 0) : Continuous (fiber_partial_map S γ Γ₀) := by
  rw [continuous_iff_continuousAt] ; intro y
  unfold fiber_partial_map fiber_map Setup.map
  sorry

end HomotopyLift
