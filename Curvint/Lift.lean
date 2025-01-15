import Mathlib.Topology.ContinuousMap.Interval
import Mathlib.Topology.UnitInterval
import Mathlib.Topology.Covering
import Mathlib.Tactic.Peel

open Set Topology unitInterval Filter ContinuousMap

local instance : Fact ((0 : ℝ) ≤ 1) := ⟨zero_le_one⟩

variable {E X Z : Type*} [TopologicalSpace E] [TopologicalSpace X] [TopologicalSpace Z]
  {e e₀ : E} {x x₀ : X} {p : E → X} {γ : C(I, X)} {m n : ℕ}

namespace IsCoveringMap

theorem lift_unique (hp : IsCoveringMap p) {Γ₁ Γ₂ : C(I, E)} (h0 : Γ₁ 0 = Γ₂ 0)
    (h : p ∘ Γ₁ = p ∘ Γ₂) : Γ₁ = Γ₂ :=
  ContinuousMap.ext <| congrFun <| hp.eq_of_comp_eq Γ₁.continuous Γ₂.continuous h 0 h0

/-- Subdivision of an interval with an associated sequence of trivializations of the covering `p`.
  One can lift a path `γ` by gluing local lifts along such a subdivision if it is adapted to it,
  see `fits`. -/
structure LiftSetup (p : E → X) where
  /-- The bounds of the intervals in the subdivision. -/
  t : ℕ → ℝ
  /-- The number of (non-trivial) pieces. -/
  n : ℕ
  /-- The sequence of basepoints for the trivializations. -/
  c : ℕ → X
  /-- The trivializations. -/
  T : ∀ i, Trivialization (p ⁻¹' {c i}) p
  ht : Monotone t
  ht0 : t 0 = 0
  ht1 : ∀ m ≥ n, t m = 1

variable {S : LiftSetup p}

local instance : Fact (S.t 0 ≤ S.t n) := ⟨S.ht n.zero_le⟩

local instance : Fact (S.t n ≤ S.t (n + 1)) := ⟨S.ht n.le_succ⟩

namespace LiftSetup

/-- The `n`th interval in the partition contained in `S`. -/
abbrev icc (S : LiftSetup p) (n : ℕ) : Set ℝ := Icc (S.t n) (S.t (n + 1))

theorem htn : S.t S.n = 1 := S.ht1 S.n le_rfl

theorem mem_I : S.t n ∈ I := by
  refine ⟨?_, ?_⟩ <;> simp [← S.ht0, ← S.ht1 (n + S.n) (by omega)] <;> apply S.ht <;> omega

@[simp]
theorem subset : Icc (S.t m) (S.t n) ⊆ I := by
  rintro t ⟨ht0, ht1⟩ ; exact ⟨le_trans mem_I.1 ht0, le_trans ht1 mem_I.2⟩

attribute [simp] ht0 ht1

/-- The embedding of intervals adapted to the partition in `S` into the unit interval. -/
def inj (S : LiftSetup p) (m n : ℕ) : C(Icc (S.t m) (S.t n), I) :=
  ⟨fun t => ⟨t, subset t.2⟩, by fun_prop⟩

/-- This holds if the path `γ` maps each interval in the partition in `S` to the base set of the
corresponding trivialization. -/
def fits (S : LiftSetup p) (γ : C(I, X)) : Prop :=
  ∀ n ∈ Finset.range S.n, MapsTo (IccExtendCM γ) (S.icc n) (S.T n).baseSet

theorem exist (hp : IsCoveringMap p) (γ : C(I, X)) : ∃ S : LiftSetup p, S.fits γ := by
  choose T mem_T using fun t => (hp (γ t)).2
  let V (t : I) : Set I := γ ⁻¹' (T t).baseSet
  have h1 t : IsOpen (V t) := (T t).open_baseSet.preimage γ.continuous
  have h2 : univ ⊆ ⋃ t, V t := fun t _ => mem_iUnion.2 ⟨t, mem_T t⟩
  choose t ht0 ht ht1 c hc using exists_monotone_Icc_subset_open_cover_unitInterval h1 h2
  obtain ⟨n, ht1⟩ := ht1
  use ⟨(t ·), n, γ ∘ c, fun n => T (c n), ht, by simpa using ht0, by simpa using ht1⟩
  rintro k - s hs
  simpa [subset hs] using hc k hs

theorem fits.eventually {Y : Type*} [TopologicalSpace Y] {y₀ : Y} {γ : C(Y, C(I, X))}
    (hS : S.fits (γ y₀)) : ∀ᶠ y in 𝓝 y₀, S.fits (γ y) := by
  simp only [LiftSetup.fits, eventually_all_finset] at hS ⊢
  peel hS with n hn hS
  have key := ContinuousMap.eventually_mapsTo CompactIccSpace.isCompact_Icc (S.T n).open_baseSet hS
  have h4 := IccExtendCM.2.tendsto (γ y₀) |>.eventually key
  exact γ.2.tendsto y₀ |>.eventually h4

/-- This describes a path which is adapted to a `LiftSetup` and a point in the fiber above its
starting point. -/
abbrev Liftable (S : LiftSetup p) := { γe : C(I, X) × E // S.fits γe.1 ∧ p γe.2 = γe.1 0 }

/-- A sub-path of a liftable path, as a bundled continuous map into the base set of the
corresponding trivialization. -/
def γn (γe : Liftable S) (hn : n ∈ Finset.range S.n) : C(S.icc n, (S.T n).baseSet) := by
  refine ⟨fun t => ⟨γe.1.1 (S.inj _ _ t), ?_⟩, ?_⟩
  · simpa [LiftSetup.subset t.2] using γe.2.1 n hn t.2
  · fun_prop

end LiftSetup

private noncomputable def LiftWithin_partialCM : ∀ n ≤ S.n,
    {F : C(S.Liftable, C(Icc (S.t 0) (S.t n), E)) // ∀ γe,
      F γe ⊥ = γe.1.2 ∧ ∀ t, p (F γe t) = γe.1.1 (S.inj _ _ t)}
  | 0 => fun _ => by
    use ContinuousMap.const'.comp ⟨fun ye => ye.1.2, by fun_prop⟩
    rintro ⟨⟨γ, e⟩, h1, h2⟩
    refine ⟨rfl, ?_⟩
    simp only [Subtype.forall, LiftSetup.ht0, Icc_self, mem_singleton_iff]
    rintro t rfl
    exact h2
  | n + 1 => fun hn => by
    obtain ⟨Φ, hΦ⟩ := LiftWithin_partialCM n (by omega)
    replace hn : n ∈ Finset.range S.n := by simp ; omega
    refine ⟨?_, ?_⟩
    · refine (concatCM (b := S.t n)).comp ⟨?_, ?_⟩
      · intro γe
        have h5 : p (Φ γe ⊤) = γe.1.1 ⟨S.t n, _⟩ := (hΦ γe).2 ⊤
        have h6 : S.t n ∈ S.icc n := by simpa using S.ht n.le_succ
        let left : C(↑(Icc (S.t 0) (S.t n)), E) := Φ γe
        let next : C(S.icc n, E) := by
          refine .comp ⟨_, continuous_subtype_val⟩ <| (S.T n).clift (⟨left ⊤, ?_⟩, S.γn γe hn)
          simpa [Trivialization.mem_source, left, h5, LiftSetup.subset h6] using γe.2.1 n hn h6
        use ⟨left, next⟩
        simp only [comp_apply, coe_mk, next]
        rw [Trivialization.clift_self]
        simp [left, hΦ]
        rfl
      · refine Continuous.subtype_mk (continuous_prod_mk.2 ⟨by fun_prop, ?_⟩) _
        apply ContinuousMap.continuous_postcomp _ |>.comp
        apply (S.T n).clift.continuous.comp
        refine continuous_prod_mk.2 ⟨?_, ?_⟩
        · exact (continuous_eval_const _).comp Φ.continuous |>.subtype_mk _
        · let Ψ : C(S.Liftable × S.icc n, C(I, X) × I) :=
            ⟨fun fx => (fx.1.1.1, ⟨fx.2.1, LiftSetup.subset fx.2.2⟩), by fun_prop⟩
          let Φ : C(S.Liftable × S.icc n, (S.T n).baseSet) := by
            refine ⟨fun fx => ⟨fx.1.1.1 ⟨fx.2.1, LiftSetup.subset fx.2.2⟩, ?_⟩, ?_⟩
            · obtain ⟨_, _⟩ := LiftSetup.subset fx.2.2
              have := fx.1.2.1 n hn fx.2.2
              rw [IccExtendCM_of_mem] at this ; assumption
            · apply Continuous.subtype_mk
              exact ContinuousEval.continuous_eval.comp Ψ.continuous
          exact Φ.curry.continuous
    · rintro ⟨⟨γ, e⟩, hγ, he⟩ ; dsimp ; constructor
      · rw [concatCM_left (S.ht n.zero_le)] ; exact hΦ ⟨⟨γ, e⟩, hγ, he⟩ |>.1
      · rintro ⟨t, ht⟩
        by_cases htn : t ≤ S.t n
        · rw [concatCM_left htn] ; exact hΦ ⟨⟨γ, e⟩, hγ, he⟩ |>.2 ⟨t, _⟩
        · rw [concatCM_right <| le_of_not_le htn]
          set γe : S.Liftable := ⟨(γ, e), hγ, he⟩ with hγe
          have := hΦ γe ; simp [hγe] at this
          simp [Trivialization.proj_clift (proj := p)]
          rfl

private noncomputable def LiftWithin_CM :
    {F : C(S.Liftable, C(I, E)) // ∀ γe, F γe 0 = γe.1.2 ∧ ∀ t, p (F γe t) = γe.1.1 t} := by
  obtain ⟨F, hF⟩ := LiftWithin_partialCM (S := S) S.n le_rfl
  let Φ : C(I, Icc (S.t 0) (S.t S.n)) := ⟨fun t => ⟨t, by simp⟩, by fun_prop⟩
  refine ⟨⟨fun γe => (F γe).comp Φ, by fun_prop⟩, fun γe => ⟨?_, fun t => ?_⟩⟩
  · simpa [Bot.bot] using hF γe |>.1
  · simpa [LiftSetup.inj] using hF γe |>.2 (Φ t)

theorem exists_unique_lift (hp : IsCoveringMap p) (he : p e = γ 0) :
    ∃! Γ : C(I, E), Γ 0 = e ∧ p ∘ Γ = γ := by
  obtain ⟨S, hS⟩ := LiftSetup.exist hp γ
  obtain ⟨F, hF⟩ := LiftWithin_CM (S := S)
  have h1 : F ⟨⟨γ, e⟩, hS, he⟩ 0 = e := hF ⟨⟨γ, e⟩, hS, he⟩ |>.1
  have h2 : p ∘ F ⟨⟨γ, e⟩, hS, he⟩ = γ := by ext t ; exact hF ⟨⟨γ, e⟩, hS, he⟩ |>.2 t
  refine ⟨F ⟨⟨γ, e⟩, hS, he⟩, ⟨h1, h2⟩, ?_⟩
  rintro Γ ⟨hΓ₁, hΓ₂⟩
  apply hp.lift_unique <;> simp [*]

/-- The path obtained by lifting through a covering map. -/
noncomputable def lift (hp : IsCoveringMap p) (γ : C(I, X)) (he : p e = γ 0) : C(I, E) :=
  (hp.exists_unique_lift he).choose

@[simp]
theorem lift_spec (γ : C(I, X)) (hp : IsCoveringMap p) (he : p e = γ 0) :
    hp.lift γ he 0 = e ∧ p ∘ hp.lift γ he = γ :=
  (hp.exists_unique_lift he).choose_spec.1

section HLift

variable {Y : Type*} [TopologicalSpace Y] {γ : C(I × Y, X)} {Γ₀ : C(Y, E)}

private def slice (γ : C(I × Y, X)) : C(Y, C(I, X)) := γ.comp prodSwap |>.curry

private noncomputable def joint_lift (hp : IsCoveringMap p) (hΓ₀ : ∀ y, p (Γ₀ y) = γ (0, y)) :
    C(Y, C(I, E)) := by
  use fun y => hp.lift (slice γ y) (hΓ₀ y)
  rw [continuous_iff_continuousAt]
  intro y₀
  obtain ⟨S, hS⟩ := LiftSetup.exist hp (slice γ y₀)
  apply ContinuousOn.continuousAt ?_ hS.eventually
  rw [continuousOn_iff_continuous_restrict]
  let G₁ : C(S.Liftable, C(I, E)) := LiftWithin_CM |>.1
  let G₂ : C({y // S.fits (slice γ y)}, S.Liftable) :=
    ⟨fun y => ⟨⟨slice γ y, Γ₀ y⟩, y.2, hΓ₀ y⟩, by fun_prop⟩
  convert G₁.comp G₂ |>.continuous
  ext1 y
  have h3 := LiftWithin_CM |>.2 ⟨⟨slice γ y, Γ₀ y⟩, y.2, hΓ₀ y⟩
  apply hp.lift_unique <;> simp [G₁, G₂, h3, lift_spec]
  ext t ; simp [h3]

theorem exists_unique_hlift (hp : IsCoveringMap p) (hΓ₀ : ∀ y, p (Γ₀ y) = γ (0, y)) :
    ∃! Γ : C(I × Y, E), ∀ y, Γ (0, y) = Γ₀ y ∧ p ∘ (Γ ⟨·, y⟩) = (γ ⟨·, y⟩) := by
  refine ⟨joint_lift hp hΓ₀ |>.uncurry |>.comp prodSwap, ?_, ?_⟩
  · exact fun y => lift_spec (slice γ y) hp (hΓ₀ y)
  · rintro Γ hΓ ; ext1 ⟨t, y⟩
    have h1 : p (Γ₀ y) = slice γ y 0 := hΓ₀ y
    suffices (Γ.comp prodSwap |>.curry y) = (hp.lift _ h1) from ContinuousMap.congr_fun this t
    apply hp.lift_unique
    · simp [lift_spec _ hp h1, hΓ]
    · simp ; ext t
      have := congr_fun (hΓ y |>.2) t ; simp at this
      simp [this, slice]

theorem HLift' [LocallyCompactSpace Y] (hp : IsCoveringMap p) {γ : C(I, C(Y, X))}
    (hΓ₀ : ∀ y, p (Γ₀ y) = γ 0 y) :
    ∃! Γ : C(I, C(Y, E)), ∀ y, Γ 0 y = Γ₀ y ∧ p ∘ (Γ · y) = (γ · y) := by
  obtain ⟨Γ, h1, h2⟩ := exists_unique_hlift hp hΓ₀ (γ := γ.uncurry)
  refine ⟨Γ.curry, h1, fun Γ' h3 => ?_⟩
  simp [← h2 Γ'.uncurry h3] ; rfl

end HLift

end IsCoveringMap

#print axioms IsCoveringMap.exists_unique_hlift
#lint
