import Mathlib

variable
  {E : Type*} [TopologicalSpace E]
  {X : Type*} [TopologicalSpace X]
  {K : Type*} [TopologicalSpace K] [CompactSpace K]
  {f : E → X}

def tomaps (K : Type*) [TopologicalSpace K] (hf : IsCoveringMap f) (φ : C(K, E)) : C(K, X) :=
  ⟨f ∘ φ, hf.continuous.comp φ.continuous⟩

theorem HigherCovering (hf : IsCoveringMap f) : IsCoveringMap (tomaps K hf) := by
  intro φ
  have h1 (k : K) := hf (φ k) |>.1
  have h2 (k : K) := hf (φ k) |>.2
  choose B hB using h2
  let φK : Set X := Set.range φ
  have h3 : IsCompact φK := isCompact_range φ.continuous
  have h4 : φK ⊆ ⋃ k, (B k).baseSet := by
    rintro x ⟨k, rfl⟩
    simpa using ⟨k, hB k⟩
  have h5 k := (B k).open_baseSet
  obtain ⟨K₀, h6⟩ := h3.elim_finite_subcover _ h5 h4
  let F : PartialHomeomorph C(K, E) (C(K, X) × tomaps K hf ⁻¹' {φ}) := sorry
  refine ⟨?_, ?_⟩
  · sorry
  · refine ⟨?_, ?_⟩
    · refine ⟨F, ?_, ?_, ?_, ?_, ?_⟩
      all_goals { sorry }
    · all_goals { sorry }
