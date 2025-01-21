import Mathlib

open Set Filter Topology

structure Setup (X F : Type*) [TopologicalSpace X] [AddCommGroup F] where
  S : X → Set X
  F : X → X → F
  --
  cover : ∀ x, x ∈ S x
  pin : ∀ x, F x x = 0
  opn : ∀ x, IsOpen (S x)
  compat x y : ∀ u ∈ S x ∩ S y, ∀ v ∈ S x ∩ S y, F y v - F x v = F y u - F x u

namespace Setup

variable {X F : Type*} [TopologicalSpace X] [AddCommGroup F] {S : Setup X F}

theorem cocycle {a b c : X} (hb : b ∈ S.S a) (hc : c ∈ S.S b ∩ S.S a) :
    S.F a b + S.F b c = S.F a c := by
  simp [← eq_sub_iff_add_eq, S.compat b a b ⟨S.cover b, hb⟩ c hc, S.pin]

def Cover (_ : Setup X F) := X × F

def proj (S : Setup X F) (z : Cover S) : X := z.1

def map (S : Setup X F) (z : Cover S) (x : X) : Cover S := ⟨x, z.2 + S.F z.1 x⟩

@[simp] theorem map_self (S : Setup X F) (z : Cover S) : S.map z z.1 = z := by
  simp [map, Setup.pin]

@[simp] theorem proj_map {z : Cover S} : S.proj ∘ S.map z = id := by
  ext x ; simp [map, proj]

def nhd (z : Cover S) : Filter (Cover S) := Filter.map (S.map z) (𝓝 z.1)

theorem mem_nhd_iff {s : Set S.Cover} {z} :
  s ∈ nhd z ↔ ∃ t ∈ 𝓝 z.1, t ⊆ S.S z.1 ∧ IsOpen t ∧ S.map z '' t ⊆ s := sorry

instance : TopologicalSpace (Cover S) := TopologicalSpace.mkOfNhds nhd

theorem nhds_eq_nhd (z : Cover S) : 𝓝 z = nhd z := by
  apply TopologicalSpace.nhds_mkOfNhds
  · intro z s hs
    simpa using mem_of_mem_nhds hs
  · simp only [mem_nhd_iff, eventually_iff_exists_mem]
    intro z s ⟨t, ht1, ht2, ht3, ht4⟩
    refine ⟨S.map z '' t, ⟨t, ht1, ht2, ht3, subset_rfl⟩, ?_⟩
    rintro y ⟨x, hx1, rfl⟩
    let t' := t ∩ S.S x
    have ht'1 : IsOpen t' := ht3.inter (S.opn x)
    have ht'2 : t' ⊆ t := inter_subset_left
    have ht'3 : t' ⊆ S.S x := inter_subset_right
    refine ⟨t', ht'1.mem_nhds ⟨hx1, S.cover x⟩, ht'3, ht'1, ?_⟩
    rintro uv ⟨a, ha1, rfl⟩
    refine ht4 ⟨a, ht'2 ha1, ?_⟩
    simp_rw [map, add_assoc, cocycle (ht2 hx1) ⟨ht'3 ha1, ht2 (ht'2 ha1)⟩]

theorem continuous_proj : Continuous S.proj := by
  rw [continuous_iff_continuousAt]
  simp [ContinuousAt, Tendsto, nhds_eq_nhd, nhd, proj]

def triv (S : Setup X F) (x : X) : Trivialization (S.proj ⁻¹' {x}) S.proj where
  toFun z := ⟨z.1, ⟨⟨x, z.2 - S.F x z.1⟩, rfl⟩⟩
  invFun z := ⟨z.1, z.2.1.2 + S.F x z.1⟩
  source := S.proj ⁻¹' S.S x
  target := S.S x ×ˢ univ
  map_source' z hz := by simpa using hz
  map_target' z hz := by simpa using hz
  left_inv' z := by simp
  right_inv' := by rintro ⟨a, ⟨b, c⟩, rfl⟩ h ; simp [proj]
  open_source := (S.opn x).preimage continuous_proj
  open_target := (S.opn x).prod isOpen_univ
  continuousOn_toFun := sorry
  continuousOn_invFun := sorry
  baseSet := S.S x
  open_baseSet := S.opn x
  source_eq := rfl
  target_eq := rfl
  proj_toFun := by simp [proj]

theorem triv_mem {x : X} : x ∈ (S.triv x).baseSet := sorry

theorem main : IsCoveringMap (proj S) := by
  intro x
  constructor
  · sorry
  · use S.triv x
    exact triv_mem

end Setup
