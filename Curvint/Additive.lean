import Mathlib

open Set Filter Topology

structure Setup (X F : Type*) [TopologicalSpace X] [AddCommGroup F] where
  S : X → Set X
  F : X → X → F
  --
  mem x : x ∈ S x
  pin x : F x x = 0
  opn x : IsOpen (S x)
  cst x y : ∀ u ∈ S x ∩ S y, ∀ v ∈ S x ∩ S y, F y v - F x v = F y u - F x u

namespace Setup

attribute [simp] pin

variable {X F : Type*} [TopologicalSpace X] [AddCommGroup F] {S : Setup X F}

theorem cocycle {a b c : X} (hb : b ∈ S.S a) (hc : c ∈ S.S b ∩ S.S a) :
    S.F a b + S.F b c = S.F a c := by
  simp [← eq_sub_iff_add_eq, S.cst b a b ⟨S.mem b, hb⟩ c hc]

def Cover (_ : Setup X F) := X × F

def proj (S : Setup X F) (z : Cover S) : X := z.1

def map (S : Setup X F) (z : Cover S) (x : X) : Cover S := ⟨x, z.2 + S.F z.1 x⟩

@[simp] theorem map_self (S : Setup X F) (z : Cover S) : S.map z z.1 = z := by
  simp [map, Setup.pin]

@[simp] theorem proj_map {z : Cover S} : S.proj ∘ S.map z = id := by
  ext x ; simp [map, proj]

def nhd (z : Cover S) : Filter (Cover S) := Filter.map (S.map z) (𝓝 z.1)

theorem mem_nhd_iff {s : Set S.Cover} {z} :
    s ∈ nhd z ↔ ∃ t ∈ 𝓝 z.1, t ⊆ S.S z.1 ∧ IsOpen t ∧ S.map z '' t ⊆ s := by
  simp only [nhd, mem_map_iff_exists_image]
  constructor
  · rintro ⟨t, ht1, ht2⟩
    obtain ⟨t', ht'1, ht'2, ht'3⟩ := mem_nhds_iff.1 ht1
    exact ⟨t' ∩ S.S z.1, (ht'2.inter (S.opn _)).mem_nhds ⟨ht'3, S.mem _⟩, inter_subset_right,
      (ht'2.inter (S.opn _)), Subset.trans (image_mono (Subset.trans inter_subset_left ht'1)) ht2⟩
  · rintro ⟨t, ht1, -, -, ht2⟩ ; exact ⟨t, ht1, ht2⟩

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
    refine ⟨t', ht'1.mem_nhds ⟨hx1, S.mem x⟩, ht'3, ht'1, ?_⟩
    rintro uv ⟨a, ha1, rfl⟩
    refine ht4 ⟨a, ht'2 ha1, ?_⟩
    simp_rw [map, add_assoc, cocycle (ht2 hx1) ⟨ht'3 ha1, ht2 (ht'2 ha1)⟩]

theorem continuous_proj : Continuous S.proj := by
  rw [continuous_iff_continuousAt]
  simp [ContinuousAt, Tendsto, nhds_eq_nhd, nhd, proj]

theorem tendsto_iff {z : S.Cover} {ι : Type*} {p : Filter ι} {f : ι → S.Cover} :
    Tendsto f p (𝓝 z) ↔
      Tendsto (S.proj ∘ f) p (𝓝 z.1) ∧ ∀ᶠ i in p, f i = S.map z (S.proj (f i)) := by
  sorry

theorem mem_nhds_iff {z : S.Cover} {s : Set S.Cover} :
    s ∈ 𝓝 z ↔ ∀ᶠ x in 𝓝 z.1, S.map z x ∈ s := by
  simp only [nhds_eq_nhd, nhd, mem_map_iff_exists_image, eventually_iff_exists_mem]
  constructor
  · rintro ⟨t, ht1, ht2⟩
    refine ⟨t, ht1, fun x hx => ht2 ⟨x, hx, rfl⟩⟩
  · rintro ⟨t, ht1, ht2⟩
    refine ⟨t, ht1, ?_⟩
    rintro a ⟨b, hb, rfl⟩
    exact ht2 _ hb

instance {x : X} : DiscreteTopology (S.proj ⁻¹' {x}) := by
  simp [discreteTopology_iff_singleton_mem_nhds, nhds_induced]
  rintro z rfl
  refine ⟨S.map z '' S.S z.1, ?_, ?_⟩
  · simp [nhds_eq_nhd, nhd]
    exact mem_of_superset ((S.opn _).mem_nhds (S.mem _)) (subset_preimage_image _ _)
  · simp [proj, map]
    rintro ⟨a, b⟩ rfl u hu1 hu2
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj_iff.1 hu2
    simp

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
  continuousOn_toFun := by
    simp [((S.opn x).preimage continuous_proj).continuousOn_iff, proj]
    rintro ⟨a, b⟩ (ha : a ∈ S.S x)
    rw [ContinuousAt]
    rintro s hs
    simp [mem_nhds_iff]
    simp [nhds_prod_eq] at hs
    change ∀ᶠ x_1 in 𝓝 a, _ at hs
    have h1 : ∀ᶠ x_1 in 𝓝 a, x_1 ∈ S.S a := (S.opn _).eventually_mem (S.mem _)
    have h2 : ∀ᶠ x_1 in 𝓝 a, x_1 ∈ S.S x := (S.opn _).eventually_mem ha
    filter_upwards [hs, h1, h2] with y hy h1 h2
    simp [map]
    convert hy using 4
    have := S.cst x a a ⟨ha, S.mem a⟩ y ⟨h2, h1⟩
    rw [add_sub_assoc, this] ; simp ; abel
  continuousOn_invFun := sorry
  baseSet := S.S x
  open_baseSet := S.opn x
  source_eq := rfl
  target_eq := rfl
  proj_toFun := by simp [proj]

theorem main : IsCoveringMap (proj S) :=
  fun x => ⟨inferInstance, S.triv x, S.mem x⟩

end Setup
