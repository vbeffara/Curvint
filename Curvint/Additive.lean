import Mathlib.Topology.Covering.Basic

open Set Filter Topology

structure Setup (X F : Type*) [TopologicalSpace X] [AddCommGroup F] where
  S : X → Set X
  F : X → X → (F ≃ F)
  --
  mem_self a : a ∈ S a
  apply_self a : F a a = Equiv.refl _
  isOpen a : IsOpen (S a)
  cocycle {a b c} (hab : b ∈ S a) (hac : c ∈ S a) (hbc : c ∈ S b) : F a c = (F a b).trans (F b c)

namespace Setup

variable {X F : Type*} [TopologicalSpace X] [AddCommGroup F] {S : Setup X F}

def Cover (_ : Setup X F) := X × F

def proj (S : Setup X F) (z : Cover S) : X := z.1

def map (S : Setup X F) (z : Cover S) (x : X) : Cover S := ⟨x, (S.F z.1 x) z.2⟩

@[simp] theorem map_self (S : Setup X F) (z : Cover S) : S.map z z.1 = z := by
  simp [map, apply_self]

@[simp] theorem proj_map {z : Cover S} : S.proj ∘ S.map z = id := by
  ext x ; simp [map, proj]

def nhd (z : Cover S) : Filter (Cover S) := Filter.map (S.map z) (𝓝 z.1)

instance : TopologicalSpace (Cover S) := TopologicalSpace.mkOfNhds nhd

theorem mem_nhd_iff {s : Set S.Cover} {z} :
    s ∈ nhd z ↔ ∃ t ∈ 𝓝 z.1, t ⊆ S.S z.1 ∧ IsOpen t ∧ S.map z '' t ⊆ s := by
  simp only [nhd, mem_map_iff_exists_image]
  constructor
  · rintro ⟨t, ht1, ht2⟩
    obtain ⟨t', ht'1, ht'2, ht'3⟩ := mem_nhds_iff.1 ht1
    exact ⟨t' ∩ S.S z.1, (ht'2.inter (S.isOpen _)).mem_nhds ⟨ht'3, S.mem_self _⟩, inter_subset_right,
      (ht'2.inter (S.isOpen _)), Subset.trans (image_mono (Subset.trans inter_subset_left ht'1)) ht2⟩
  · rintro ⟨t, ht1, -, -, ht2⟩ ; exact ⟨t, ht1, ht2⟩

theorem nhds_eq_nhd (z : Cover S) : 𝓝 z = nhd z := by
  apply TopologicalSpace.nhds_mkOfNhds
  · intro z s hs
    simpa using mem_of_mem_nhds hs
  · simp only [mem_nhd_iff, eventually_iff_exists_mem]
    intro z s ⟨t, ht1, ht2, ht3, ht4⟩
    refine ⟨S.map z '' t, ⟨t, ht1, ht2, ht3, subset_rfl⟩, ?_⟩
    rintro y ⟨x, hx1, rfl⟩
    let t' := t ∩ S.S x
    have ht'1 : IsOpen t' := ht3.inter (S.isOpen x)
    have ht'2 : t' ⊆ S.S x := inter_subset_right
    refine ⟨t', ht'1.mem_nhds ⟨hx1, S.mem_self x⟩, ht'2, ht'1, ?_⟩
    rintro uv ⟨a, ha1, rfl⟩
    have ha2 : a ∈ t := inter_subset_left ha1
    refine ht4 ⟨a, ha2, ?_⟩
    simp [map, S.cocycle (ht2 hx1) (ht2 ha2) (ht'2 ha1)]

theorem continuous_proj : Continuous S.proj := by
  rw [continuous_iff_continuousAt]
  simp [ContinuousAt, Tendsto, nhds_eq_nhd, nhd, proj]

theorem mem_nhds_iff {z : S.Cover} {s : Set S.Cover} :
    s ∈ 𝓝 z ↔ ∀ᶠ x in 𝓝 z.1, S.map z x ∈ s := by
  simp only [nhds_eq_nhd, nhd, mem_map_iff_exists_image, eventually_iff_exists_mem]
  constructor
  · rintro ⟨t, ht1, ht2⟩
    exact ⟨t, ht1, fun x hx => ht2 ⟨x, hx, rfl⟩⟩
  · rintro ⟨t, ht1, ht2⟩
    refine ⟨t, ht1, ?_⟩
    rintro a ⟨b, hb, rfl⟩
    exact ht2 _ hb

instance {x : X} : DiscreteTopology (S.proj ⁻¹' {x}) := by
  simp only [discreteTopology_iff_singleton_mem_nhds, nhds_induced, mem_comap, subset_singleton_iff,
    mem_preimage, Subtype.forall, mem_singleton_iff, Subtype.mk.injEq]
  rintro z rfl
  refine ⟨S.map z '' S.S z.1, ?_, ?_⟩
  · simp [nhds_eq_nhd, nhd]
    exact mem_of_superset ((S.isOpen _).mem_nhds (S.mem_self _)) (subset_preimage_image _ _)
  · simp only [proj, map, mem_image, forall_exists_index, and_imp]
    rintro ⟨a, b⟩ rfl u hu1 hu2
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj_iff.1 hu2
    simp [apply_self]

def triv (S : Setup X F) (x : X) : Trivialization (S.proj ⁻¹' {x}) S.proj where
  toFun z := ⟨z.1, ⟨⟨x, (S.F x z.1).symm z.2⟩, rfl⟩⟩
  invFun z := ⟨z.1, (S.F x z.1) z.2.1.2⟩
  source := S.proj ⁻¹' S.S x
  target := S.S x ×ˢ univ
  map_source' z hz := by simpa using hz
  map_target' z hz := by simpa using hz
  left_inv' z := by simp
  right_inv' := by rintro ⟨a, ⟨b, c⟩, rfl⟩ h ; simp [proj]
  open_source := (S.isOpen x).preimage continuous_proj
  open_target := (S.isOpen x).prod isOpen_univ
  continuousOn_toFun := by
    simp only [((S.isOpen x).preimage continuous_proj).continuousOn_iff, mem_preimage, proj]
    rintro ⟨a, b⟩ (ha : a ∈ S.S x) s hs
    simp only [mem_map, mem_nhds_iff, mem_preimage]
    simp only [nhds_prod_eq, nhds_discrete, prod_pure, mem_map] at hs
    have h1 : ∀ᶠ y in 𝓝 a, y ∈ S.S a := (S.isOpen _).eventually_mem <| S.mem_self _
    have h2 : ∀ᶠ y in 𝓝 a, y ∈ S.S x := (S.isOpen _).eventually_mem ha
    filter_upwards [hs, h1, h2] with y hy h1 h2
    simpa [map, S.cocycle ha h2 h1] using hy
  continuousOn_invFun := by
    simp only [((S.isOpen _).prod isOpen_univ).continuousOn_iff, mem_prod, mem_univ, and_true,
      Prod.forall, Subtype.forall, mem_preimage, proj, mem_singleton_iff]
    rintro a ⟨b, c⟩ rfl (ha : a ∈ S.S b) s hs
    simp only [mem_nhds_iff] at hs
    simp only [nhds_prod_eq, nhds_discrete, prod_pure, map_map, mem_map]
    have h1 : ∀ᶠ y in 𝓝 a, y ∈ S.S a := (S.isOpen _).eventually_mem <| S.mem_self _
    have h2 : ∀ᶠ y in 𝓝 a, y ∈ S.S b := (S.isOpen _).eventually_mem ha
    filter_upwards [hs, h1, h2] with x hx h1 h2
    simpa [map, S.cocycle ha h2 h1, add_assoc] using hx
  baseSet := S.S x
  open_baseSet := S.isOpen x
  source_eq := rfl
  target_eq := rfl
  proj_toFun := by simp [proj]

theorem main : IsCoveringMap (proj S) := fun x => ⟨inferInstance, S.triv x, S.mem_self x⟩

end Setup
