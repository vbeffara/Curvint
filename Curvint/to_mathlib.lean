import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.FundThmCalculus
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Deriv.Pow

open intervalIntegral Real MeasureTheory Filter Topology Set Metric

variable {𝕜 E V : Type*} {r : ℝ} {z : ℂ} {a b t : ℝ} {n : ℕ}

theorem has_deriv_at_integral_of_continuous_of_lip
    {φ : ℂ → ℝ → ℂ} {ψ : ℝ → ℂ} {z₀ : ℂ} {a b C δ : ℝ} (hab : a ≤ b) (δ_pos : 0 < δ)
    (φ_cts : ∀ᶠ z in 𝓝 z₀, ContinuousOn (φ z) (Icc a b))
    (φ_der : ∀ t ∈ Ioc a b, HasDerivAt (λ x => φ x t) (ψ t) z₀)
    (φ_lip : ∀ t ∈ Ioc a b, LipschitzOnWith (Real.nnabs C) (λ x => φ x t) (ball z₀ δ))
    (ψ_cts : ContinuousOn ψ (Ioc a b)) :
    HasDerivAt (λ z => ∫ t in a..b, φ z t) (∫ t in a..b, ψ t) z₀ := by
  simp only [intervalIntegral, not_lt, hab, Ioc_eq_empty, Measure.restrict_empty,
    integral_zero_measure, sub_zero]
  let μ : Measure ℝ := volume.restrict (Ioc a b)
  have h1 : ∀ᶠ z in 𝓝 z₀, AEStronglyMeasurable (φ z) μ :=
    φ_cts.mono (λ z h => (h.mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc)
  have h2 : Integrable (φ z₀) μ :=
    φ_cts.self_of_nhds.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have h3 : AEStronglyMeasurable ψ μ := ψ_cts.aestronglyMeasurable measurableSet_Ioc
  have h4 : ∀ᵐ t ∂μ, LipschitzOnWith (Real.nnabs C) (λ z => φ z t) (ball z₀ δ) :=
    (ae_restrict_iff' measurableSet_Ioc).mpr (.of_forall φ_lip)
  have h5 : Integrable (λ _ => C) μ := integrable_const _
  have h6 : ∀ᵐ t ∂μ, HasDerivAt (λ z => φ z t) (ψ t) z₀ :=
    (ae_restrict_iff' measurableSet_Ioc).mpr (.of_forall φ_der)
  exact (_root_.hasDerivAt_integral_of_dominated_loc_of_lip δ_pos h1 h2 h3 h4 h5 h6).2

section uIoo

theorem uIoo_eq_union : uIoo a b = (Ioo a b) ∪ (Ioo b a) := by
  cases le_total a b <;> simp [*, uIoo]

theorem mem_uIoo : t ∈ uIoo a b ↔ (a < t ∧ t < b) ∨ (b < t ∧ t < a) := by simp [uIoo_eq_union]

theorem uIoo_eq_uIoc_sdiff_ends : uIoo a b = Ι a b \ {a, b} := by
  ext t
  constructor <;> intro hh
  · simp [mem_uIoo] at hh
    cases hh with
    | inl h => simp [uIoc, h, h.2.le, h.1.ne.symm, h.2.ne]
    | inr h => simp [uIoc, h, h.2.le, h.1.ne.symm, h.2.ne]
  · simp_rw [uIoc, mem_diff, mem_Ioc, mem_insert_iff, mem_singleton_iff] at hh
    push_neg at hh
    refine ⟨hh.1.1, lt_of_le_of_ne hh.1.2 ?_⟩
    cases le_total a b <;> simp [*]

theorem uIoo_subset_uIcc : uIoo a b ⊆ uIcc a b := by
  cases le_total a b <;> simp [uIoo, uIcc, Ioo_subset_Icc_self, *]

theorem uIcc_mem_nhds (h : t ∈ uIoo a b) : uIcc a b ∈ 𝓝 t :=
  mem_of_superset (isOpen_Ioo.mem_nhds h) uIoo_subset_uIcc

theorem uIcc_mem_nhds_within (h : t ∈ uIoo a b) : uIcc a b ∈ 𝓝[Ioi t] t :=
  nhdsWithin_le_nhds (uIcc_mem_nhds h)

theorem eventually_mem_uIoo_of_mem_uIoc : ∀ᵐ x, x ∈ Ι a b → x ∈ uIoo a b := by
  apply eventually_of_mem (U := {a, b}ᶜ)
  · simpa only [mem_ae_iff, compl_compl] using measure_union_null volume_singleton volume_singleton
  · rw [uIoo_eq_uIoc_sdiff_ends]
    exact λ t h1 h2 => ⟨h2, h1⟩
end uIoo

section helper_integral

variable [NormedAddCommGroup E] [NormedSpace ℝ E] {f g : ℝ → E}

theorem derivWithin_of_mem_uIoo {f : ℝ → E} (ht : t ∈ uIoo a b) : derivWithin f (uIcc a b) t = deriv f t :=
  by rw [derivWithin, deriv, fderivWithin_of_mem_nhds (uIcc_mem_nhds ht)]

theorem intervalIntegral.integral_congr_uIoo (h : EqOn f g (uIoo a b)) : ∫ t in a..b, f t = ∫ t in a..b, g t := by
  apply intervalIntegral.integral_congr_ae
  filter_upwards [eventually_mem_uIoo_of_mem_uIoc] with t ht1 ht2 using h (ht1 ht2)

end helper_integral

namespace ContDiffOn

variable [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {f : ℝ → E} {g : ℝ → ℝ}

omit [CompleteSpace E] in
theorem continuousOn_derivWithin'' {n : ℕ∞} (h : ContDiffOn ℝ n f (uIcc a b)) (hn : 1 ≤ n) :
    ContinuousOn (derivWithin f (uIcc a b)) (uIcc a b) := by
  by_cases hab : a = b
  · simp [continuousOn_singleton, hab]
  · refine h.continuousOn_derivWithin (uniqueDiffOn_Icc (min_lt_max.2 hab)) ?_
    simpa

omit [CompleteSpace E] in
theorem integral_derivWithin_smul_comp
    (hg : ContDiffOn ℝ 1 g (uIcc a b)) (hf : ContinuousOn f (g '' uIcc a b)) :
    (∫ x in a..b, derivWithin g (uIcc a b) x • (f ∘ g) x) = (∫ x in g a..g b, f x) := by
  refine integral_comp_smul_deriv'' hg.continuousOn (λ t ht => ?_) (hg.continuousOn_derivWithin'' le_rfl) hf
  apply (hg.differentiableOn le_rfl t (uIoo_subset_uIcc ht)).hasDerivWithinAt.mono_of_mem_nhdsWithin
  exact uIcc_mem_nhds_within ht

end ContDiffOn

theorem exists_div_lt (a : ℝ) {ε : ℝ} (hε : 0 < ε) : ∃ n : ℕ, a / ↑(n + 1) < ε :=
  Tendsto.eventually_lt_const hε
    (tendsto_const_div_atTop_nhds_zero_nat a |>.comp (tendsto_add_atTop_nat 1)) |>.exists

section sort_finset

variable {α : Type*} [LinearOrder α] {l l1 l2 : List α} {s : Finset α}

theorem List.Sorted.ext (h1 : l1.Sorted (. ≤ .)) (h2 : l2.Sorted (. ≤ .))
    (h'1 : l1.Nodup) (h'2 : l2.Nodup) (h : ∀ x, x ∈ l1 ↔ x ∈ l2) : l1 = l2 :=
  List.eq_of_perm_of_sorted ((List.perm_ext_iff_of_nodup h'1 h'2).2 h) h1 h2

theorem List.Sorted.ext' (h1 : l1.Sorted (. < .)) (h2 : l2.Sorted (. < .))
    (h4 : ∀ x, x ∈ l1 ↔ x ∈ l2) : l1 = l2 :=
  List.Sorted.ext h1.le_of_lt h2.le_of_lt h1.nodup h2.nodup h4

@[simp] theorem List.Sorted.toFinset_sort (hl : l.Sorted (· < ·)) : (l.toFinset).sort (· ≤ ·) = l :=
  List.Sorted.ext' (l.toFinset).sort_sorted_lt hl (by simp)

end sort_finset
