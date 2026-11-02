import AcceleratedLogConcave.Probability.FiniteHistory
import Mathlib.InformationTheory.KullbackLeibler.ChainRule
import Mathlib.Probability.Kernel.Composition.AbsolutelyContinuous
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-!
# Conditional relative entropy

The integral version of Mathlib's composition-product chain rule. The jointly
measurable kernel Radon–Nikodym derivative supplies a measurable version of
pointwise KL when the output measurable space is countably generated.
-/

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal

namespace AcceleratedLogConcave.Probability

variable {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
  [MeasurableSpace.CountablyGenerated B]

/-- Pointwise kernel entropy is measurable for countably generated outputs. -/
theorem measurable_klDiv_kernel (P Q : Kernel A B)
    [IsMarkovKernel P] [IsMarkovKernel Q] :
    Measurable (fun a => klDiv (P a) (Q a)) := by
  classical
  let g : A × B → ℝ≥0∞ := fun p =>
    ENNReal.ofReal (klFun ((P.rnDeriv Q p.1 p.2).toReal))
  have hg : Measurable g := by
    exact continuous_klFun.measurable.comp
      ((Kernel.measurable_rnDeriv P Q).ennreal_toReal) |>.ennreal_ofReal
  have hinner (a : A) :
      (∫⁻ b, g (a, b) ∂Q a) =
        ∫⁻ b, ENNReal.ofReal (klFun (((P a).rnDeriv (Q a) b).toReal)) ∂Q a := by
    apply lintegral_congr_ae
    filter_upwards [P.rnDeriv_eq_rnDeriv_measure (η := Q) (a := a)] with b hb
    simp [g, hb]
  have heq : (fun a => klDiv (P a) (Q a)) =
      fun a => if P a ≪ Q a then ∫⁻ b, g (a, b) ∂Q a else ∞ := by
    funext a
    rw [klDiv_eq_lintegral_klFun, hinner]
  rw [heq]
  exact Measurable.ite (Kernel.measurableSet_absolutelyContinuous P Q)
    hg.lintegral_kernel_prod_right' measurable_const

/-- Conditional KL is the average of pointwise KL. All terms remain extended valued. -/
theorem klDiv_compProd_same_eq_lintegral (μ : Measure A) [IsFiniteMeasure μ]
    (P Q : Kernel A B) [IsMarkovKernel P] [IsMarkovKernel Q] :
    klDiv (μ ⊗ₘ P) (μ ⊗ₘ Q) = ∫⁻ a, klDiv (P a) (Q a) ∂μ := by
  by_cases hac : μ ⊗ₘ P ≪ μ ⊗ₘ Q
  · have hae : ∀ᵐ a ∂μ, P a ≪ Q a :=
      Measure.absolutelyContinuous_compProd_right_iff.mp hac
    rw [klDiv_eq_lintegral_klFun_of_ac hac]
    calc
      _ = ∫⁻ p, ENNReal.ofReal (klFun ((P.rnDeriv Q p.1 p.2).toReal)) ∂(μ ⊗ₘ Q) := by
        apply lintegral_congr_ae
        filter_upwards [rnDeriv_measure_compProd_right μ P Q] with p hp
        rw [hp]
      _ = ∫⁻ a, ∫⁻ b, ENNReal.ofReal (klFun ((P.rnDeriv Q a b).toReal)) ∂Q a ∂μ := by
        apply Measure.lintegral_compProd
        fun_prop
      _ = _ := by
        apply lintegral_congr_ae
        filter_upwards [hae] with a ha
        rw [klDiv_eq_lintegral_klFun_of_ac ha]
        apply lintegral_congr_ae
        filter_upwards [P.rnDeriv_eq_rnDeriv_measure (η := Q) (a := a)] with b hb
        rw [hb]
  · rw [klDiv_of_not_ac hac]
    symm
    by_contra hfinite
    have hae := ae_lt_top (measurable_klDiv_kernel P Q) hfinite
    apply hac
    apply Measure.AbsolutelyContinuous.compProd_right
    filter_upwards [hae] with a ha
    exact (klDiv_ne_top_iff.mp ha.ne).1

/-- The KL chain rule with its conditional term written as an actual integral. -/
theorem klDiv_compProd_eq_add_lintegral (μ ν : Measure A)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (P Q : Kernel A B) [IsMarkovKernel P] [IsMarkovKernel Q] :
    klDiv (μ ⊗ₘ P) (ν ⊗ₘ Q) =
      klDiv μ ν + ∫⁻ a, klDiv (P a) (Q a) ∂μ := by
  rw [klDiv_compProd_eq_add, klDiv_compProd_same_eq_lintegral]

section FinitePaths

variable {X : Type*} [MeasurableSpace X] [MeasurableSpace.CountablyGenerated X]

/-- Exact-reference chain sum for the conditional visible-state path.

Only the marginals of the exact transitions `P` enter the sum. The implemented
transitions `Q` need no invariant law, and the local errors are averaged rather
than bounded uniformly over states. The equality also holds when entropy is infinite. -/
theorem lintegral_klDiv_finiteHistoryKernel_eq_sum
    (μ : Measure X) (P Q : ℕ → Kernel X X)
    [∀ j, IsMarkovKernel (P j)] [∀ j, IsMarkovKernel (Q j)] (n : ℕ) :
    (∫⁻ x, klDiv (finiteHistoryKernel P n x) (finiteHistoryKernel Q n x) ∂μ) =
      ∑ j ∈ Finset.range n, ∫⁻ z, klDiv (P j z) (Q j z) ∂referenceLaw μ P j := by
  induction n with
  | zero => simp [finiteHistoryKernel]
  | succ n ih =>
    have hlocal := measurable_klDiv_kernel (P n) (Q n)
    have hstep (x : X) :
        klDiv (finiteHistoryKernel P (n + 1) x) (finiteHistoryKernel Q (n + 1) x) =
          klDiv (finiteHistoryKernel P n x) (finiteHistoryKernel Q n x) +
            ∫⁻ h, klDiv (P n (historyLast n h)) (Q n (historyLast n h))
              ∂finiteHistoryKernel P n x := by
      rw [finiteHistoryKernel_succ_apply, finiteHistoryKernel_succ_apply,
        klDiv_compProd_eq_add_lintegral]
      rfl
    simp_rw [hstep]
    rw [lintegral_add_left (measurable_klDiv_kernel
      (finiteHistoryKernel P n) (finiteHistoryKernel Q n))]
    rw [lintegral_finiteHistoryKernel_historyLast μ P n
      (fun z => klDiv (P n z) (Q n z)) hlocal]
    rw [ih, Finset.sum_range_succ]

end FinitePaths

end AcceleratedLogConcave.Probability
