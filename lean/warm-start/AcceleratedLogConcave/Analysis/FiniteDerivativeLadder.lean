import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-! Exact ordinary iterated derivatives from a finite consecutive ladder on
an open set. No derivative at or above the last field is assumed. -/
noncomputable section
open Set
open scoped Topology
set_option autoImplicit false
namespace AcceleratedLogConcave.Analysis
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem iteratedDeriv_eq_of_finite_ladder (n : ℕ) (f : ℕ → ℝ → E)
    {s : Set ℝ} (hs : IsOpen s)
    (hd : ∀ k < n, ∀ t ∈ s, HasDerivAt (f k) (f (k + 1) t) t)
    {t : ℝ} (ht : t ∈ s) : iteratedDeriv n (f 0) t = f n t := by
  induction n generalizing f with
  | zero => simp only [iteratedDeriv_zero]
  | succ n ih =>
    rw [iteratedDeriv_succ']
    have he : deriv (f 0) =ᶠ[𝓝 t] f 1 := by
      filter_upwards [hs.mem_nhds ht] with u hu
      exact (hd 0 (Nat.zero_lt_succ n) u hu).deriv
    calc
      iteratedDeriv n (deriv (f 0)) t = iteratedDeriv n (f 1) t :=
        (he.iteratedDeriv n).eq_of_nhds
      _ = f (n + 1) t := by
        exact ih (fun k => f (k + 1))
          (fun k hk u hu => hd (k + 1) (Nat.succ_lt_succ hk) u hu)

end AcceleratedLogConcave.Analysis
