import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Source precision indices and separate recursion ranks

This scalar interface records the allowed call indices in warm-start.tex,
lines 2567–2636. It does not construct a source graph or a finite oracle program.
Precision is real; only a mean at precision at most `1/2` is terminal.
Sampling is a finite helper with same-precision mean suppliers, not another
recursive sampling routine. All active-final suppliers remain in `WorkChild`.

`SupportChild` is the potential recursive shift support selected by source role.
Connecting it to actual shifts still requires the active-final coefficient-zero
identity and preservation of zero coordinates under absorption. It never removes
an execution from the work relation. Ranks count call depth, not total work,
finite let-depth, tape size, or size-certificate transitions. They depend only on
scalar labels, with no oracle, center, momentum, tape, or probability-law inputs.
-/

namespace AcceleratedLogConcave.Oracle.Precision

/-- The source stopping rule applies to means, including the equality case. -/
def terminal (q : ℝ) : Prop := q ≤ (1 / 2 : ℝ)

/-- Scalar call indices. A sampling label is passed unchanged to its mean suppliers. -/
inductive CallIndex where
  | mean (q : ℝ)
  | sampling (alpha : ℝ)

/-- Roles distinguish the source precision allocations and the finite wrapper. -/
inductive EdgeRole where
  | activeFinal
  | mainLayer
  | privateAnchor
  | samplingSupplier
  deriving DecidableEq

/-- Allowed source transitions, oriented child then parent for well-foundedness.
There is no sampling-to-sampling edge or outgoing terminal-mean edge. This is
an index relation, not an instantiated graph or a certificate supplied by a compiler. -/
inductive CallEdge (t : ℝ) : EdgeRole → CallIndex → CallIndex → Prop where
  | activeFinal {q : ℝ} (hq : (1 / 2 : ℝ) < q) :
      CallEdge t .activeFinal (.mean (q - t)) (.mean q)
  | mainLayer {q : ℝ} (hq : (1 / 2 : ℝ) < q) :
      CallEdge t .mainLayer (.mean (q - 1 / 4)) (.mean q)
  | privateAnchor {q : ℝ} (hq : (1 / 2 : ℝ) < q) :
      CallEdge t .privateAnchor (.sampling (q - 1 / 4)) (.mean q)
  | samplingSupplier (alpha : ℝ) :
      CallEdge t .samplingSupplier (.mean alpha) (.sampling alpha)

/-- All allowed suppliers, including active-final and zero-shift suppliers. -/
def WorkChild (t : ℝ) (child parent : CallIndex) : Prop :=
  ∃ role, CallEdge t role child parent

/-- Potential support edges only. Actual-shift correspondence remains a separate
obligation; this predicate never changes `WorkChild` or finite-program execution. -/
def SupportChild (t : ℝ) (child parent : CallIndex) : Prop :=
  ∃ role, role ≠ .activeFinal ∧ CallEdge t role child parent

/-- Natural ceiling clamps below-threshold precision to zero when `step > 0`.
The precision subtraction itself is real, not truncated natural subtraction. -/
noncomputable def precisionRank (step q : ℝ) : ℕ :=
  Nat.ceil ((q - (1 / 2 : ℝ)) / step)

/-- The extra nonterminal unit pays a private sampling wrapper whose mean
suppliers have already crossed the stopping threshold. -/
noncomputable def meanFullRank (t q : ℝ) : ℕ := by
  classical
  exact if terminal q then 0 else precisionRank t q + 1

/-- Full rank includes the sampling wrapper and every executed supplier role. -/
noncomputable def fullRank (t : ℝ) : CallIndex → ℕ
  | .mean q => meanFullRank t q
  | .sampling alpha => meanFullRank t alpha + 1

/-- Quarter-decrement rank for potential shift support, doubled to pay wrappers. -/
noncomputable def meanSupportRank (q : ℝ) : ℕ :=
  2 * Nat.ceil (4 * (q - (1 / 2 : ℝ)))

/-- Support rank does not bound all executed edges; active-final edges remain work. -/
noncomputable def supportRank : CallIndex → ℕ
  | .mean q => meanSupportRank q
  | .sampling alpha => meanSupportRank alpha + 1

theorem SupportChild.workChild {t : ℝ} {child parent : CallIndex}
    (h : SupportChild t child parent) : WorkChild t child parent := by
  obtain ⟨role, _, hedge⟩ := h
  exact ⟨role, hedge⟩

theorem precisionRank_zero_iff {step q : ℝ} (hs : 0 < step) :
    precisionRank step q = 0 ↔ terminal q := by
  simp only [precisionRank, Nat.ceil_eq_zero, terminal]
  rw [div_le_iff₀ hs, zero_mul, sub_nonpos]

theorem precisionRank_pos_iff {step q : ℝ} (hs : 0 < step) :
    0 < precisionRank step q ↔ (1 / 2 : ℝ) < q := by
  rw [Nat.pos_iff_ne_zero, ne_eq, precisionRank_zero_iff hs]
  exact not_le

theorem precisionRank_mono {step q q' : ℝ} (hs : 0 < step) (hq : q' ≤ q) :
    precisionRank step q' ≤ precisionRank step q := by
  exact Nat.ceil_mono (div_le_div_of_nonneg_right (sub_le_sub_right hq _) hs.le)

/-- A multiple-unit drop uses a nonterminal child, preventing natural truncation
from falsely paying arbitrarily many units after an overshoot. -/
theorem precisionRank_drop_units {step q child : ℝ} (n : ℕ)
    (hs : 0 < step) (hc : (1 / 2 : ℝ) < child)
    (hchild : child + (n : ℝ) * step ≤ q) :
    precisionRank step child + n ≤ precisionRank step q := by
  have hx : 0 ≤ (child - (1 / 2 : ℝ)) / step := by positivity
  rw [precisionRank, precisionRank, ← Nat.ceil_add_natCast hx n]
  apply Nat.ceil_mono
  apply (le_div_iff₀ hs).2
  calc
    ((child - (1 / 2 : ℝ)) / step + (n : ℝ)) * step =
        child - 1 / 2 + (n : ℝ) * step := by
          rw [add_mul, div_mul_cancel₀ _ hs.ne']
    _ ≤ q - 1 / 2 := by linarith

/-- One unit remains available even when the child crosses the terminal cutoff. -/
theorem precisionRank_drop {step q child : ℝ}
    (hs : 0 < step) (hq : (1 / 2 : ℝ) < q)
    (hchild : child ≤ q - step) :
    precisionRank step child + 1 ≤ precisionRank step q := by
  by_cases hc : child ≤ (1 / 2 : ℝ)
  · rw [(precisionRank_zero_iff hs).2 hc]
    exact (precisionRank_pos_iff hs).2 hq
  · apply precisionRank_drop_units 1 hs (lt_of_not_ge hc)
    simpa using (show child + step ≤ q by linarith)

end AcceleratedLogConcave.Oracle.Precision
