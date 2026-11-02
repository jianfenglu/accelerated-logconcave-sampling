import AcceleratedLogConcave.Oracle.RecursiveOccurrenceStep
import AcceleratedLogConcave.Oracle.RecursiveCallPath
import AcceleratedLogConcave.Oracle.RecursiveStabilityEnvelope
import AcceleratedLogConcave.Oracle.FixedTapeStabilityAbsorption

/-! Uniform fixed-tape stability on an explicitly admissible state predicate.
Closure and smallness are hypotheses about actual occurrences. They are not
derived from a root schedule here. Only `actualRowMass` and its row certificate
are used from RecursiveStabilityEnvelope; no auxiliary family envelope is used. -/
noncomputable section
set_option autoImplicit false
namespace AcceleratedLogConcave.Oracle.RecursiveCall
open Numerics.AffineGraph RecursiveExecutable FixedTapeStability Precision TapeLowering
open scoped BigOperators NNReal

variable {d m n ns a h : ℕ} (C : Source m n ns)
    (anchors : Fin a ≃ C.M.Anchor) (seeds : Fin h ≃ Fin m × C.M.Kernel)
    (ht : 0 < C.t) (htq : C.t ≤ 1/4) (scale : ℝ)

local notation "E" => meanCore C.M C.nodes anchors seeds C.S C.snodes
  C.Ds C.δ C.t C.w C.layers ht htq scale

/-- Fuel induction over actual calls. Terminal states require no radius or width
sign. The nonterminal smallness and occurrence closure remain explicit inputs. -/
theorem childStable_admissible_fuel
    (G : Point d → Point d) (L : ℝ≥0)
    (hG : LipschitzWith L (fun x => scale • G (scale • x)))
    (hm : 0 < m) (hpsi : C.M.psi ≤ C.M.R^4)
    (η : ℝ) (H : ℕ) (hη : 0 ≤ η) (hη100 : η ≤ 1/100)
    (hheight : 20*(H : ℝ)*η ≤ 1/2)
    (P : State → Prop)
    (hclosed : ∀ p o c, P p → Edge C p o c → P c)
    (hradius : ∀ p, P p → 1/2 < p.precision → 0 ≤ p.radius)
    (hrow : ∀ p, P p → 1/2 < p.precision →
      (L : ℝ) * actualRowMass C.M p.radius p.width ≤ η)
    (hsize : ∀ p, P p → 1/2 < p.precision → (L : ℝ)*p.radius^2 ≤ η)
    (fuel : ℕ) (p : State) (hf : fuel ≤ H) (hp : P p)
    (hrank : precisionRank C.t p.precision ≤ fuel) :
    ChildStable (E p.radius p.width p.precision).program
      (E p.radius p.width p.precision).coefficient G ((L : ℝ)*(1+20*η)^fuel) := by
  induction fuel generalizing p with
  | zero =>
    have hq : p.precision ≤ 1/2 := (precisionRank_zero_iff ht).mp (by omega)
    simpa only [pow_zero, mul_one] using
      meanCore_childStable_terminal C.M C.nodes anchors seeds C.S C.snodes
        C.Ds C.δ C.t C.w C.layers ht htq scale p.radius p.width p.precision hq G L hG
  | succ fuel ih =>
    by_cases hq : p.precision ≤ 1/2
    · apply (meanCore_childStable_terminal C.M C.nodes anchors seeds C.S C.snodes
        C.Ds C.δ C.t C.w C.layers ht htq scale p.radius p.width p.precision hq G L hG).mono
      have hpow := (height_factor_mem H (fuel+1) hη hf hheight).1
      nlinarith [L.coe_nonneg]
    · have hq' : 1/2 < p.precision := lt_of_not_ge hq
      let F : ℝ := (1+20*η)^fuel
      have hF := height_factor_mem H fuel hη (by omega) hheight
      have hc (o : Occurrence C.layers n ns m) :
          ChildStable (E (C.child p o).radius (C.child p o).width (C.child p o).precision).program
            (E (C.child p o).radius (C.child p o).width (C.child p o).precision).coefficient G
            (F*(L : ℝ)) := by
        have he : Edge C p o (C.child p o) := ⟨hq', rfl⟩
        have hd := he.rank_drop ht htq
        have hi := ih (C.child p o) (by omega) (hclosed p o _ hp he) (by omega)
        simpa only [F, mul_comm] using hi
      have hs := childStable_occurrence_step C anchors seeds ht htq scale p hq' G
        (F*(L : ℝ)) (actualRowMass C.M p.radius p.width) hm (hradius p hp hq')
        (mul_nonneg (le_trans (by norm_num) hF.1) L.coe_nonneg) hpsi hc
        (fun _ => (actualRowMass C.M p.radius p.width).coe_nonneg)
        (fun _ => row_mass_le_actualRowMass C.M p.radius p.width)
      apply hs.mono
      have hb : (backwardEnd C.M.R)^2 ≤ 1 := by
        nlinarith [C.M.backwardEnd_pos, C.M.backwardEnd_lt_one]
      calc
        _ ≤ F*(L : ℝ)*(1+20*η) := meanGrowth_le_linear C.layers
          (le_trans (by norm_num) hF.1) hF.2 L.coe_nonneg (hradius p hp hq')
          (actualRowMass C.M p.radius p.width).coe_nonneg hη hη100 hb
          (hsize p hp hq') (hrow p hp hq')
        _ = (L : ℝ)*(1+20*η)^(fuel+1) := by dsimp [F]; rw [pow_succ]; ring

/-- The height budget absorbs the actual recursion into `2*L`. This does not
instantiate the admissible predicate from a root schedule. -/
theorem childStable_admissible_uniform
    (G : Point d → Point d) (L : ℝ≥0)
    (hG : LipschitzWith L (fun x => scale • G (scale • x)))
    (hm : 0 < m) (hpsi : C.M.psi ≤ C.M.R^4)
    (η : ℝ) (H : ℕ) (hη : 0 ≤ η) (hη100 : η ≤ 1/100)
    (hheight : 20*(H : ℝ)*η ≤ 1/2)
    (P : State → Prop)
    (hclosed : ∀ p o c, P p → Edge C p o c → P c)
    (hradius : ∀ p, P p → 1/2 < p.precision → 0 ≤ p.radius)
    (hrow : ∀ p, P p → 1/2 < p.precision →
      (L : ℝ) * actualRowMass C.M p.radius p.width ≤ η)
    (hsize : ∀ p, P p → 1/2 < p.precision → (L : ℝ)*p.radius^2 ≤ η)
    (p : State) (hp : P p) (hrank : precisionRank C.t p.precision ≤ H) :
    ChildStable (E p.radius p.width p.precision).program
      (E p.radius p.width p.precision).coefficient G (2*(L : ℝ)) := by
  apply (childStable_admissible_fuel C anchors seeds ht htq scale G L hG hm hpsi
    η H hη hη100 hheight P hclosed hradius hrow hsize H p le_rfl hp hrank).mono
  have hF := (height_factor_mem H H hη le_rfl hheight).2
  nlinarith [L.coe_nonneg]

/-- Literal output displacement with identical entering momentum and complete
raw tape. Coefficient tables vary with the state and are the actual tables. -/
theorem admissible_sub_le_uniform
    (G : Point d → Point d) (L : ℝ≥0)
    (hG : LipschitzWith L (fun x => scale • G (scale • x)))
    (hm : 0 < m) (hpsi : C.M.psi ≤ C.M.R^4)
    (η : ℝ) (H : ℕ) (hη : 0 ≤ η) (hη100 : η ≤ 1/100)
    (hheight : 20*(H : ℝ)*η ≤ 1/2)
    (P : State → Prop)
    (hclosed : ∀ p o c, P p → Edge C p o c → P c)
    (hradius : ∀ p, P p → 1/2 < p.precision → 0 ≤ p.radius)
    (hrow : ∀ p, P p → 1/2 < p.precision →
      (L : ℝ) * actualRowMass C.M p.radius p.width ≤ η)
    (hsize : ∀ p, P p → 1/2 < p.precision → (L : ℝ)*p.radius^2 ≤ η)
    (p : State) (hp : P p) (hrank : precisionRank C.t p.precision ≤ H)
    (momentum x y : Point d) (tape : Tape d (E p.radius p.width p.precision).program) :
    ‖RetainedMeanFinalBatch.childPoint (run (E p.radius p.width p.precision).program G
        ⟨(E p.radius p.width p.precision).coefficient, x, momentum⟩ Env.empty tape) -
      RetainedMeanFinalBatch.childPoint (run (E p.radius p.width p.precision).program G
        ⟨(E p.radius p.width p.precision).coefficient, y, momentum⟩ Env.empty tape)‖ ≤
      2*(L : ℝ)*‖x-y‖ :=
  childStable_tape _ _ G _ (childStable_admissible_uniform C anchors seeds ht htq scale
    G L hG hm hpsi η H hη hη100 hheight P hclosed hradius hrow hsize p hp hrank)
    momentum x y tape

end AcceleratedLogConcave.Oracle.RecursiveCall
