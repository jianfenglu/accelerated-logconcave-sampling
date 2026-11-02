import AcceleratedLogConcave.Tensor.SingleEdgeAllProper
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic

/-!

-/
noncomputable section
open scoped BigOperators Classical ContDiff
open Function
namespace AcceleratedLogConcave.Tensor.ActualCoefficient
open EdgeClosure

abbrev Space (D : ℕ) := EuclideanSpace ℝ (Fin D)
abbrev basis (D : ℕ) := EuclideanSpace.basisFun (Fin D) ℝ

variable {D : ℕ}
variable {A B C G : Type*} [Fintype A] [Fintype B] [Fintype C]
  [DecidableEq A] [DecidableEq B] [DecidableEq C]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- Basis expansion in an actual continuous linear map. No positivity of D. -/
theorem linear_basis_expansion (L : Space D →L[ℝ] G) (v : Space D) :
    L v = ∑ w : Fin D, inner ℝ (basis D w) v • L (basis D w) := by
  have h := congrArg L ((basis D).sum_repr' v)
  simpa only [map_sum, map_smul] using h.symm

/-- Literal matrix multiplication with its actual left/right order. -/
theorem inner_comp_basis (L R : Space D →L[ℝ] Space D) (i o : Fin D) :
    inner ℝ (basis D o) ((L.comp R) (basis D i)) =
      ∑ w : Fin D, inner ℝ (basis D o) (L (basis D w)) *
        inner ℝ (basis D w) (R (basis D i)) := by
  change inner ℝ (basis D o) (L (R (basis D i))) = _
  rw [linear_basis_expansion L (R (basis D i))]
  simp only [inner_sum, inner_smul_right]
  apply Finset.sum_congr rfl
  intro w _
  exact mul_comm _ _

/-- Readout slots include every ordinary input and output coordinate.
The generic readout is a linear functional, not a norm/equality hypothesis. -/
def mapCoeff (T : ContinuousMultilinearMap ℝ (fun _ : A => Space D) G)
    (readout : (C → Fin D) → G →L[ℝ] ℝ) : Coeff (A ⊕ C) D :=
  WithLp.toLp 2 (fun a => readout (fun c => a (.inr c))
    (T (fun i => basis D (a (.inl i)))))

def vectorCoeff (T : ContinuousMultilinearMap ℝ (fun _ : A => Space D) (Space D)) :
    Coeff (A ⊕ Unit) D :=
  mapCoeff T (fun a => innerSL ℝ (basis D (a ())))

/-- Wrapper order is derivative slots, ordinary input, ordinary output. -/
def operatorCoeff
    (T : ContinuousMultilinearMap ℝ (fun _ : A => Space D) (Space D →L[ℝ] Space D)) :
    Coeff ((A ⊕ Unit) ⊕ Unit) D :=
  WithLp.toLp 2 (fun a => inner ℝ (basis D (a (.inr ())))
    ((T (fun i => basis D (a (.inl (.inl i)))))
      (basis D (a (.inl (.inr ()))))))

/-- Actual map evaluation on ALL retained indices, not a directional norm. -/
def composeCoeff
    (T : ContinuousMultilinearMap ℝ (fun _ : A => Space D) (Space D →L[ℝ] Space D))
    (U : ContinuousMultilinearMap ℝ (fun _ : B => Space D) (Space D →L[ℝ] Space D)) :
    Coeff ((A ⊕ Unit) ⊕ (B ⊕ Unit)) D :=
  WithLp.toLp 2 (fun a => inner ℝ (basis D (a (.inl (.inr ()))))
    (((T (fun i => basis D (a (.inl (.inl i))))).comp
      (U (fun i => basis D (a (.inr (.inl i))))))
      (basis D (a (.inr (.inr ()))))))

omit [DecidableEq A] [DecidableEq B] in
/-- This supplies the previously missing actual-map equality. -/
theorem operatorCompose_eq_actual
    (T : ContinuousMultilinearMap ℝ (fun _ : A => Space D) (Space D →L[ℝ] Space D))
    (U : ContinuousMultilinearMap ℝ (fun _ : B => Space D) (Space D →L[ℝ] Space D)) :
    operatorCompose D (operatorCoeff T) (operatorCoeff U) = composeCoeff T U := by
  ext a
  exact (inner_comp_basis
    (T (fun i => basis D (a (.inl (.inl i)))))
    (U (fun i => basis D (a (.inr (.inl i)))))
    (a (.inr (.inr ()))) (a (.inl (.inr ())))).symm

/-- All proper rectangular cuts of the actual composition coefficient.
Empty A and B, repeated coordinate labels, and D=0 remain allowed. -/
theorem composeCoeff_allProper
    (T : ContinuousMultilinearMap ℝ (fun _ : A => Space D) (Space D →L[ℝ] Space D))
    (U : ContinuousMultilinearMap ℝ (fun _ : B => Space D) (Space D →L[ℝ] Space D))
    {CT CU : ℝ} (hCT : 0 ≤ CT) (hCU : 0 ≤ CU)
    (hT : AllProper D (operatorCoeff T) CT) (hU : AllProper D (operatorCoeff U) CU) :
    AllProper D (composeCoeff T U) (CT * CU) := by
  rw [← operatorCompose_eq_actual]
  exact operatorCompose_allProper D _ _ hCT hCU hT hU

/-- Keep literal external subtype slots of contractAt. -/
abbrev AttachSlots (p : A) :=
  {s : A ⊕ C // s ≠ Sum.inl p} ⊕ {s : B ⊕ Unit // s ≠ Sum.inr ()}

/-- The selected direction is zero only as the base of Function.update;
that slot is immediately replaced by the actual branch value. -/
def attachmentBase (p : A) (a : AttachSlots (B := B) (C := C) p → Fin D) : A → Space D :=
  fun j => if h : j = p then 0 else basis D (a (.inl ⟨.inl j, by simpa using h⟩))

def attachmentBranch (p : A)
    (a : AttachSlots (B := B) (C := C) p → Fin D) : B → Space D :=
  fun j => basis D (a (.inr ⟨.inl j, by simp⟩))

/-- Actual insertion into a selected derivative slot of T.
C retains every readout slot; no contracted output is silently discarded. -/
def attachCoeff (p : A)
    (T : ContinuousMultilinearMap ℝ (fun _ : A => Space D) G)
    (readout : (C → Fin D) → G →L[ℝ] ℝ)
    (V : ContinuousMultilinearMap ℝ (fun _ : B => Space D) (Space D)) :
    Coeff (AttachSlots (B := B) (C := C) p) D :=
  WithLp.toLp 2 (fun a =>
    readout (fun c => a (.inl ⟨.inr c, by simp⟩))
      (T (Function.update (attachmentBase p a) p (V (attachmentBranch p a)))))

/-- Arbitrary original derivative slot, exact scalar basis-contraction identity. -/
theorem contractAt_eq_actual_attach (p : A)
    (T : ContinuousMultilinearMap ℝ (fun _ : A => Space D) G)
    (readout : (C → Fin D) → G →L[ℝ] ℝ)
    (V : ContinuousMultilinearMap ℝ (fun _ : B => Space D) (Space D)) :
    contractAt D (Sum.inl p) (Sum.inr ()) (mapCoeff T readout) (vectorCoeff V) =
      attachCoeff p T readout V := by
  ext a
  let L : Space D →L[ℝ] ℝ :=
    (readout (fun c => a (.inl ⟨.inr c, by simp⟩))).comp
      (T.toContinuousLinearMap (attachmentBase p a) p)
  have h := linear_basis_expansion L (V (attachmentBranch p a))
  change (∑ w : Fin D, _ * _) = _
  rw [show attachCoeff p T readout V a = L (V (attachmentBranch p a)) from rfl]
  rw [h]
  apply Finset.sum_congr rfl
  intro w _
  have hdirs : (fun j => basis D
      (insertEdge D (Sum.inl p) (fun z => a (.inl z)) w (Sum.inl j))) =
      Function.update (attachmentBase p a) p (basis D w) := by
    funext j
    by_cases hj : j = p
    · subst j; simp [insertEdge]
    · simp [insertEdge, attachmentBase, hj]
  change
    readout (fun c => a (.inl ⟨.inr c, by simp⟩))
        (T (fun j => basis D
          (insertEdge D (Sum.inl p) (fun z => a (.inl z)) w (Sum.inl j)))) *
      inner ℝ (basis D w) (V (attachmentBranch p a)) =
    inner ℝ (basis D w) (V (attachmentBranch p a)) *
      readout (fun c => a (.inl ⟨.inr c, by simp⟩))
        (T (Function.update (attachmentBase p a) p (basis D w)))
  rw [hdirs, mul_comm]

/-- Positive-order vector attachment, now on actual map evaluations.
Nonempty C keeps root rank >=2; Nonempty B rules out the false rank-one bound. -/
theorem attachCoeff_allProper [Nonempty C] [Nonempty B] (p : A)
    (T : ContinuousMultilinearMap ℝ (fun _ : A => Space D) G)
    (readout : (C → Fin D) → G →L[ℝ] ℝ)
    (V : ContinuousMultilinearMap ℝ (fun _ : B => Space D) (Space D))
    {CT CV : ℝ} (hCT : 0 ≤ CT) (hCV : 0 ≤ CV)
    (hT : AllProper D (mapCoeff T readout) CT)
    (hV : AllProper D (vectorCoeff V) CV) :
    AllProper D (attachCoeff p T readout V) (CT * CV) := by
  let : Nonempty {s : A ⊕ C // s ≠ Sum.inl p} := by
    obtain ⟨c⟩ := ‹Nonempty C›
    exact ⟨⟨.inr c, by simp⟩⟩
  rw [← contractAt_eq_actual_attach]
  exact attachVector_allProper D (Sum.inl p) _ _ hCT hCV hT hV

/-- The operator readout retains BOTH ordinary operator slots. -/
def operatorReadout (a : (Unit ⊕ Unit) → Fin D) :
    (Space D →L[ℝ] Space D) →L[ℝ] ℝ :=
  (innerSL ℝ (basis D (a (.inr ())))).comp
    (ContinuousLinearMap.apply ℝ (Space D) (basis D (a (.inl ()))))

omit [DecidableEq A] in
/-- Reassociating slots identifies generic attachment inputs with operatorCoeff. -/
theorem mapCoeff_operatorReadout
    (T : ContinuousMultilinearMap ℝ (fun _ : A => Space D) (Space D →L[ℝ] Space D)) :
    relabel D (Equiv.sumAssoc A Unit Unit).symm (mapCoeff T operatorReadout) =
      operatorCoeff T := by
  ext a
  rfl

omit [DecidableEq A] in
/-- Reverse chart used to pass an operator endpoint budget into attachment. -/
theorem operatorCoeff_relabel
    (T : ContinuousMultilinearMap ℝ (fun _ : A => Space D) (Space D →L[ℝ] Space D)) :
    relabel D (Equiv.sumAssoc A Unit Unit) (operatorCoeff T) =
      mapCoeff T operatorReadout := by
  ext a
  rfl

/-- Operator-valued derivative root, positive-order vector branch, and ALL
retained derivative/input/output indices. The root may have exactly one
spatial derivative slot; the branch may have any positive order. -/
theorem attach_operator_allProper [Nonempty B] (p : A)
    (T : ContinuousMultilinearMap ℝ (fun _ : A => Space D) (Space D →L[ℝ] Space D))
    (V : ContinuousMultilinearMap ℝ (fun _ : B => Space D) (Space D))
    {CT CV : ℝ} (hCT : 0 ≤ CT) (hCV : 0 ≤ CV)
    (hT : AllProper D (operatorCoeff T) CT)
    (hV : AllProper D (vectorCoeff V) CV) :
    AllProper D (attachCoeff p T operatorReadout V) (CT * CV) := by
  apply attachCoeff_allProper p T operatorReadout V hCT hCV _ hV
  rw [← operatorCoeff_relabel]
  exact hT.relabel (Equiv.sumAssoc A Unit Unit)

/-- Whole finite basis expansion of an actual multilinear map, prior to estimates. -/
theorem multilinear_basis_expansion
    (T : ContinuousMultilinearMap ℝ (fun _ : A => Space D) G) (v : A → Space D) :
    T v = ∑ w : A → Fin D,
      (∏ i, inner ℝ (basis D (w i)) (v i)) • T (fun i => basis D (w i)) := by
  calc
    T v = T (fun i => ∑ j : Fin D, inner ℝ (basis D j) (v i) • basis D j) := by
      congr 1
      funext i
      exact ((basis D).sum_repr' (v i)).symm
    _ = ∑ w : A → Fin D,
        T (fun i => inner ℝ (basis D (w i)) (v i) • basis D (w i)) := T.map_sum _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro w _
      exact T.map_smul_univ _ _

/-- All-index coefficient expansion of the ACTUAL ordered composition derivative.
No jet-tower assumptions and no requested coefficient equality premise.
Mathlib partitions count each labeled set partition once, preserving c.emb. -/
theorem iteratedFDeriv_comp_coefficient
    (g : Space D → G) (f : Space D → Space D) (y : Space D)
    (hg : ContDiffAt ℝ ∞ g (f y)) (hf : ContDiffAt ℝ ∞ f y)
    (n : ℕ) (a : Fin n → Fin D) (L : G →L[ℝ] ℝ) :
    L (iteratedFDeriv ℝ n (g ∘ f) y (fun i => basis D (a i))) =
      ∑ c : OrderedFinpartition n, ∑ w : Fin c.length → Fin D,
        (∏ i, inner ℝ (basis D (w i))
          (iteratedFDeriv ℝ (c.partSize i) f y
            (fun j => basis D (a (c.emb i j))))) *
        L (iteratedFDeriv ℝ c.length g (f y) (fun i => basis D (w i))) := by
  rw [iteratedFDeriv_comp hg hf (by simp : (n : WithTop ℕ∞) ≤ ∞)]
  change L ((∑ c : OrderedFinpartition n,
    c.compAlongOrderedFinpartition (iteratedFDeriv ℝ c.length g (f y))
      (fun i => iteratedFDeriv ℝ (c.partSize i) f y)) (fun i => basis D (a i))) = _
  simp only [sum_apply, map_sum]
  apply Finset.sum_congr rfl
  intro c _
  change L (iteratedFDeriv ℝ c.length g (f y)
    (fun i => iteratedFDeriv ℝ (c.partSize i) f y
      (fun j => basis D (a (c.emb i j))))) = _
  rw [multilinear_basis_expansion]
  simp only [map_sum, map_smul, smul_eq_mul]

/-- Direct specialization to actual operator-valued spatial maps U and Y.
Taking U=firstScaledJet(t, ·), Y=backwardProbabilityTransport(t, ·)
uses standard ContDiffAt premises, never an unknown coefficient estimate. -/
theorem operator_composition_derivative_coefficient
    (U : Space D → (Space D →L[ℝ] Space D)) (Y : Space D → Space D)
    (y : Space D) (hU : ContDiffAt ℝ ∞ U (Y y)) (hY : ContDiffAt ℝ ∞ Y y)
    (n : ℕ) (a : Fin n → Fin D) (i o : Fin D) :
    inner ℝ (basis D o)
      ((iteratedFDeriv ℝ n (U ∘ Y) y (fun j => basis D (a j))) (basis D i)) =
      ∑ c : OrderedFinpartition n, ∑ w : Fin c.length → Fin D,
        (∏ j, inner ℝ (basis D (w j))
          (iteratedFDeriv ℝ (c.partSize j) Y y
            (fun k => basis D (a (c.emb j k))))) *
        inner ℝ (basis D o)
          ((iteratedFDeriv ℝ c.length U (Y y) (fun j => basis D (w j))) (basis D i)) := by
  exact iteratedFDeriv_comp_coefficient U Y y hU hY n a
    (operatorReadout (Sum.elim (fun _ => i) (fun _ => o)))

end AcceleratedLogConcave.Tensor.ActualCoefficient
