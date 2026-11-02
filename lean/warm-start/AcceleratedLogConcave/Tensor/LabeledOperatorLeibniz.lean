import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Tactic

/-!

-/
noncomputable section
open scoped BigOperators ContDiff
namespace LabeledOperatorLeibniz

/-- A left/right assignment of each of n labeled derivative slots.
The head slot is 0; every old slot is shifted by Fin.succ. -/
def Split : ℕ → Type
  | 0 => Unit
  | n + 1 => Split n ⊕ Split n

instance splitFintype : (n : ℕ) → Fintype (Split n)
  | 0 => inferInstanceAs (Fintype Unit)
  | n + 1 => by
    letI := splitFintype n
    exact inferInstanceAs (Fintype (Split n ⊕ Split n))

instance splitDecidableEq : (n : ℕ) → DecidableEq (Split n)
  | 0 => inferInstanceAs (DecidableEq Unit)
  | n + 1 => by
    letI := splitDecidableEq n
    exact inferInstanceAs (DecidableEq (Split n ⊕ Split n))

def leftCount : {n : ℕ} → Split n → ℕ
  | 0, _ => 0
  | _ + 1, .inl s => leftCount s + 1
  | _ + 1, .inr s => leftCount s

def rightCount : {n : ℕ} → Split n → ℕ
  | 0, _ => 0
  | _ + 1, .inl s => rightCount s
  | _ + 1, .inr s => rightCount s + 1

/-- Increasing enumeration of slots assigned to the left factor. -/
def leftEmb : {n : ℕ} → (s : Split n) → Fin (leftCount s) → Fin n
  | 0, _ => Fin.elim0
  | _ + 1, .inl s => Fin.cases 0 (fun j => (leftEmb s j).succ)
  | _ + 1, .inr s => fun j => (leftEmb s j).succ

/-- Increasing enumeration of the complementary slots. -/
def rightEmb : {n : ℕ} → (s : Split n) → Fin (rightCount s) → Fin n
  | 0, _ => Fin.elim0
  | _ + 1, .inl s => fun j => (rightEmb s j).succ
  | _ + 1, .inr s => Fin.cases 0 (fun j => (rightEmb s j).succ)

theorem counts_add : {n : ℕ} → (s : Split n) → leftCount s + rightCount s = n
  | 0, _ => rfl
  | n + 1, .inl s => by simp only [leftCount, rightCount]; have := counts_add s; omega
  | n + 1, .inr s => by simp only [leftCount, rightCount]; have := counts_add s; omega

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- No symmetry or commutation is used: left derivative is composed AFTER right. -/
def term {n : ℕ} (B H : E → (V →L[ℝ] V)) (s : Split n)
    (y : E) (v : Fin n → E) : V →L[ℝ] V :=
  (iteratedFDeriv ℝ (leftCount s) B y (v ∘ leftEmb s)).comp
    (iteratedFDeriv ℝ (rightCount s) H y (v ∘ rightEmb s))

private theorem diff_jet (B : E → (V →L[ℝ] V)) (hB : ContDiff ℝ ∞ B)
    (p : ℕ) (y : E) : DifferentiableAt ℝ (iteratedFDeriv ℝ p B) y :=
  ((hB.iteratedFDeriv_right (m := 1) (by simp)).differentiable (by simp)) y

/-- Evaluation commutes with differentiation, retaining the entire tuple. -/
theorem derivative_jet_eval (B : E → (V →L[ℝ] V)) (hB : ContDiff ℝ ∞ B)
    (p : ℕ) (y u : E) (w : Fin p → E) :
    fderiv ℝ (fun z => iteratedFDeriv ℝ p B z w) y u =
      iteratedFDeriv ℝ (p + 1) B y (Fin.cons u w) := by
  rw [fderiv_continuousMultilinear_apply_const_apply (diff_jet B hB p y)]
  rfl

theorem differentiable_term {n : ℕ} (B H : E → (V →L[ℝ] V))
    (hB : ContDiff ℝ ∞ B) (hH : ContDiff ℝ ∞ H)
    (s : Split n) (y : E) (v : Fin n → E) :
    DifferentiableAt ℝ (fun z => term B H s z v) y :=
  ((diff_jet B hB _ y).continuousMultilinear_apply_const _).clm_comp
    ((diff_jet H hH _ y).continuousMultilinear_apply_const _)

/-- The one-step Leibniz branching identity. New slot 0 is assigned exactly
once to each factor, with all previously retained labels shifted together. -/
theorem derivative_term {n : ℕ} (B H : E → (V →L[ℝ] V))
    (hB : ContDiff ℝ ∞ B) (hH : ContDiff ℝ ∞ H)
    (s : Split n) (y u : E) (v : Fin n → E) :
    fderiv ℝ (fun z => term B H s z v) y u =
      term (n := n+1) B H (Sum.inl s : Split (n + 1)) y (Fin.cons u v) +
      term (n := n+1) B H (Sum.inr s : Split (n + 1)) y (Fin.cons u v) := by
  unfold term
  rw [fderiv_clm_comp
    ((diff_jet B hB _ y).continuousMultilinear_apply_const _)
    ((diff_jet H hH _ y).continuousMultilinear_apply_const _)]
  change
    (iteratedFDeriv ℝ (leftCount s) B y (v ∘ leftEmb s)).comp
      (fderiv ℝ (fun z => iteratedFDeriv ℝ (rightCount s) H z
        (v ∘ rightEmb s)) y u) +
    (fderiv ℝ (fun z => iteratedFDeriv ℝ (leftCount s) B z
        (v ∘ leftEmb s)) y u).comp
      (iteratedFDeriv ℝ (rightCount s) H y (v ∘ rightEmb s)) = _
  rw [derivative_jet_eval H hH, derivative_jet_eval B hB]
  simp only [leftCount, rightCount, leftEmb, rightEmb,
    Function.comp_def, Fin.cons_succ]
  exact add_comm _ _

/-- Arbitrary-order identity for the ACTUAL operator product derivative.
There is one summand for each labeling, including the empty labeling at n=0.
This is equality of operators, not a directional norm estimate. -/
theorem iteratedFDeriv_comp_split (B H : E → (V →L[ℝ] V))
    (hB : ContDiff ℝ ∞ B) (hH : ContDiff ℝ ∞ H)
    (n : ℕ) (y : E) (v : Fin n → E) :
    iteratedFDeriv ℝ n (fun z => (B z).comp (H z)) y v =
      ∑ s : Split n, term B H s y v := by
  induction n generalizing y with
  | zero =>
    change (B y).comp (H y) = ∑ _s : Unit, (B y).comp (H y)
    simp
  | succ n ih =>
    have hp : ContDiff ℝ ∞ (fun z => (B z).comp (H z)) := hB.clm_comp hH
    rw [(diff_jet _ hp n y).iteratedFDeriv_succ_apply_left']
    have heq : (fun z => iteratedFDeriv ℝ n (fun z => (B z).comp (H z)) z
        (Fin.tail v)) = (fun z => ∑ s : Split n, term B H s z (Fin.tail v)) :=
      funext (fun z => ih z (Fin.tail v))
    rw [heq, fderiv_fun_sum (fun s _ => differentiable_term B H hB hH s y _)]
    simp only [sum_apply]
    simp_rw [derivative_term B H hB hH]
    rw [Finset.sum_add_distrib]
    change _ = ∑ s : Split n ⊕ Split n, term (n := n+1) B H s y v
    rw [Fintype.sum_sum_type]
    simp only [Fin.cons_self_tail]



/-- Characteristic function of the retained left subset. -/
def encode : {n : ℕ} → Split n → (Fin n → Bool)
  | 0, _ => Fin.elim0
  | _ + 1, .inl s => Fin.cons true (encode s)
  | _ + 1, .inr s => Fin.cons false (encode s)

def decode : {n : ℕ} → (Fin n → Bool) → Split n
  | 0, _ => ()
  | _ + 1, b => if b 0 then Sum.inl (decode (Fin.tail b)) else Sum.inr (decode (Fin.tail b))

@[simp] theorem decode_encode : {n : ℕ} → (s : Split n) → decode (encode s) = s
  | 0, s => by cases s; rfl
  | _ + 1, .inl s => by simp [decode, encode, decode_encode s, Fin.tail_cons]; rfl
  | _ + 1, .inr s => by simp [decode, encode, decode_encode s, Fin.tail_cons]; rfl

@[simp] theorem encode_decode : {n : ℕ} → (b : Fin n → Bool) → encode (decode b) = b
  | 0, b => by funext i; exact Fin.elim0 i
  | n + 1, b => by
    have ih := encode_decode (Fin.tail b)
    cases h : b 0 <;>
      simp [decode, h, encode, ih] <;>
      funext i <;> refine Fin.cases ?_ (fun j => ?_) i <;> simp [h, Fin.tail]

/-- Bijection proves that each labeled subset appears exactly once, with no
factorials, cardinality grouping, or quotient by repeated coordinate values. -/
def subsetEquiv (n : ℕ) : Split n ≃ Finset (Fin n) where
  toFun s := Finset.univ.filter (fun i => encode s i = true)
  invFun S := decode (fun i => decide (i ∈ S))
  left_inv s := by
    have h : (fun i => decide (i ∈ Finset.univ.filter
        (fun i => encode s i = true))) = encode s := by
      funext i
      cases hi : encode s i <;> simp [hi]
    change decode (fun i => decide (i ∈ Finset.univ.filter
      (fun i => encode s i = true))) = s
    rw [h, decode_encode]
  right_inv S := by
    ext i
    simp [encode_decode]

theorem left_range : {n : ℕ} → (s : Split n) → (i : Fin n) →
    (∃ j, leftEmb s j = i) ↔ encode s i = true
  | 0, _, i => Fin.elim0 i
  | n + 1, .inl s, i => by
    refine Fin.cases ?_ (fun k => ?_) i
    · simp [leftEmb, leftCount, encode, Fin.exists_fin_succ]
    · simp [leftEmb, leftCount, encode, Fin.exists_fin_succ, left_range s k]
      exact fun h => False.elim (Fin.succ_ne_zero k h.symm)
  | n + 1, .inr s, i => by
    refine Fin.cases ?_ (fun k => ?_) i
    · simp [leftEmb, leftCount, encode]
    · simp [leftEmb, leftCount, encode, left_range s k]

theorem right_range : {n : ℕ} → (s : Split n) → (i : Fin n) →
    (∃ j, rightEmb s j = i) ↔ encode s i = false
  | 0, _, i => Fin.elim0 i
  | n + 1, .inl s, i => by
    refine Fin.cases ?_ (fun k => ?_) i
    · simp [rightEmb, rightCount, encode]
    · simp [rightEmb, rightCount, encode, right_range s k]
  | n + 1, .inr s, i => by
    refine Fin.cases ?_ (fun k => ?_) i
    · simp [rightEmb, rightCount, encode, Fin.exists_fin_succ]
    · simp [rightEmb, rightCount, encode, Fin.exists_fin_succ, right_range s k]
      exact fun h => False.elim (Fin.succ_ne_zero k h.symm)

private theorem strictMono_cons_zero {a n : ℕ} (f : Fin a → Fin n)
    (hf : StrictMono f) : StrictMono (Fin.cases 0 (fun i => (f i).succ)) := by
  intro i j
  refine Fin.cases ?_ (fun i => ?_) i
  · refine Fin.cases ?_ (fun j => ?_) j
    · simp
    · simp
  · refine Fin.cases ?_ (fun j => ?_) j
    · simp
    · simpa using (fun h => hf h)

theorem left_strictMono : {n : ℕ} → (s : Split n) → StrictMono (leftEmb s)
  | 0, _ => by intro i; exact Fin.elim0 i
  | n + 1, .inl s => strictMono_cons_zero _ (left_strictMono s)
  | n + 1, .inr s => by
    intro i j hij
    simpa [leftEmb] using left_strictMono s hij

theorem right_strictMono : {n : ℕ} → (s : Split n) → StrictMono (rightEmb s)
  | 0, _ => by intro i; exact Fin.elim0 i
  | n + 1, .inl s => by
    intro i j hij
    simpa [rightEmb] using right_strictMono s hij
  | n + 1, .inr s => strictMono_cons_zero _ (right_strictMono s)

/-- Exact finite subset and complement embeddings, not cardinality surrogates. -/
abbrev subsetLeftEmb {n : ℕ} (S : Finset (Fin n)) := leftEmb ((subsetEquiv n).symm S)
abbrev subsetRightEmb {n : ℕ} (S : Finset (Fin n)) := rightEmb ((subsetEquiv n).symm S)

theorem subset_left_range {n : ℕ} (S : Finset (Fin n)) (i : Fin n) :
    (∃ j, subsetLeftEmb S j = i) ↔ i ∈ S := by
  rw [subsetLeftEmb, left_range]
  change encode (decode (fun j => decide (j ∈ S))) i = true ↔ i ∈ S
  simp

theorem subset_right_range {n : ℕ} (S : Finset (Fin n)) (i : Fin n) :
    (∃ j, subsetRightEmb S j = i) ↔ i ∉ S := by
  rw [subsetRightEmb, right_range]
  change encode (decode (fun j => decide (j ∈ S))) i = false ↔ i ∉ S
  simp

/-- Subset-labeled Leibniz formula. Sizes are the counts of the displayed
increasing enumerations; range theorems identify them literally as S and Sᶜ. -/
theorem iteratedFDeriv_comp_subsets (B H : E → (V →L[ℝ] V))
    (hB : ContDiff ℝ ∞ B) (hH : ContDiff ℝ ∞ H)
    (n : ℕ) (y : E) (v : Fin n → E) :
    iteratedFDeriv ℝ n (fun z => (B z).comp (H z)) y v =
      ∑ S : Finset (Fin n),
        (iteratedFDeriv ℝ (leftCount ((subsetEquiv n).symm S)) B y
          (v ∘ subsetLeftEmb S)).comp
        (iteratedFDeriv ℝ (rightCount ((subsetEquiv n).symm S)) H y
          (v ∘ subsetRightEmb S)) := by
  rw [iteratedFDeriv_comp_split B H hB hH]
  have h := (subsetEquiv n).sum_comp (fun S => term B H ((subsetEquiv n).symm S) y v)
  simp only [Equiv.symm_apply_apply] at h
  change _ = _ at h
  simpa only [term, subsetLeftEmb, subsetRightEmb] using h



theorem leftCount_card {n : ℕ} (s : Split n) :
    leftCount s = ((subsetEquiv n) s).card := by
  have heq : Finset.univ.image (leftEmb s) = (subsetEquiv n) s := by
    ext i
    simp [subsetEquiv, left_range]
  calc
    leftCount s = (Finset.univ : Finset (Fin (leftCount s))).card := by simp
    _ = (Finset.univ.image (leftEmb s)).card :=
      (Finset.card_image_of_injective _ (left_strictMono s).injective).symm
    _ = _ := congrArg Finset.card heq

theorem rightCount_card {n : ℕ} (s : Split n) :
    rightCount s = (Finset.univ \ ((subsetEquiv n) s)).card := by
  have heq : Finset.univ.image (rightEmb s) = Finset.univ \ (subsetEquiv n) s := by
    ext i
    simp [subsetEquiv, right_range]
  calc
    rightCount s = (Finset.univ : Finset (Fin (rightCount s))).card := by simp
    _ = (Finset.univ.image (rightEmb s)).card :=
      (Finset.card_image_of_injective _ (right_strictMono s).injective).symm
    _ = _ := congrArg Finset.card heq

theorem subset_leftCount {n : ℕ} (S : Finset (Fin n)) :
    leftCount ((subsetEquiv n).symm S) = S.card := by
  simpa using leftCount_card ((subsetEquiv n).symm S)

theorem subset_rightCount {n : ℕ} (S : Finset (Fin n)) :
    rightCount ((subsetEquiv n).symm S) = n - S.card := by
  have hc := counts_add ((subsetEquiv n).symm S)
  rw [subset_leftCount] at hc
  omega

/-- The n=0 identity has its one empty labeling, not a dropped empty sum. -/
theorem order_zero (B H : E → (V →L[ℝ] V)) (y : E) (v : Fin 0 → E) :
    iteratedFDeriv ℝ 0 (fun z => (B z).comp (H z)) y v =
      ∑ s : Split 0, term B H s y v := by
  change (B y).comp (H y) = ∑ _s : Unit, (B y).comp (H y)
  simp

end LabeledOperatorLeibniz
