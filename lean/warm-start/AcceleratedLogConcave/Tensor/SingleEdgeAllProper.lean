import AcceleratedLogConcave.Tensor.SingleEdgeGrouped

/-!

-/
noncomputable section
open scoped BigOperators Classical
namespace AcceleratedLogConcave.Tensor.EdgeClosure

variable {X Y : Type*} [Fintype X] [Fintype Y]
  [DecidableEq X] [DecidableEq Y]

/-- All genuine rectangular proper cuts; the output is an ordinary slot. -/
def AllProper (D : ℕ) (T : Coeff X D) (C : ℝ) : Prop :=
  ∀ S : Finset X, NontrivialSplit S → splitNorm D S T ≤ C

/-- Relabel all slots, without dropping any coefficient. -/
def relabel (D : ℕ) (e : X ≃ Y) (T : Coeff X D) : Coeff Y D :=
  WithLp.toLp 2 (fun a => T (a ∘ e))

omit [DecidableEq X] [DecidableEq Y] in
@[simp] theorem relabel_apply (D : ℕ) (e : X ≃ Y) (T : Coeff X D)
    (a : Y → Fin D) : relabel D e T a = T (a ∘ e) := rfl

/-- Explicit restriction, used for both sides of an arbitrary rectangular cut. -/
def subtypeCongr (e : X ≃ Y) (p : X → Prop) (q : Y → Prop)
    (h : ∀ x, p x ↔ q (e x)) : {x // p x} ≃ {y // q y} where
  toFun x := ⟨e x.val, (h x.val).mp x.property⟩
  invFun y := ⟨e.symm y.val, (h (e.symm y.val)).mpr (by simpa using y.property)⟩
  left_inv x := by apply Subtype.ext; exact e.symm_apply_apply x.val
  right_inv y := by apply Subtype.ext; exact e.apply_symm_apply y.val

/-- Exact Euclidean rectangular norm transport, with no dimensional assumption. -/
theorem splitNorm_relabel (D : ℕ) (e : X ≃ Y)
    (S : Finset X) (R : Finset Y) (h : ∀ x, x ∈ S ↔ e x ∈ R)
    (T : Coeff X D) :
    splitNorm D R (relabel D e T) = splitNorm D S T := by
  let er := subtypeCongr e (fun x => x ∈ S) (fun y => y ∈ R) h
  let ec := subtypeCongr e (fun x => x ∉ S) (fun y => y ∉ R)
    (fun x => not_congr (h x))
  let fr : LeftAssignment D R ≃ LeftAssignment D S :=
    (Equiv.arrowCongr er (Equiv.refl (Fin D))).symm
  let fc : RightAssignment D R ≃ RightAssignment D S :=
    (Equiv.arrowCongr ec (Equiv.refl (Fin D))).symm
  have he : (fun r c => unfoldEquiv D S T (fr r) (fc c)) =
      unfoldEquiv D R (relabel D e T) := by
    funext r c
    rw [unfold_apply, unfold_apply]
    change T _ = T _
    apply congrArg (fun a => T a)
    funext x
    by_cases hx : x ∈ S
    · have hy := (h x).mp hx
      simp [fr, er, subtypeCongr, Equiv.arrowCongr, hx, hy,
        Function.comp_def]
    · have hy : e x ∉ R := fun hy => hx ((h x).mpr hy)
      simp [fc, ec, subtypeCongr, Equiv.arrowCongr, hx, hy,
        Function.comp_def]
  have hn := matrixCLM_reindex_norm (unfoldEquiv D S T) fr fc
  rw [he] at hn
  exact hn

/-- All-proper bounds survive arbitrary bijective slot renaming. -/
theorem AllProper.relabel {D : ℕ} {T : Coeff X D} {C : ℝ}
    (hT : AllProper D T C) (e : X ≃ Y) : AllProper D (relabel D e T) C := by
  intro R hR
  let S : Finset X := Finset.univ.filter (fun x => e x ∈ R)
  have hs (x : X) : x ∈ S ↔ e x ∈ R := by simp [S]
  have hp : NontrivialSplit S := by
    rcases hR with ⟨⟨y, hy⟩, ⟨z, hz⟩⟩
    refine ⟨⟨e.symm y, (hs _).mpr (by simpa using hy)⟩, ?_⟩
    refine ⟨e.symm z, Finset.mem_compl.mpr ?_⟩
    intro hz'
    have := (hs _).mp hz'
    exact (Finset.mem_compl.mp hz) (by simpa using this)
  rw [splitNorm_relabel D e S R hs T]
  exact hT S hp

/-- Canonical column/row decomposition of a slot set, including empty groups. -/
def cutChart (S : Finset X) : X ≃ {x // x ∉ S} ⊕ {x // x ∈ S} where
  toFun x := if hx : x ∈ S then .inr ⟨x,hx⟩ else .inl ⟨x,hx⟩
  invFun := Sum.elim Subtype.val Subtype.val
  left_inv x := by dsimp; split_ifs <;> rfl
  right_inv x := by
    cases x with
    | inl x => simp [x.property]
    | inr x => simp [x.property]

section Charts
variable {AC AR BC BR : Type*}

/-- Move only the edge slot; do not exchange any tensor factors. -/
def moveEdge : ((BC ⊕ BR) ⊕ Unit) ≃ ((Unit ⊕ BC) ⊕ BR) where
  toFun
    | .inl (.inl b) => .inl (.inr b)
    | .inl (.inr b) => .inr b
    | .inr u => .inl (.inl u)
  invFun
    | .inl (.inl u) => .inr u
    | .inl (.inr b) => .inl (.inl b)
    | .inr b => .inl (.inr b)
  left_inv s := by rcases s with (b | b) | u <;> rfl
  right_inv s := by rcases s with (u | b) | b <;> rfl

/-- Column and row grouping on all retained external slots. -/
def fourShuffle : ((AC ⊕ AR) ⊕ (BC ⊕ BR)) ≃ ((AC ⊕ BC) ⊕ (AR ⊕ BR)) where
  toFun
    | .inl (.inl a) => .inl (.inl a)
    | .inl (.inr a) => .inr (.inl a)
    | .inr (.inl b) => .inl (.inr b)
    | .inr (.inr b) => .inr (.inr b)
  invFun
    | .inl (.inl a) => .inl (.inl a)
    | .inl (.inr b) => .inr (.inl b)
    | .inr (.inl a) => .inl (.inr a)
    | .inr (.inr b) => .inr (.inr b)
  left_inv s := by rcases s with (a | a) | (b | b) <;> rfl
  right_inv s := by rcases s with (a | b) | (a | b) <;> rfl
end Charts

section Edge
variable {A B : Type*} [Fintype A] [Fintype B]
  [DecidableEq A] [DecidableEq B]

/-- Literal one-edge contraction; every external index is retained. -/
def join (D : ℕ) (T : Coeff (A ⊕ Unit) D) (U : Coeff (B ⊕ Unit) D) :
    Coeff (A ⊕ B) D :=
  WithLp.toLp 2 (fun a => ∑ w : Fin D,
    T (Sum.elim (fun i => a (.inl i)) (fun _ => w)) *
    U (Sum.elim (fun i => a (.inr i)) (fun _ => w)))

omit [DecidableEq A] [DecidableEq B] in
@[simp] theorem join_apply (D : ℕ) (T : Coeff (A ⊕ Unit) D)
    (U : Coeff (B ⊕ Unit) D) (a : (A ⊕ B) → Fin D) :
    join D T U a = ∑ w : Fin D,
      T (Sum.elim (fun i => a (.inl i)) (fun _ => w)) *
      U (Sum.elim (fun i => a (.inr i)) (fun _ => w)) := rfl

omit [DecidableEq A] [DecidableEq B] in
/-- The orientation change is a literal equality, not a transpose estimate. -/
theorem join_swap (D : ℕ) (T : Coeff (A ⊕ Unit) D)
    (U : Coeff (B ⊕ Unit) D) :
    relabel D (Equiv.sumComm B A) (join D U T) = join D T U := by
  ext a
  dsimp only [relabel, join]
  apply Finset.sum_congr rfl
  intro w _
  exact mul_comm _ _

/-- Endpoint and external slot charts for a fixed external cut. -/
def chartA (SA : Finset A) : (A ⊕ Unit) ≃
    ({a // a ∉ SA} ⊕ ({a // a ∈ SA} ⊕ Unit)) :=
  (Equiv.sumCongr (cutChart SA) (Equiv.refl Unit)).trans (Equiv.sumAssoc _ _ _)

def chartB (SB : Finset B) : (B ⊕ Unit) ≃
    ((Unit ⊕ {b // b ∉ SB}) ⊕ {b // b ∈ SB}) :=
  (Equiv.sumCongr (cutChart SB) (Equiv.refl Unit)).trans moveEdge

def chartOut (SA : Finset A) (SB : Finset B) : (A ⊕ B) ≃
    (({a // a ∉ SA} ⊕ {b // b ∉ SB}) ⊕
      ({a // a ∈ SA} ⊕ {b // b ∈ SB})) :=
  (Equiv.sumCongr (cutChart SA) (cutChart SB)).trans fourShuffle

/-- Full coefficient identity with the repaired grouped implementation.
This equality quantifies over arbitrary complete assignments, not pure tensors. -/
theorem join_grouped (D : ℕ) (SA : Finset A) (SB : Finset B)
    (T : Coeff (A ⊕ Unit) D) (U : Coeff (B ⊕ Unit) D) :
    relabel D (chartOut SA SB) (join D T U) =
      SingleEdge.contract D (relabel D (chartA SA) T) (relabel D (chartB SB) U) := by
  ext a
  dsimp only [relabel, join, SingleEdge.contract]
  apply Finset.sum_congr rfl
  intro w _
  congr 1
  · apply congrArg (fun f => T f)
    funext s
    cases s with
    | inl i =>
      by_cases hi : i ∈ SA <;>
        simp [chartOut, chartA, fourShuffle, cutChart, hi, Function.comp_def]
    | inr u => cases u; rfl
  · apply congrArg (fun f => U f)
    funext s
    cases s with
    | inl i =>
      by_cases hi : i ∈ SB <;>
        simp [chartOut, chartB, fourShuffle, moveEdge, cutChart, hi, Function.comp_def]
    | inr u => cases u; rfl

/-- Fixed-cut closure in the first edge orientation. Only combinatorial
witnesses select the orientation; endpoint bounds are all-proper bounds. -/
theorem join_cut_forward (D : ℕ) (T : Coeff (A ⊕ Unit) D)
    (U : Coeff (B ⊕ Unit) D) {CA CB : ℝ} (hCA : 0 ≤ CA) (hCB : 0 ≤ CB)
    (hT : AllProper D T CA) (hU : AllProper D U CB)
    (S : Finset (A ⊕ B))
    (hac : ∃ a : A, Sum.inl a ∉ S) (hbr : ∃ b : B, Sum.inr b ∈ S) :
    splitNorm D S (join D T U) ≤ CA * CB := by
  let SA : Finset A := Finset.univ.filter (fun a => Sum.inl a ∈ S)
  let SB : Finset B := Finset.univ.filter (fun b => Sum.inr b ∈ S)
  have hchart (s : A ⊕ B) : s ∈ S ↔ chartOut SA SB s ∈ outputSlots := by
    cases s with
    | inl a =>
      by_cases h : Sum.inl a ∈ S <;>
        simp [chartOut, cutChart, fourShuffle, SA, h]
    | inr b =>
      by_cases h : Sum.inr b ∈ S <;>
        simp [chartOut, cutChart, fourShuffle, SB, h]
  let : Nonempty {a // a ∉ SA} := by
    obtain ⟨a, ha⟩ := hac
    exact ⟨⟨a, by simpa [SA] using ha⟩⟩
  let : Nonempty {b // b ∈ SB} := by
    obtain ⟨b, hb⟩ := hbr
    exact ⟨⟨b, by simpa [SB] using hb⟩⟩
  rw [← splitNorm_relabel D (chartOut SA SB) S outputSlots hchart,
    join_grouped]
  exact SingleEdge.contract_splitNorm_le_of_allSplits D _ _ hCA hCB
    (hT.relabel (chartA SA)) (hU.relabel (chartB SB))

/-- The opposite edge orientation, established by swapping endpoint labels
and transporting both external rectangular assignment spaces exactly. -/
theorem join_cut_reverse (D : ℕ) (T : Coeff (A ⊕ Unit) D)
    (U : Coeff (B ⊕ Unit) D) {CA CB : ℝ} (hCA : 0 ≤ CA) (hCB : 0 ≤ CB)
    (hT : AllProper D T CA) (hU : AllProper D U CB)
    (S : Finset (A ⊕ B))
    (har : ∃ a : A, Sum.inl a ∈ S) (hbc : ∃ b : B, Sum.inr b ∉ S) :
    splitNorm D S (join D T U) ≤ CA * CB := by
  let R : Finset (B ⊕ A) :=
    Finset.univ.filter (fun s => Equiv.sumComm B A s ∈ S)
  have hr (s : B ⊕ A) : s ∈ R ↔ Equiv.sumComm B A s ∈ S := by simp [R]
  have hac' : ∃ b : B, Sum.inl b ∉ R := by simpa [R] using hbc
  have hbr' : ∃ a : A, Sum.inr a ∈ R := by simpa [R] using har
  rw [← join_swap D T U, splitNorm_relabel D (Equiv.sumComm B A) R S hr]
  simpa only [mul_comm] using join_cut_forward D U T hCB hCA hU hT R hac' hbr'

/-- Exhaustive cut orientation, including monochromatic endpoint exteriors. -/
theorem cut_orientation [Nonempty A] [Nonempty B] (S : Finset (A ⊕ B))
    (hS : NontrivialSplit S) :
    ((∃ a : A, Sum.inl a ∉ S) ∧ (∃ b : B, Sum.inr b ∈ S)) ∨
    ((∃ a : A, Sum.inl a ∈ S) ∧ (∃ b : B, Sum.inr b ∉ S)) := by
  have ha : (∃ a : A, Sum.inl a ∈ S) ∨ (∃ a : A, Sum.inl a ∉ S) := by
    obtain ⟨a⟩ := ‹Nonempty A›
    by_cases h : Sum.inl a ∈ S
    · exact Or.inl ⟨a,h⟩
    · exact Or.inr ⟨a,h⟩
  have hb : (∃ b : B, Sum.inr b ∈ S) ∨ (∃ b : B, Sum.inr b ∉ S) := by
    obtain ⟨b⟩ := ‹Nonempty B›
    by_cases h : Sum.inr b ∈ S
    · exact Or.inl ⟨b,h⟩
    · exact Or.inr ⟨b,h⟩
  have hr : (∃ a : A, Sum.inl a ∈ S) ∨ (∃ b : B, Sum.inr b ∈ S) := by
    rcases hS.1 with ⟨a | b,h⟩
    · exact Or.inl ⟨a,h⟩
    · exact Or.inr ⟨b,h⟩
  have hc : (∃ a : A, Sum.inl a ∉ S) ∨ (∃ b : B, Sum.inr b ∉ S) := by
    rcases hS.2 with ⟨a | b,h⟩
    · exact Or.inl ⟨a,Finset.mem_compl.mp h⟩
    · exact Or.inr ⟨b,Finset.mem_compl.mp h⟩
  tauto

/-- Universal single-edge closure. Nonempty A,B say exactly that each
endpoint has at least two total slots. No Nonempty (Fin D) is required. -/
theorem join_allProper [Nonempty A] [Nonempty B] (D : ℕ)
    (T : Coeff (A ⊕ Unit) D) (U : Coeff (B ⊕ Unit) D)
    {CA CB : ℝ} (hCA : 0 ≤ CA) (hCB : 0 ≤ CB)
    (hT : AllProper D T CA) (hU : AllProper D U CB) :
    AllProper D (join D T U) (CA * CB) := by
  intro S hS
  rcases cut_orientation S hS with ⟨hac,hbr⟩ | ⟨har,hbc⟩
  · exact join_cut_forward D T U hCA hCB hT hU S hac hbr
  · exact join_cut_reverse D T U hCA hCB hT hU S har hbc

omit [DecidableEq A] [DecidableEq B] in
/-- Dimension zero is the genuinely empty edge sum, not an empty group. -/
theorem join_zero_dimension (T : Coeff (A ⊕ Unit) 0) (U : Coeff (B ⊕ Unit) 0) :
    join 0 T U = 0 := by
  ext a
  simp [join]

end Edge
end AcceleratedLogConcave.Tensor.EdgeClosure

namespace AcceleratedLogConcave.Tensor.EdgeClosure
open scoped BigOperators Classical

section ArbitrarySlots
variable {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]

/-- Expose any chosen slot as the single Unit edge slot. -/
def expose (x : X) : X ≃ {z : X // z ≠ x} ⊕ Unit where
  toFun z := if h : z = x then .inr () else .inl ⟨z,h⟩
  invFun := Sum.elim Subtype.val (fun _ => x)
  left_inv z := by dsimp; split_ifs with h; exact h.symm; rfl
  right_inv z := by
    cases z with
    | inl z => simp [z.property]
    | inr u => cases u; simp

/-- Literal insertion of the edge coordinate in an otherwise complete assignment. -/
def insertEdge (D : ℕ) (x : X) (a : {z : X // z ≠ x} → Fin D)
    (w : Fin D) : X → Fin D :=
  fun z => if h : z = x then w else a ⟨z,h⟩

/-- Arbitrary original slot labels and arbitrary contracted positions. -/
def contractAt (D : ℕ) (x : X) (y : Y) (T : Coeff X D) (U : Coeff Y D) :
    Coeff ({z : X // z ≠ x} ⊕ {z : Y // z ≠ y}) D :=
  WithLp.toLp 2 (fun a => ∑ w : Fin D,
    T (insertEdge D x (fun z => a (.inl z)) w) *
    U (insertEdge D y (fun z => a (.inr z)) w))

/-- Literal coefficient bridge to the normalized wrapper, before estimates. -/
theorem contractAt_eq_join (D : ℕ) (x : X) (y : Y)
    (T : Coeff X D) (U : Coeff Y D) :
    contractAt D x y T U =
      join D (relabel D (expose x) T) (relabel D (expose y) U) := by
  ext a
  dsimp only [contractAt, relabel, join]
  apply Finset.sum_congr rfl
  intro w _
  congr 1
  · apply congrArg (fun f => T f)
    funext z
    by_cases h : z = x <;> simp [insertEdge, expose, h]
  · apply congrArg (fun f => U f)
    funext z
    by_cases h : z = y <;> simp [insertEdge, expose, h]

/-- The advertised arbitrary-slot, arbitrary-edge-position, all-proper wrapper.
The two nonemptiness premises are precisely total endpoint rank at least two.
Dimension zero and every choice of empty internal row/column groups are included. -/
theorem contractAt_allProper (D : ℕ) (x : X) (y : Y)
    [Nonempty {z : X // z ≠ x}] [Nonempty {z : Y // z ≠ y}]
    (T : Coeff X D) (U : Coeff Y D) {CA CB : ℝ}
    (hCA : 0 ≤ CA) (hCB : 0 ≤ CB)
    (hT : AllProper D T CA) (hU : AllProper D U CB) :
    AllProper D (contractAt D x y T U) (CA * CB) := by
  rw [contractAt_eq_join]
  exact join_allProper D _ _ hCA hCB (hT.relabel (expose x)) (hU.relabel (expose y))

/-- Any user-selected external ordering is allowed; no output slot is removed. -/
theorem contractAt_relabel_allProper {Z : Type*} [Fintype Z] [DecidableEq Z]
    (D : ℕ) (x : X) (y : Y)
    [Nonempty {z : X // z ≠ x}] [Nonempty {z : Y // z ≠ y}]
    (e : ({z : X // z ≠ x} ⊕ {z : Y // z ≠ y}) ≃ Z)
    (T : Coeff X D) (U : Coeff Y D) {CA CB : ℝ}
    (hCA : 0 ≤ CA) (hCB : 0 ≤ CB)
    (hT : AllProper D T CA) (hU : AllProper D U CB) :
    AllProper D (relabel D e (contractAt D x y T U)) (CA * CB) :=
  (contractAt_allProper D x y T U hCA hCB hT hU).relabel e
end ArbitrarySlots

section Composition
variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

/-- Swap an operator's ordinary input/output only for exposing the contracted
input. This is a slot relabeling, not a commutation of operator multiplication. -/
def swapLast : ((A ⊕ Unit) ⊕ Unit) ≃ ((A ⊕ Unit) ⊕ Unit) where
  toFun
    | .inl (.inl a) => .inl (.inl a)
    | .inl (.inr u) => .inr u
    | .inr u => .inl (.inr u)
  invFun
    | .inl (.inl a) => .inl (.inl a)
    | .inl (.inr u) => .inr u
    | .inr u => .inl (.inr u)
  left_inv s := by rcases s with (a | u) | u <;> rfl
  right_inv s := by rcases s with (a | u) | u <;> rfl

/-- Coefficients of ordered operator composition T.comp U: root derivative
slots A, root output, branch derivative slots B, and branch input all survive. -/
def operatorCompose (D : ℕ) (T : Coeff ((A ⊕ Unit) ⊕ Unit) D)
    (U : Coeff ((B ⊕ Unit) ⊕ Unit) D) :
    Coeff ((A ⊕ Unit) ⊕ (B ⊕ Unit)) D :=
  WithLp.toLp 2 (fun a => ∑ w : Fin D,
    T (Sum.elim (Sum.elim (fun i => a (.inl (.inl i))) (fun _ => w))
      (fun _ => a (.inl (.inr ())))) *
    U (Sum.elim (fun i => a (.inr i)) (fun _ => w)))

omit [DecidableEq A] [DecidableEq B] in
/-- Exact ordered multiplication, including both ordinary operator indices. -/
theorem operatorCompose_eq_join (D : ℕ)
    (T : Coeff ((A ⊕ Unit) ⊕ Unit) D)
    (U : Coeff ((B ⊕ Unit) ⊕ Unit) D) :
    operatorCompose D T U = join D (relabel D swapLast T) U := by
  ext a
  dsimp only [operatorCompose, relabel, join]
  apply Finset.sum_congr rfl
  intro w _
  congr 1
  apply congrArg (fun f => T f)
  funext s
  rcases s with (i | u) | u
  · rfl
  · cases u; rfl
  · cases u; rfl

/-- Binary composition bound suitable for each labeled Leibniz term in B U₁(Y).
A and B may be empty, so order-zero factors are included. -/
theorem operatorCompose_allProper (D : ℕ)
    (T : Coeff ((A ⊕ Unit) ⊕ Unit) D)
    (U : Coeff ((B ⊕ Unit) ⊕ Unit) D) {CA CB : ℝ}
    (hCA : 0 ≤ CA) (hCB : 0 ≤ CB)
    (hT : AllProper D T CA) (hU : AllProper D U CB) :
    AllProper D (operatorCompose D T U) (CA * CB) := by
  rw [operatorCompose_eq_join]
  exact join_allProper D _ _ hCA hCB (hT.relabel swapLast) hU

/-- Attaching a positive-order vector jet to a selected derivative slot is
contractAt_allProper with y the vector-output slot. No hypothesis on a target
composition coefficient or its norm is needed. -/
theorem attachVector_allProper {X : Type*} [Fintype X] [DecidableEq X]
    [Nonempty B] (D : ℕ) (x : X) [Nonempty {z : X // z ≠ x}]
    (T : Coeff X D) (V : Coeff (B ⊕ Unit) D) {CT CV : ℝ}
    (hCT : 0 ≤ CT) (hCV : 0 ≤ CV)
    (hT : AllProper D T CT) (hV : AllProper D V CV) :
    AllProper D (contractAt D x (Sum.inr ()) T V) (CT * CV) := by
  let : Nonempty {z : B ⊕ Unit // z ≠ Sum.inr ()} := by
    obtain ⟨b⟩ := ‹Nonempty B›
    exact ⟨⟨Sum.inl b, by simp⟩⟩
  exact contractAt_allProper D x (Sum.inr ()) T V hCT hCV hT hV
end Composition

section FiniteSums
variable {X I : Type*} [Fintype X] [DecidableEq X] [Fintype I]

/-- Each ordered partition term can be bounded independently, then summed
in the same genuine rectangular operator space. -/
theorem allProper_sum (D : ℕ) (T : I → Coeff X D) (C : I → ℝ)
    (h : ∀ i, AllProper D (T i) (C i)) :
    AllProper D (∑ i, T i) (∑ i, C i) := by
  intro S hS
  change ‖splitOperatorEquiv D S (∑ i, T i)‖ ≤ _
  rw [map_sum]
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun i _ => h i S hS))

/-- Empty slot groups have exactly one assignment for EVERY D, including zero. -/
theorem empty_group_assignments_card (G : Type*) [Fintype G] [IsEmpty G] (D : ℕ) :
    Fintype.card (G → Fin D) = 1 := by simp
end FiniteSums
end AcceleratedLogConcave.Tensor.EdgeClosure
