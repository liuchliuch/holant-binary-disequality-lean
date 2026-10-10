import Holant.EightVertex.ProductAnchor.NetworksData
import Mathlib.Tactic.Ring


namespace Holant.LocalDrafts.Hardness.EightVertexNonexception
open Holant

abbrev Word := Fin 4 → Bool

@[ext] structure Entries (K : Type*) where
  a : K
  b : K
  c : K
  d : K
  w : K
  z : K
  y : K
  x : K

def entries {K : Type*} (M : Signature K 4) : Entries K :=
  ⟨M ![false,false,false,false], M ![false,false,true,true],
   M ![false,true,false,true], M ![false,true,true,false],
   M ![true,false,false,true], M ![true,false,true,false],
   M ![true,true,false,false], M ![true,true,true,true]⟩

def table {K : Type*} [Zero K] (p : Entries K) : Signature K 4 := fun t =>
  match t 0, t 1, t 2, t 3 with
  | false, false, false, false => p.a
  | false, false, true, true => p.b
  | false, true, false, true => p.c
  | false, true, true, false => p.d
  | true, false, false, true => p.w
  | true, false, true, false => p.z
  | true, true, false, false => p.y
  | true, true, true, true => p.x
  | _, _, _, _ => 0

def EvenSupport {K : Type*} [Zero K] (M : Signature K 4) : Prop :=
  ∀ t, weight t % 2 ≠ 0 → M t = 0

def NonzeroCorners {K : Type*} [Mul K] [Zero K] (M : Signature K 4) : Prop :=
  (entries M).a * (entries M).x ≠ 0

theorem word_eta (t : Word) : t = ![t 0,t 1,t 2,t 3] := by
  funext i
  fin_cases i <;> rfl

/-- The support promise reconstructs M, rather than supplying a different
eight-entry tensor as an additional mathematical input. -/
theorem table_entries {K : Type*} [Zero K] (M : Signature K 4)
    (hM : EvenSupport M) : table (entries M) = M := by
  funext t
  rw [word_eta t]
  cases h0 : t 0 <;> cases h1 : t 1 <;>
    cases h2 : t 2 <;> cases h3 : t 3
  all_goals simp only [table,entries,Matrix.cons_val_zero,Matrix.cons_val_succ]
  all_goals first | rfl | (symm; apply hM; decide)

/-- The literal coefficient test for the sparse branch. The endpoint promise
is retained separately, so the same test is usable on every original input. -/
def SparseCase {K : Type*} [Zero K] (M : Signature K 4) : Prop :=
  (entries M).b = 0 ∧ (entries M).y = 0 ∧ (entries M).w = 0 ∧
  (entries M).c ≠ 0 ∧ (entries M).d ≠ 0 ∧ (entries M).z ≠ 0

/-- Exact entries of M (X tensor X) M, with original ordered row/column bits. -/
def chainEntries {K : Type*} [CommSemiring K] (p : Entries K) : Entries K :=
  ⟨p.a * (p.b + p.y), p.a * p.x + p.b ^ 2,
   p.c * (p.w + p.d), p.c * p.z + p.d ^ 2,
   p.w ^ 2 + p.z * p.c, p.z * (p.w + p.d),
   p.y ^ 2 + p.x * p.a, p.x * (p.y + p.b)⟩

def chainValue {K : Type*} [CommSemiring K] (M : Signature K 4)
    (u v : Bool) (t : Word) : K :=
  M ![t 0,t 1,u,v] * M ![!u,!v,t 2,t 3]

def chainSum {K : Type*} [CommSemiring K] (M : Signature K 4) : Signature K 4 :=
  fun t => (chainValue M false false t + chainValue M true false t) +
    (chainValue M false true t + chainValue M true true t)

theorem chainSum_table {K : Type*} [CommSemiring K] (p : Entries K) :
    chainSum (table p) = table (chainEntries p) := by
  funext t
  unfold chainSum chainValue table
  cases h0 : t 0 <;> cases h1 : t 1 <;>
    cases h2 : t 2 <;> cases h3 : t 3 <;>
    simp [h0,h1,h2,h3,chainEntries] <;> ring

theorem chainSum_entries {K : Type*} [CommSemiring K] (M : Signature K 4)
    (hM : EvenSupport M) : chainSum M = table (chainEntries (entries M)) := by
  calc
    chainSum M = chainSum (table (entries M)) :=
      congrArg chainSum (table_entries M hM).symm
    _ = table (chainEntries (entries M)) := chainSum_table (entries M)

/-- The sparse output is a weight-two tensor, with one genuinely optional
coefficient. This uses a*x, never the normalized a^2 from the paper. -/
def sparseEntries {K : Type*} [CommSemiring K] (p : Entries K) : Entries K :=
  ⟨0, p.a * p.x, p.c * p.d, p.c * p.z + p.d ^ 2,
    p.c * p.z, p.d * p.z, p.a * p.x, 0⟩

theorem chainEntries_sparse {K : Type*} [CommSemiring K] (M : Signature K 4)
    (h : SparseCase M) : chainEntries (entries M) = sparseEntries (entries M) := by
  rcases h with ⟨hb,hy,hw,hc,hd,hz⟩
  apply Entries.ext <;> simp [chainEntries,sparseEntries,hb,hy,hw,mul_comm]

theorem sparse_singleLayer {K : Type*} [CommSemiring K] (p : Entries K) :
    Signature.SingleLayer (table (sparseEntries p)) 2 := by
  intro t ht
  have hw := Holant.EightVertex.ProductAnchor.weight_four t
  unfold table
  cases h0 : t 0 <;> cases h1 : t 1 <;>
    cases h2 : t 2 <;> cases h3 : t 3 <;>
    simp [h0,h1,h2,h3,sparseEntries] at hw ⊢
  all_goals exact (ht hw).elim

/-- Five distinct supported original boundary words. The sixth entry may
vanish; it is deliberately not made a nonzero hypothesis. -/
theorem sparse_mandatory_entries {K : Type*} [CommSemiring K] [NoZeroDivisors K]
    (M : Signature K 4) (hcorner : NonzeroCorners M) (h : SparseCase M) :
    table (sparseEntries (entries M)) ![false,false,true,true] ≠ 0 ∧
    table (sparseEntries (entries M)) ![false,true,false,true] ≠ 0 ∧
    table (sparseEntries (entries M)) ![true,false,false,true] ≠ 0 ∧
    table (sparseEntries (entries M)) ![true,false,true,false] ≠ 0 ∧
    table (sparseEntries (entries M)) ![true,true,false,false] ≠ 0 := by
  rcases h with ⟨hb,hy,hw,hc,hd,hz⟩
  change (entries M).a * (entries M).x ≠ 0 ∧
    (entries M).c * (entries M).d ≠ 0 ∧
    (entries M).c * (entries M).z ≠ 0 ∧
    (entries M).d * (entries M).z ≠ 0 ∧
    (entries M).a * (entries M).x ≠ 0
  exact ⟨hcorner,mul_ne_zero hc hd,mul_ne_zero hc hz,mul_ne_zero hd hz,hcorner⟩

theorem sparse_optional_entry {K : Type*} [CommSemiring K] (M : Signature K 4) :
    table (sparseEntries (entries M)) ![false,true,true,false] =
      (entries M).c * (entries M).z + (entries M).d ^ 2 := rfl

theorem word_eq_iff (u v : Word) : u = v ↔
    u 0 = v 0 ∧ u 1 = v 1 ∧ u 2 = v 2 ∧ u 3 = v 3 := by
  constructor
  · intro h
    exact ⟨congrFun h 0,congrFun h 1,congrFun h 2,congrFun h 3⟩
  · rintro ⟨h0,h1,h2,h3⟩
    funext i
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
    · exact h3

def mandatoryWords : Finset Word :=
  {![false,false,true,true],![false,true,false,true],![true,false,false,true],
   ![true,false,true,false],![true,true,false,false]}
def optionalWord : Word := ![false,true,true,false]

noncomputable def supportWords {K : Type*} [Zero K] (M : Signature K 4) : Finset Word := by
  classical
  exact Finset.univ.filter (fun t => M t ≠ 0)

theorem mandatoryWords_card : mandatoryWords.card = 5 := by decide
theorem optionalWord_not_mem : optionalWord ∉ mandatoryWords := by decide

attribute [local instance] Classical.propDecidable

theorem sparse_support_mem {K : Type*} [CommSemiring K] [NoZeroDivisors K]
    (M : Signature K 4) (hc : NonzeroCorners M) (hs : SparseCase M) (t : Word) :
    table (sparseEntries (entries M)) t ≠ 0 ↔
      t ∈ mandatoryWords ∨ (t = optionalWord ∧
        (entries M).c * (entries M).z + (entries M).d ^ 2 ≠ 0) := by
  classical
  rcases hs with ⟨hb,hy,hw,hc',hd,hz⟩
  have hax : (entries M).a * (entries M).x ≠ 0 := hc
  have hcd := mul_ne_zero hc' hd
  have hcz := mul_ne_zero hc' hz
  have hdz := mul_ne_zero hd hz
  rw [word_eta t]
  cases h0 : t 0 <;> cases h1 : t 1 <;>
    cases h2 : t 2 <;> cases h3 : t 3 <;>
    simp [mandatoryWords,optionalWord,word_eq_iff,table,sparseEntries,
      h0,h1,h2,h3,hax,hcd,hcz,hdz]

/-- Exact support, including the cancellation branch of the sixth entry. -/
theorem sparse_support {K : Type*} [CommSemiring K] [NoZeroDivisors K]
    (M : Signature K 4) (hc : NonzeroCorners M) (hs : SparseCase M) :
    supportWords (table (sparseEntries (entries M))) =
      if (entries M).c * (entries M).z + (entries M).d ^ 2 = 0 then mandatoryWords
      else insert optionalWord mandatoryWords := by
  classical
  ext t
  simp only [supportWords,Finset.mem_filter,Finset.mem_univ,true_and,
    sparse_support_mem M hc hs t]
  by_cases ho : (entries M).c * (entries M).z + (entries M).d ^ 2 = 0 <;>
    simp [ho,or_comm]

theorem sparse_support_card {K : Type*} [CommSemiring K] [NoZeroDivisors K]
    (M : Signature K 4) (hc : NonzeroCorners M) (hs : SparseCase M) :
    (supportWords (table (sparseEntries (entries M)))).card =
      if (entries M).c * (entries M).z + (entries M).d ^ 2 = 0 then 5 else 6 := by
  classical
  rw [sparse_support M hc hs]
  by_cases ho : (entries M).c * (entries M).z + (entries M).d ^ 2 = 0 <;>
    simp [ho,mandatoryWords_card,optionalWord_not_mem]

end Holant.LocalDrafts.Hardness.EightVertexNonexception
