import Holant.Proofs.Algorithms.TransformRecognition.RationalSparseMachine


namespace Holant.LocalDrafts.MainChain.TransformRecognition.FiniteSystemDisjunction
open Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition
open Sparse
variable {v : ℕ}

def appendBranch (S T : List (Poly v 1)) : List (Poly v 1) :=
  S.flatMap (fun p => T.map (mul RationalCompiler.data p))
def combine : List (List (Poly v 1)) → List (Poly v 1)
  | [] => [one RationalCompiler.data]
  | S::rest => appendBranch S (combine rest)

theorem append_zero_iff {E : Type*} [Field E] (φ : ℚ →+* E) (z : Fin v → E)
    (S T : List (Poly v 1)) :
    (∀ p ∈ appendBranch S T, SparseEvaluation.evaluate RationalCompiler.field φ z p=0) ↔
      (∀ p ∈ S, SparseEvaluation.evaluate RationalCompiler.field φ z p=0) ∨
      (∀ p ∈ T, SparseEvaluation.evaluate RationalCompiler.field φ z p=0) := by
  classical
  have hm (p q : Poly v 1) : SparseEvaluation.evaluate RationalCompiler.field φ z
      (mul RationalCompiler.data p q) =
      SparseEvaluation.evaluate RationalCompiler.field φ z p *
      SparseEvaluation.evaluate RationalCompiler.field φ z q :=
    SparseEvaluation.mul_eval RationalCompiler.field φ z p q
  simp only [appendBranch,List.forall_mem_flatMap,List.forall_mem_map,
    hm]
  constructor
  · intro h
    by_cases hs : ∀ p ∈ S, SparseEvaluation.evaluate RationalCompiler.field φ z p=0
    · exact Or.inl hs
    · right
      push_neg at hs
      obtain ⟨p,hp,hp0⟩ := hs
      intro q hq
      exact (mul_eq_zero.mp (h p hp q hq)).resolve_left hp0
  · rintro (hs | ht) p hp q hq
    · rw [hs p hp,zero_mul]
    · rw [ht q hq,mul_zero]

theorem combine_zero_iff {E : Type*} [Field E] (φ : ℚ →+* E) (z : Fin v → E)
    (branches : List (List (Poly v 1))) :
    (∀ p ∈ combine branches, SparseEvaluation.evaluate RationalCompiler.field φ z p=0) ↔
      ∃ S ∈ branches, ∀ p ∈ S, SparseEvaluation.evaluate RationalCompiler.field φ z p=0 := by
  induction branches with
  | nil =>
    have h1 : SparseEvaluation.evaluate RationalCompiler.field φ z
        (one (v:=v) RationalCompiler.data)=1 := SparseEvaluation.one_eval RationalCompiler.field φ z
    simp [combine,h1]
  | cons S rest ih =>
    rw [combine,append_zero_iff,ih]
    simp only [List.mem_cons,exists_eq_or_imp]

/-- The same assignment to original input entries is retained throughout the
finite disjunction. No branch may choose different coefficient conjugates. -/
theorem bound_solution_iff {E : Type*} [Field E] (φ : ℚ →+* E)
    {m : ℕ} (address : Fin m → Fin v) (w : Fin m → E)
    (branches : List (List (Poly v 1))) :
    (∃ z : Fin v → E, (∀ i, z (address i)=w i) ∧
      ∀ p ∈ combine branches, SparseEvaluation.evaluate RationalCompiler.field φ z p=0) ↔
    ∃ S ∈ branches, ∃ z : Fin v → E, (∀ i, z (address i)=w i) ∧
      ∀ p ∈ S, SparseEvaluation.evaluate RationalCompiler.field φ z p=0 := by
  constructor
  · rintro ⟨z,hb,hz⟩
    obtain ⟨S,hS,hs⟩ := (combine_zero_iff φ z branches).mp hz
    exact ⟨S,hS,z,hb,hs⟩
  · rintro ⟨S,hS,z,hb,hz⟩
    exact ⟨z,hb,(combine_zero_iff φ z branches).mpr ⟨S,hS,hz⟩⟩

end Holant.LocalDrafts.MainChain.TransformRecognition.FiniteSystemDisjunction
