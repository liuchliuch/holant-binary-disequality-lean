import Holant.Proofs.Hardness.EOBinaryConjugateProgrammeState

/-! Physical paired roots and controller initialization. Conjugated roots are
computed from the four fixed conjugated coefficients, never by assuming the
original coefficient field is closed under conjugation. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.EOBinaryConjugateProgrammePairs
open Turing Computability Holant.Algebraic Holant.Complexity BinaryCompose FixedFieldMachines
open BinaryCSPProgrammeCore
open EOBinaryConjugateProgrammeState
open Holant.LocalDrafts.Tractability.AffineMachine
namespace R
export EOBinaryConjugateProgrammeRoots (Index indexEncoding indices indicesComputes monomial monomialComputes roots)
end R
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 4096
set_option Elab.async false
variable {L : Type} [Field L] [Algebra ℚ L] [StarRing L] {d : ℕ}
variable (F : FixedField L d) (c : Fin 4→L)

def roots (n : ℕ) : List (L×L) :=
  (R.indices n).map fun p=>(R.monomial c p,R.monomial (fun j=>star (c j)) p)

def computes : Computes unary (rootsEncoding F) (roots c) :=
  R.indicesComputes.andThen (WireLists.mapComputes R.indexEncoding (scalarsEncoding F)
    (fun p=>(R.monomial c p,R.monomial (fun j=>star (c j)) p))
    (pairComputes (R.monomialComputes F c) (R.monomialComputes F (fun j=>star (c j)))))

@[simp] theorem roots_length (n : ℕ) : (roots c n).length=(n+1)^4 := by simp [roots]

theorem roots_first (n : ℕ) : (roots c n).map Prod.fst=R.roots c n := by simp [roots,R.roots]

theorem roots_conjugate (n : ℕ) (p : L×L) (hp : p∈roots c n) : p.2=star p.1 := by
  obtain ⟨q,_,rfl⟩ := List.mem_map.mp hp
  simp [R.monomial,star_mul,star_pow,mul_comm,mul_left_comm,mul_assoc]

theorem roots_bound {A : Type} (base : A→L) (unit : A) (hunit : base unit=1)
    (hc : ∀j,Holant.OneHot.ArithmeticSize.Bound base 1 (c j))
    (hstar : ∀j,Holant.OneHot.ArithmeticSize.Bound base 1 (star (c j))) (n : ℕ) :
    ∀p∈roots c n,Holant.OneHot.ArithmeticSize.Bound base (4*n) p.1 ∧
      Holant.OneHot.ArithmeticSize.Bound base (4*n) p.2 := by
  intro p hp
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp
  exact ⟨EOBinaryConjugateProgrammeRoots.roots_bound c base unit hunit hc n _
    (List.mem_map.mpr ⟨q,hq,rfl⟩),
    EOBinaryConjugateProgrammeRoots.roots_bound (fun j=>star (c j)) base unit hunit hstar n _
    (List.mem_map.mpr ⟨q,hq,rfl⟩)⟩

/-- Multiplication of unary counts is a nested tape traversal. -/
def unaryMultiply : Computes (pairEncoding unary unary) unary (fun p : ℕ×ℕ=>p.1*p.2) := by
  let ctx := Wiring.firstComputes (pairEncoding unary unary) unary
  let list := (ctx.andThen (Wiring.secondComputes unary unary)).andThen
    (WireLists.replicate encodingBoolBool true)
  let tab := WireLists.tabulate (pairEncoding unary unary) (framedListEncoding encodingBoolBool)
    (fun p : ℕ×ℕ=>p.1) (Wiring.firstComputes unary unary)
    (fun p _=>List.replicate p.2 true) list
  exact congrComputes ((tab.andThen (WireLists.flatten encodingBoolBool)).andThen
    (WireLists.lengthComputes encodingBoolBool)) (fun p=>by
      simp [List.length_flatten,List.sum_replicate,Nat.mul_comm])

abbrev inputEncoding := pairEncoding (rootsEncoding F) (valuesEncoding F)

def initialComputes : Computes (inputEncoding F) (encoding F) (fun p=>initial p.1 p.2) := by
  let rs := Wiring.firstComputes (rootsEncoding F) (valuesEncoding F)
  let ys := Wiring.secondComputes (rootsEncoding F) (valuesEncoding F)
  let count := rs.andThen (WireLists.lengthComputes (scalarsEncoding F))
  let fuel := (pairComputes count (count.andThen WireLists.succComputes)).andThen unaryMultiply
  let den := (rs.andThen (FixedGadgetSubstitution.Compiler.getDComputes (scalarsEncoding F) 0 (0,0))).andThen
    (Wiring.firstComputes F.encoding F.encoding)
  exact assemble F rs ys rs rs ys den
    (constantComputes (inputEncoding F) F.encoding 0) (constantComputes (inputEncoding F) F.encoding 0)
    (constantComputes (inputEncoding F) F.encoding 1) fuel

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.EOBinaryConjugateProgrammePairs
