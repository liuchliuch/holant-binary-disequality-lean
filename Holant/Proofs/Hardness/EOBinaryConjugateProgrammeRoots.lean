import Holant.Proofs.Hardness.BinaryCSPProgrammeRoots
import Holant.Proofs.Hardness.EOBinaryPlaneConjugate

/-! The full four-coordinate multiplicity grid, including repeated roots, is
written by finite Boolean-stack loops. Every root is computed from four fixed
field coefficients. No conjugation closure assumption or root oracle is used. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.EOBinaryConjugateProgrammeRoots
open Turing Computability Holant.Algebraic Holant.Complexity BinaryCompose FixedFieldMachines
open BinaryCSPProgrammeCore
open Holant.OneHot
namespace W
export Holant.LocalDrafts.Tractability.AffineMachine.WireLists (tabulate flatten succComputes mapComputes)
end W
namespace C
export BinaryCSPProgrammeRoots (Index indexEncoding indices indicesComputes indices_length mem_indices)
end C
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 4096
set_option Elab.async false

abbrev Index := ℕ × C.Index
abbrev indexEncoding := pairEncoding unary C.indexEncoding

def indices (n : ℕ) : List Index :=
  (List.range (n+1)).flatMap fun i => (C.indices n).map fun p => (i,p)

def cellComputes : Computes (pairEncoding unary unary) (framedListEncoding indexEncoding)
    (fun p : ℕ×ℕ => (C.indices p.1).map fun q => (p.2,q)) := by
  let context := Wiring.firstComputes (pairEncoding unary unary) C.indexEncoding
  let first := context.andThen (Wiring.secondComputes unary unary)
  let index := Wiring.secondComputes (pairEncoding unary unary) C.indexEncoding
  exact Holant.LocalDrafts.Tractability.AffineMachine.AccessPrograms.map
    C.indexEncoding indexEncoding
    ((Wiring.firstComputes unary unary).andThen C.indicesComputes)
    (fun p q => (p.2,q)) (pairComputes first index)

def indicesComputes : Computes unary (framedListEncoding indexEncoding) indices :=
  congrComputes ((W.tabulate unary (framedListEncoding indexEncoding)
    (fun n => n+1) W.succComputes
    (fun n i => (C.indices n).map fun p => (i,p)) cellComputes).andThen
      (W.flatten indexEncoding)) (fun _ => rfl)

@[simp] theorem indices_length (n : ℕ) : (indices n).length=(n+1)^4 := by
  simp [indices,List.length_flatMap,List.sum_replicate,pow_succ,Nat.mul_comm]

theorem mem_indices {n : ℕ} {p : Index} : p∈indices n ↔
    p.1≤n ∧ p.2.1≤n ∧ p.2.2.1≤n ∧ p.2.2.2≤n := by
  rcases p with ⟨i,p⟩
  simp only [indices,List.mem_flatMap,List.mem_range,List.mem_map,Prod.mk.injEq]
  constructor
  · rintro ⟨i',hi',p',hp',rfl,rfl⟩
    exact ⟨by omega,C.mem_indices.mp hp'⟩
  · rintro ⟨hi,hp⟩
    exact ⟨i,by omega,p,C.mem_indices.mpr hp,rfl,rfl⟩

variable {K : Type} [Field K] [Algebra ℚ K] {d : ℕ}
variable (F : FixedField K d) (c : Fin 4→K)

def monomial (p : Index) : K := c 0^p.1*c 1^p.2.1*c 2^p.2.2.1*c 3^p.2.2.2

def roots (n : ℕ) : List K := (indices n).map (monomial c)

def monomialComputes : Computes indexEncoding F.encoding (monomial c) := by
  let i := Wiring.firstComputes unary C.indexEncoding
  let tail := Wiring.secondComputes unary C.indexEncoding
  let rest := tail.andThen (BinaryCSPProgrammeRoots.monomialComputes F (c 1) (c 2) (c 3))
  exact congrComputes ((pairComputes (i.andThen (ThreeModeProgrammeRoots.powerComputes F (c 0)))
    rest).andThen (Concrete.fieldMultiplication F)) (fun p => by
      dsimp [monomial,BinaryCSPProgrammeRoots.monomial]
      ring)

def rootsComputes : Computes unary (framedListEncoding F.encoding) (roots c) :=
  indicesComputes.andThen (W.mapComputes indexEncoding F.encoding (monomial c) (monomialComputes F c))

omit [Algebra ℚ K] in
@[simp] theorem roots_length (n : ℕ) : (roots c n).length=(n+1)^4 := by simp [roots]

omit [Algebra ℚ K] in
theorem roots_nonzero (hc : ∀j,c j≠0) (n : ℕ) : ∀r∈roots c n,r≠0 := by
  intro r hr
  obtain ⟨p,_,rfl⟩ := List.mem_map.mp hr
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ (hc 0))
    (pow_ne_zero _ (hc 1))) (pow_ne_zero _ (hc 2))) (pow_ne_zero _ (hc 3))

omit [Algebra ℚ K] in
theorem monomial_mem (n : ℕ) (p : EOBinaryPlaneConjugate.Grid n) :
    EOBinaryPlaneConjugate.monomial c p∈roots c n := by
  refine List.mem_map.mpr ⟨((p 0).val,(p 1).val,(p 2).val,(p 3).val),?_,?_⟩
  · exact mem_indices.mpr ⟨Nat.le_of_lt_succ (p 0).isLt,Nat.le_of_lt_succ (p 1).isLt,
      Nat.le_of_lt_succ (p 2).isLt,Nat.le_of_lt_succ (p 3).isLt⟩
  · simp [monomial,EOBinaryPlaneConjugate.monomial,Fin.prod_univ_succ,mul_assoc]

omit [Algebra ℚ K] in
theorem roots_bound {A : Type} (base : A→K) (unit : A) (hunit : base unit=1)
    (hc : ∀j,ArithmeticSize.Bound base 1 (c j)) (n : ℕ) :
    ∀r∈roots c n,ArithmeticSize.Bound base (4*n) r := by
  intro r hr
  obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hr
  obtain ⟨h₀,h₁,h₂,h₃⟩ := mem_indices.mp hp
  have h := (((ThreeModeProgrammeRootBounds.power_bound base (hc 0) p.1).mul
    (ThreeModeProgrammeRootBounds.power_bound base (hc 1) p.2.1)).mul
    (ThreeModeProgrammeRootBounds.power_bound base (hc 2) p.2.2.1)).mul
    (ThreeModeProgrammeRootBounds.power_bound base (hc 3) p.2.2.2)
  exact h.mono unit hunit (by omega)

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.EOBinaryConjugateProgrammeRoots
